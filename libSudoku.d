/*
	Author: eGust
	e-mail: egustc@gmail.com
	https://github.com/eGust/Sudoku.D
*/
module libSudoku;

import std.range, std.array, std.random, std.conv, core.bitop;
debug import std.stdio;

enum SudokuStatus {
	ssUnknown, ssSolved, ssInvalid,
	ssUnsolvable, ssOnlySolution, ssMultiSolution,
	ssCrossing, ssCrossDone, 
}

struct SudokuData {
	public union {
		ubyte[81]	tiles;
		ubyte[9][9]	rows;
	}

	this(ubyte[81] src)
	{
		tiles = src;
	}

	this(ubyte[9][9] src)
	{
		rows = src;
	}

	auto toString()
	{
		auto s = appender!(string);
		foreach (r, row; rows)
		{
			s.put([
				(row[0..3].map!( (n) => to!string(n) )).join(" "), 
				(row[3..6].map!( (n) => to!string(n) )).join(" "), 
				(row[6..9].map!( (n) => to!string(n) )).join(" "), 
				].join(" | "));
			if (r < 8)
				s.put( "\n" );
			if (r==2 || r==5)
				s.put( "------+-------+------\n" );
		}
		return s.data;
	}
}

SudokuStatus	checkSudokuStatus(ref in SudokuData sd, bool checkSolvable = false)
{
	auto isFull = true;
	enum FULL_MASK = 0b_0001_1111_1111;
	foreach (i; 0..9)
	{
		static bool isInvalid(ubyte n, ref ushort mask)
		{
			if (n==0)
				return false;
			auto m = cast(ushort)(1<<(n-1));
			if (mask & m)
				return true;
			mask |= m;
			return false;
		}

		ushort rowMask, colMask, mtxMask;
		auto mr = i / 3 * 3, mc = i % 3 * 3;
		foreach (j; 0..9)
		{
			if ( isInvalid(sd.rows[i][j], rowMask) 
			  || isInvalid(sd.rows[j][i], colMask) 
			  || isInvalid(sd.rows[mr+j/3][mc+j%3], mtxMask) )
				return SudokuStatus.ssInvalid;
		}

		//writefln("%x\t%x\t%x", rowMask, colMask, mtxMask);
		isFull = isFull && rowMask==FULL_MASK && colMask==FULL_MASK && mtxMask==FULL_MASK;
	}

	if (isFull)
		return SudokuStatus.ssSolved;

	static auto checkSolutionStatus(ref in SudokuData sd)
	{
		switch ( doSolveSudoku(sd, (cnt, ref in _) => cnt <= 1) )
		{
			case 0:
				return SudokuStatus.ssUnsolvable;
			case 1:
				return SudokuStatus.ssOnlySolution;
			default:
				return SudokuStatus.ssMultiSolution;
		}
	}

	return checkSolvable ? checkSolutionStatus(sd) : SudokuStatus.ssUnknown;
}

private enum {
	RELATIVE_COUNT = 20,
	MTX_OFFSET = [ 0, 1, 2, 9, 10, 11, 18, 19, 20, ],
	relative = initRelative(),
}

private static auto initRelative()
{
	ubyte[RELATIVE_COUNT][81] result;
	foreach(n, ref r; result)
	{
		auto idx = 0, col=n%9, row = n-col, mtx = n/27*27 + col/3*3;
		bool[81] used;
		used[n] = true;

		foreach (i; 0..9)
		{
			auto ri = row + i, ci = col + i*9, mi = mtx + MTX_OFFSET[i];

			if (!used[ri])
			{
				used[ri] = true;
				r[idx++] = cast(ubyte)ri;
			}
			if (!used[ci])
			{
				used[ci] = true;
				r[idx++] = cast(ubyte)ci;
			}
			if (!used[mi])
			{
				used[mi] = true;
				r[idx++] = cast(ubyte)mi;
			}
		}
	}
	return result;
}

private auto doSolveSudoku(ref in SudokuData sd, bool delegate(int, ref in SudokuData) dg = null)
{
	struct Tile {
		ubyte	digit, mskCnt;
		ushort	umask;
	}

	// init
	Tile[81] tiles;
	ubyte[80] index;
	int idxCount;

	// init
	foreach(ubyte idx; 0..81)
	{
		auto v = tiles[idx].digit = sd.tiles[idx];
		if(v==0)
		{
			// if the cell is 0 then append to the remains list.
			index[idxCount++] = idx;
			continue;
		}
		
		// set the flag of relative cells.
		auto mask = 1<<(v-1);
		foreach(i; relative[idx])
			tiles[i].umask |= mask;
	}
	
	// update "count". popcnt returns the number of bit 1.
	foreach(ref t; tiles)
		t.mskCnt = cast(ubyte) popcnt(t.umask);

	bool stop = false;
	uint solutionCount;

	void tryNext()
	{
		if (idxCount == 0)
		{
			// found!
			if (dg)
			{
				SudokuData tmp;
				foreach (i, ref t; tmp.tiles)
					t = tiles[i].digit;
				stop = !dg(++solutionCount, tmp);
			}
			return;
		}

		// greater count == less possible numbers, so find the max one
		auto maxId = --idxCount, maxTid = index[maxId], maxCnt = tiles[maxTid].mskCnt;
		if (maxCnt < 8)
			foreach (id, tid; index[0..idxCount])
			{
				auto cnt = tiles[tid].mskCnt;
				if (cnt <= maxCnt)
					continue;
				maxId = id;
				maxTid = tid;
				maxCnt = cnt;

				if (maxCnt == 8)
					// only 1 possible number
					break;
			}

		// backup
		index[maxId] = index[idxCount];
		Tile[RELATIVE_COUNT+1] bakTiles = void;
		bakTiles[RELATIVE_COUNT] = tiles[maxTid];
		foreach (i, rid; relative[maxTid])
			bakTiles[i] = tiles[rid];

		auto mask = tiles[maxTid].umask;
		enumMaskOutter:
		  foreach (_; 0..9-maxCnt)
		{
			/*	for exp.		[..654321]
				to be found:	  --- v = 3
				mask (m) 	=	0b_010011	PLUS	1 =>
				:	mask+1  =	0b_010100	XOR	 mask =>
				:	m^(m+1) =	0b_000111	PLUS	1 =>
				->	 t   =		0b_001000	SHR		1 =>
				->	flag =		0b_000100	OR	 mask =>
				->	mask =		0b_010111	( save for next loop )
				
				bsf returns the number of tail's 0
				=>	bsf(t) => 3
			 */
			auto t = ((mask+1) ^ mask) + 1, flag = t >> 1;
			mask |= flag;
			tiles[maxTid].digit = cast(ubyte)bsf(t);
			
			foreach (i, rid; relative[maxTid])
			{
				// if the cell is already filled, skip it.
				if (tiles[rid].digit)
					continue;
				
				auto msk = bakTiles[i].umask;
				if (msk & flag) {
					// already set, just restore
					tiles[rid] = bakTiles[i];
				} else {
					// not set yet. reduce candidate number first.
					auto newCnt = bakTiles[i].mskCnt;
					if(++newCnt == 9)
						// while candidate number becomes to 0, it won't work. so give up.
						continue enumMaskOutter;
					tiles[rid].umask = cast(ushort)(msk | flag);
					tiles[rid].mskCnt = newCnt;
				}
			}
			tryNext;

			if (stop)
				return;
		}

		// restore
		tiles[maxTid] = bakTiles[RELATIVE_COUNT];
		foreach (i, rid; relative[maxTid])
			tiles[rid] = bakTiles[i];
		index[maxId] = maxTid;
		++idxCount;
	}

	tryNext();
	return solutionCount;
}

bool	solveSudoku(ref SudokuData sd)
{
	switch (checkSudokuStatus(sd)) {
		case SudokuStatus.ssInvalid:
			return false;
		case SudokuStatus.ssSolved:
			return true;
		default:
			return (doSolveSudoku( sd, (cnt, ref in r) => (sd = r, false) ) > 0);
	}
}

auto	findAllSolutions(ref SudokuData sd)
{
	switch (checkSudokuStatus(sd)) {
		case SudokuStatus.ssInvalid:
			return null;
		case SudokuStatus.ssSolved:
			return null;
		default:
			auto rs = appender!(SudokuData[]);
			doSolveSudoku( sd, (cnt, ref in r) => (rs.put(SudokuData(r.tiles)), true) );
			return rs.data;
	}
}

SudokuData	GenerateSudoku()
{
/* Algorithm:
step.1	There are 3 INDEPENDENT 3*3 sub-squares. Shuffle each sub-square (1~9).
step.2	Set 6 single position (marked as ?) to random number.
step.3	Try to solve the sudoku. Repeat the steps if failed.
	0 1 2   3 4 5   6 7 8
  =========================
0 | 1 2 3 | . . ? | . . . |
1 | 4 5 6 | . . . | . . ? |
2 | 7 8 9 | . . . | . . . |
  |-------+-------+-------|
3 | . . . | 1 2 3 | ? . . |
4 | . . . | 4 5 6 | . . . |
5 | . . ? | 7 8 9 | . . . |
  |-------+-------+--------
6 | . . . | . ? . | 1 2 3 |
7 | ? . . | . . . | 4 5 6 |
8 | . . . | . . . | 7 8 9 |
  =========================
*/
	enum {
		MTX_BASE = [ [0, 0], [3, 3], [6, 6], ],
		SINGLES = [
				[0, 5], [1, 8],
				[5, 2], [3, 6],
				[7, 0], [6, 4],
			],
	}

	ubyte[] ids = [ 1, 2, 3, 4, 5, 6, 7, 8, 9, ];
	SudokuData[] sds;
	SudokuData sd;
	do {
		foreach (mb; MTX_BASE)
		{
			auto idx = mb[0]*9 + mb[1];
			randomShuffle(ids);
			foreach (i; 0..9)
				sd.tiles[idx + MTX_OFFSET[i]] = ids[i];
		}

		foreach (coord; SINGLES)
		{
			auto r = coord[0]*9, c = coord[1], mask = 0;
			ubyte d;
			foreach (i; 0..9)
			{
				mask |= 1 << sd.tiles[r+i];
				mask |= 1 << sd.tiles[i*9+c];
			}

			do {
				d = cast(ubyte) uniform(1, 10);
			} while (1<<d & mask);
			sd.tiles[r+c] = d;
		}
		sds = findAllSolutions(sd);
	} while( !sds );

	return sds[uniform(0, sds.length)];
}

SudokuStatus	CrossSudoku(ref SudokuData sd, bool delegate(SudokuStatus, int, ref in SudokuData) dg = null)
{
	auto r = checkSudokuStatus(sd, true);
	switch (r) {
		case SudokuStatus.ssSolved: case SudokuStatus.ssOnlySolution:
			break;
		case SudokuStatus.ssInvalid: case SudokuStatus.ssUnsolvable: case SudokuStatus.ssMultiSolution:
			return r;
		default: ;
	}

	ubyte[81] index;
	/*
	index	[i0, ..., iM, ... iN, 0... ]
	            first--^       ^--last
	..iM: Failed
	iN..: Crossed
	Random select from iM..iN and try to cross. 
	*/
	ubyte last, first;
	foreach (ubyte i, ref t; sd.tiles)
	{
		if (t == 0)
			continue;
		index[last++] = i;
	}

	while (first < last)
	{
		// This way is the same as shuffle.
		auto rnd = uniform(first, last), ridx = index[rnd], t = sd.tiles[ridx];
		sd.tiles[ridx] = 0;
		if ( doSolveSudoku(sd, (cnt, ref in _) => cnt <= 1) == 1 )
		{
			// succ: only exists 1 solution
			if (dg)
			{
				if (!dg(SudokuStatus.ssCrossing, last-1, sd))
					return SudokuStatus.ssCrossing;
			}
			index[rnd] = index[--last];
		} else {
			// failed! => Cross this number will cause more than 1 solutions, so skip it.
			sd.tiles[ridx] = t;
			index[rnd] = index[first++];
		}
	}

	if (dg)
		dg(SudokuStatus.ssCrossing, last-1, sd);
	return SudokuStatus.ssCrossDone;
}

unittest
{
	import std.stdio, std.datetime;
	ubyte[81][] TestData = [
		[0,0,0,0,0,0,0,1,0,9,5,0,0,6,0,4,7,0,6,1,0,0,0,0,5,0,0,0,9,3,2,0,4,0,0,1,5,2,0,0,0,3,0,0,8,4,8,1,0,0,0,0,2,0,0,6,7,0,0,0,1,9,0,0,0,0,0,0,0,0,0,7,0,3,0,5,0,1,8,0,0],
		[7,0,1,0,6,4,0,5,0,0,0,4,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,8,4,0,5,9,1,3,0,0,9,3,0,6,8,7,0,2,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,0,0,0,0,0,0,8,2,4,0,9,5,2,0,0,0,1,0,0],
		[0,7,4,0,0,0,0,8,0,0,0,8,9,0,0,0,5,0,0,6,0,0,0,1,0,9,0,3,0,0,0,8,4,0,0,2,2,0,6,3,0,0,0,0,0,0,5,0,0,9,0,0,0,4,0,0,0,0,6,5,0,0,0,0,0,3,0,0,0,9,4,0,0,0,0,0,0,0,1,7,0],
		[0,0,0,0,6,9,0,0,0,1,0,0,0,0,3,0,2,8,5,6,0,0,0,0,9,0,3,0,0,5,0,1,7,0,0,0,0,7,0,0,2,6,8,1,0,2,0,0,0,0,0,7,0,0,0,0,0,0,0,1,0,8,0,7,0,0,0,4,2,1,0,0,4,0,9,0,7,0,0,0,6],
		[7,3,0,0,6,0,0,8,0,0,0,0,0,0,3,2,0,0,8,0,0,0,4,5,0,6,0,6,0,0,8,0,0,0,2,0,0,0,0,0,5,1,0,4,0,0,1,2,0,0,0,0,0,0,3,0,0,5,2,0,7,0,0,4,5,0,0,0,7,9,0,2,0,0,0,0,0,0,6,0,4],
		[0,0,0,0,0,0,0,1,0,0,5,0,0,0,0,8,0,7,1,0,7,9,0,3,0,6,2,4,0,6,8,3,7,5,0,0,0,1,0,0,0,5,0,0,0,0,7,0,4,1,0,0,0,6,2,6,0,7,0,0,0,0,3,0,0,0,3,2,0,0,0,0,0,9,0,0,0,4,2,0,0],
		[4,0,5,6,0,0,9,3,1,9,0,6,4,0,0,0,2,8,1,0,0,0,0,2,6,0,0,8,0,0,7,0,0,3,0,0,0,0,0,5,0,1,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,5,0,0,0,6,0,0,0,0,9,2,4,3,2,0,3,0,0,4,0,8,0],
		[2,0,6,0,0,0,0,0,0,0,0,7,0,3,8,0,0,9,5,0,9,7,0,0,4,3,0,0,0,0,0,0,5,0,0,0,0,1,0,9,0,0,7,6,0,0,0,2,0,0,4,0,8,0,0,0,0,3,9,2,5,0,0,7,2,0,5,0,6,0,1,0,0,0,0,0,1,0,0,0,0],
		[0,6,0,0,0,0,4,0,0,0,0,7,3,4,1,5,0,0,2,0,4,6,0,8,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,2,9,0,0,0,0,3,8,0,0,7,0,6,9,0,4,0,0,0,0,0,8,0,0,0,0,0,8,0,4,3,6,0,0,0,0,0,0,0,1,7,0],
		[7,0,0,0,0,0,6,9,4,0,2,5,4,0,0,0,0,0,6,0,8,0,0,1,3,2,5,2,0,0,0,0,0,8,4,0,4,0,0,3,0,0,9,0,6,5,0,0,0,0,0,0,3,0,0,0,0,0,6,5,2,0,9,1,0,0,0,0,2,0,0,0,0,6,0,0,0,3,0,0,0],

		[0,9,0,7,0,0,0,4,3,1,0,0,0,0,0,9,0,0,0,0,7,4,8,0,0,0,0,0,8,0,0,0,0,0,0,9,0,5,0,0,1,2,0,6,0,7,0,0,0,0,0,0,0,0,0,0,5,1,0,8,0,0,2,0,1,4,0,5,7,0,0,0,0,0,0,3,9,0,0,0,1],
	];

	enum {
		testSolve = true,
		testGenCro = true,
	}

	static if (testSolve)
	{
		writeln("test solve");
		foreach (i, t; TestData)
		{
			auto sudoku = SudokuData(t);
			writeln(i+1);
			writeln("=====================");
			writeln(sudoku);
			writeln("---------------------");
			writeln("solving...");
			
			auto t1 = Clock.currTime;
			auto solved = solveSudoku(sudoku);
			auto t2 = Clock.currTime;
			writeln(checkSudokuStatus(sudoku));
			writeln("---------------------");
			if(solved)
			{
				writeln(sudoku);
				writeln("=====================");
			}
			writefln("%s, %s ms", solved, (t2-t1).total!"msecs");
			writeln;
		}
		writeln;
	}

	static if (testGenCro)
	{
		writeln("test generate and cross");
		foreach (i; 0..5)
		{
			auto t1 = Clock.currTime;
			auto sd = GenerateSudoku, csd = sd;
			CrossSudoku(csd, (ss, cnt, ref in _) => (cnt > 40) );
			auto t2 = Clock.currTime;
			writeln("=====================");
			writeln(sd);
			writeln("---------------------");
			writeln(checkSudokuStatus(sd));
			writeln("---------------------");
			writeln(csd);
			writeln("=====================");
			writeln(checkSudokuStatus(csd, true));

			auto nz = 0;
			foreach (t; csd.tiles)
				nz += (t!=0);
			writefln("%s, %s ms", nz, (t2-t1).total!"msecs");
			writeln;
		}
	}
}

