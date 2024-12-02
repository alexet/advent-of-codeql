extensible predicate testDay2(string data);

extensible predicate realDay2(string data);

import utils

module Impl<inputSig/1 input> {
  import Helpers<input/1>

  int diff(int i, int j) { result = grid(i, j) - grid(i, j + 1) }

  int doubleDiff(int i, int j) { result = grid(i, j) - grid(i, j + 2) }

  int dropGrid(int i, int j, int k) {
    exists(grid(i, j)) and
    (
      k < j and result = grid(i, k)
      or
      k >= j and result = grid(i, k + 1)
    )
  }

  int diff2(int i, int j, int k) { result = dropGrid(i, j, k) - dropGrid(i, j, k + 1) }

  /**
   * This was inteded to be a more efficient version than safe3 but it had a bug and I gave up
   */
  predicate safeUpTo(int i, int j, boolean decreasing, boolean usedSkip) {
    exists(line(i)) and j = 0 and decreasing in [true, false] and usedSkip = false
    or
    exists(line(i)) and j = 1 and decreasing in [true, false] and usedSkip = true
    or
    (
      decreasing = true and
      safeUpTo(i, j - 1, decreasing, usedSkip) and
      diff(i, j - 1) in [1 .. 3]
      or
      decreasing = true and
      usedSkip = true and
      safeUpTo(i, j - 2, decreasing, false) and
      doubleDiff(i, j - 2) in [1 .. 3]
      or
      decreasing = false and
      safeUpTo(i, j - 1, decreasing, usedSkip) and
      -diff(i, j - 1) in [1 .. 3]
      or
      decreasing = false and
      usedSkip = true and
      safeUpTo(i, j - 2, decreasing, false) and
      -doubleDiff(i, j - 2) in [1 .. 3]
    )
  }

  predicate isSafe(int i) {
    forex(int j | exists(diff(i, j)) | diff(i, j) in [1 .. 3])
    or
    forex(int j | exists(diff(i, j)) | diff(i, j) in [-3 .. -1])
  }

  predicate isSafe2(int i) {
    exists(int maxCol | maxCol = max(int j | exists(grid(i, j))) |
      safeUpTo(i, maxCol, _, _)
      or
      safeUpTo(i, maxCol - 1, _, false)
    )
  }

  predicate isSafe2(int i, boolean pos, boolean skip) {
    exists(int maxCol | maxCol = max(int j | exists(grid(i, j))) |
      safeUpTo(i, maxCol, pos, skip)
      or
      safeUpTo(i, maxCol - 1, pos, false) and skip = true
    )
  }

  predicate isSafe3(int i) {
    exists(int j |
      forex(int k | exists(diff2(i, j, k)) | diff2(i, j, k) in [1 .. 3])
      or
      forex(int k | exists(diff2(i, j, k)) | diff2(i, j, k) in [-3 .. -1])
    )
  }

  int safeCount() { result = count(int i | isSafe(i)) }

  int safeCount2() { result = count(int i | isSafe2(i)) }

  int safeCount3() { result = count(int i | isSafe3(i)) }
}

module TestImpl = Impl<testDay2/1>;

module RealImpl = Impl<realDay2/1>;

select 1
