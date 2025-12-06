import input
import utils

string testData() { result = testData(2025, 4) }

string realData() { result = realData(2025, 4) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  predicate hasPaper(int x, int y) { charGrid(x, y) = "@" }

  predicate accessiblePaper(int x, int y) {
    hasPaper(x, y) and
    count(int x2, int y2 |
      x2 in [x - 1 .. x + 1] and
      y2 in [y - 1 .. y + 1] and
      (x2 != x or y2 != y) and
      hasPaper(x2, y2)
    ) < 4
  }

  int accessiblePaperCount() { result = count(int x, int y | accessiblePaper(x, y)) }

  pragma[nomagic]
  boolean hasPaper2(int i, int x, int y) {
    i = 0 and
    (
      charGrid(x, y) = "@" and result = true
      or
      charGrid(x, y) != "@" and result = false
    )
    or
    didSomethingOnIter(i - 1) and
    (
      hasPaper2(i - 1, x, y) = false and result = false
      or
      hasPaper2(i - 1, x, y) = true and result = accessiblePaper2(i - 1, x, y).booleanNot()
    )
  }

  predicate didSomethingOnIter(int i) { accessiblePaper2(i, _, _) = true }

  predicate isNeighbour(int x, int y, int x2, int y2) {
    exists(charGrid(x, y)) and
    exists(charGrid(x2, y2)) and
    x2 in [x - 1 .. x + 1] and
    y2 in [y - 1 .. y + 1] and
    (x2 != x or y2 != y)
  }

  pragma[noinline]
  int hasPaperCount(int i, int x, int y) { result = boolToInt(hasPaper2(i, x, y)) }

  language[monotonicAggregates]
  pragma[noinline]
  int neighborCount(int i, int x, int y) {
    hasPaper2(i, x, y) = true and
    result =
      strictsum(int x2, int y2 |
        isNeighbour(x, y, x2, y2)
      |
        hasPaperCount(i, x2, y2)
      )
  }

  pragma[noinline]
  boolean accessiblePaper2(int i, int x, int y) {
    hasPaper2(i, x, y) = false and result = false
    or
    neighborCount(i, x, y) < 4 and result = true
    or
    neighborCount(i, x, y) >= 4 and result = false
  }

  int accessiblePaperCount2() {
    result = count(int i, int x, int y | accessiblePaper2(i, x, y) = true)
  }
}

select 1
