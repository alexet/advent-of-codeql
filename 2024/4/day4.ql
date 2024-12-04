extensible predicate testDay4(string data);

extensible predicate realDay4(string data);

import utils

module Impl<inputSig/1 input> {
  import Helpers<input/1>

  string chars(int x, int y) { result = line(x).charAt(y) }

  string wordCharAt(int x, int y, Dir8 dir, int i) {
    i in [0 .. 3] and
    result = chars(x + dir.dx() * i, y + dir.dy() * i)
  }

  string wordAt(int x, int y, Dir8 dir) {
    forall(int i | i in [0 .. 3] | exists(wordCharAt(x, y, dir, i))) and
    result = strictconcat(int i | i in [0 .. 3] | wordCharAt(x, y, dir, i) order by i)
  }

  int xmasCount() { result = count(int x, int y, Dir8 dir | wordAt(x, y, dir) = "XMAS") }

  string msAt(int x, int y) {
    result = chars(x, y) and
    result in ["M", "S"]
  }

  predicate xmasAt(int x, int y) {
    chars(x, y) = "A" and
    msAt(x + 1, y + 1) != msAt(x - 1, y - 1) and
    msAt(x + 1, y - 1) != msAt(x - 1, y + 1)
  }

  int xmasCount2() { result = count(int x, int y | xmasAt(x, y)) }
}

module TestImpl = Impl<testDay4/1>;

module RealImpl = Impl<realDay4/1>;

select RealImpl::xmasCount(), RealImpl::xmasCount2()
