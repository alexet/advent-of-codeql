

import input
import utils

string testData() {
    result = testData(2024,4)
}

string realData() {
    result = realData(2024,4)
}

import utils

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  string chars(int x, int y) { result = line(x).charAt(y) }

  bindingset[i]
  string wordCharAt(int x, int y, Dir8 dir, int i) {
    result = chars(x + dir.dx() * i, y + dir.dy() * i)
  }

  predicate xmasAt(int x, int y, Dir8 dir) {
    wordCharAt(x, y, dir, 0) = "X" and
    wordCharAt(x, y, dir, 1) = "M" and
    wordCharAt(x, y, dir, 2) = "A" and
    wordCharAt(x, y, dir, 3) = "S" 
  }

  int xmasCount() { result = count(int x, int y, Dir8 dir | xmasAt(x, y, dir)) }

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

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

select RealImpl::xmasCount(), RealImpl::xmasCount2()
