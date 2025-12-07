import input
import utils

string testData() { result = testData(2025, 7) }

string realData() { result = realData(2025, 7) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  predicate isStart(int x, int y) { charGrid(x, y) = "S" }

  predicate isSplitter(int x, int y) { charGrid(x, y) = "^" }

  predicate inGrid(int x, int y) { exists(charGrid(x, y)) }

  predicate hasBeam(int x, int y) {
    isStart(x, y)
    or
    inGrid(x, y) and
    (
      hasBeam(x, y - 1) and
      not isSplitter(x, y)
      or
      isSplitter(x - 1, y) and
      hasBeam(x - 1, y - 1)
      or
      isSplitter(x + 1, y) and
      hasBeam(x + 1, y - 1)
    )
  }

  predicate splitPoint(int x, int y) {
    isSplitter(x, y) and
    (
      hasBeam(x, y - 1) or
      hasBeam(x, y - 1)
    )
  }

  int splitCount() { result = count(int x, int y | splitPoint(x, y)) }

  BigInt beamCount(int x, int y) {
    isStart(x, y) and result = 1.toBigInt()
    or
    inGrid(x, y) and isStart(_, y) and not isStart(x, y) and result = 0.toBigInt()
    or
    inGrid(x, y) and
    exists(BigInt l, BigInt r, BigInt u |
      (if isSplitter(x, y) then u = 0.toBigInt() else u = beamCount(x, y - 1)) and
      (if isSplitter(x - 1, y) then l = beamCount(x - 1, y - 1) else l = 0.toBigInt()) and
      (if isSplitter(x + 1, y) then r = beamCount(x + 1, y - 1) else r = 0.toBigInt()) and
      result = l + r + u
    )
  }

  int lastRow() { result = max(int y | exists(charGrid(_, y))) }

  BigInt lastRowBeamCount() { result = sum(int x | | beamCount(x, lastRow())) }
}

select 1
