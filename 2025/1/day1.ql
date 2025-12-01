import input
import utils

string testData() { result = testData(2025, 1) }

string realData() { result = realData(2025, 1) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  string dir(int i) { result = line(i).charAt(0) }

  int amount(int i) { result = line(i).suffix(1).toInt() }

  int signedAmount(int i) {
    dir(i) = "L" and result = -amount(i)
    or
    dir(i) = "R" and result = amount(i)
  }

  int posAfter(int i) {
    i = -1 and result = 50
    or
    result = (posAfter(i - 1) + (signedAmount(i) % 100) + 100) % 100
  }

  predicate extraCrossesZero(int i) {
    dir(i) = "R" and posAfter(i - 1) + (amount(i) % 100) >= 100 and posAfter(i - 1) != 0
    or
    dir(i) = "L" and posAfter(i - 1) - (amount(i) % 100) <= 0 and posAfter(i - 1) != 0
  }

  int fullZeroCross(int i) {
    if extraCrossesZero(i) then result = amount(i) / 100 + 1 else result = amount(i) / 100
  }

  int zerocount() { result = count(int i | posAfter(i) = 0) }

  int zeroCrosses() { result = strictsum(int i | | fullZeroCross(i)) }
}

select 1
