import input
import utils

string testData() { result = testData(2025, 2) }

string realData() { result = realData(2025, 2) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  string range(int i) { result = input().splitAt(",", i) }

  BigInt start(int i) { result = range(i).splitAt("-", 0).toBigInt() }

  BigInt end(int i) { result = range(i).splitAt("-", 1).toBigInt() }

  cached
  BigInt inRange(int i) {
    result = start(i)
    or
    result = inRange(i) + [1 .. 100].toBigInt() and result <= end(i)
  }

  int potentialLength() { result = inRange(_).toString().length() }

  BigInt divisors(int overallLength) {
    overallLength = potentialLength() and
    exists(int segmentLength |
      segmentLength in [1 .. overallLength / 2] and
      overallLength % segmentLength = 0 and
      result =
        concat(int j |
          j in [0 .. overallLength - 1] and j % segmentLength = 0
        |
          concat(int k | k in [0 .. segmentLength - 2] | "0") + "1"
        ).toBigInt()
    )
  }

  string idPart(string idStr, int segmentLength, int j) {
    idStr = inRange(_).toString() and
    segmentLength in [1 .. idStr.length() / 2] and
    idStr.length() % segmentLength = 0 and
    j in [0 .. idStr.length() - 1] and
    j % segmentLength = 0 and
    result = idStr.substring(j, j + segmentLength)
  }

  BigInt invalidID(int i) {
    exists(string idStr |
      result = inRange(i) and
      idStr = result.toString() and
      result % divisors(idStr.length()) = 0.toBigInt()
    )
  }

  BigInt badIdSum() { result = sum(int i | | invalidID(i)) }
}

string test1(string idStr, int segmentLength, int j) {
  idStr = "17" and segmentLength = 1 and j = 0 and result = "1"
  or
  idStr = "17" and segmentLength = 1 and j = 1 and result = "7"
}

string test2(int segmentLength) { exists(unique(int j | | test1(result, segmentLength, j))) }

select 1
