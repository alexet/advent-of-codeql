import input
import utils

string testData() { result = testData(2025, 3) }

string realData() { result = realData(2025, 3) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  string bank(int i) { result = line(i) }

  int bankVals(int i, int j) { result = bank(i).charAt(j).toInt() }

  int maxBankVal(int i) {
    result = max(int j, int k | k > j | bankVals(i, j) * 10 + bankVals(i, k))
  }

  int sumBankVals() { result = sum(int i | | maxBankVal(i)) }

  int maxLength() { result = 12 }

  language[monotonicAggregates]
  int bestDigitIndex(int id, int length) {
    length in [1 .. maxLength()] and
    result =
      max(int j |
        j in [0 .. bank(id).length() - maxLength() + length - 1]
      |
        j order by bankValsAdjusted(id, length, j), j desc
      )
  }

  BigInt bestBankVal(int i) {
    result =
      strictconcat(int j || bankVals(i, bestDigitIndex(i, j)).toString() order by j).toBigInt()
  }

  BigInt sumBankVals2() { result = sum(int i | | bestBankVal(i)) }

  int bankValsAdjusted(int i, int k, int j) {
    k = 1 and result = bankVals(i, j)
    or
    j > bestDigitIndex(i, k - 1) and result = bankVals(i, j)
    or
    j in [0 .. bestDigitIndex(i, k - 1)] and result = -1
  }
}

select RealImpl::sumBankVals().toString(), RealImpl::sumBankVals2().toString()
