import input
import utils

string testData() { result = testData(2025, 5) }

string realData() { result = realData(2025, 5) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  string freshRangesRaw(int i) { result = input().splitAt("\n\n", 0).splitAt("\n", i) }

  BigInt ingrediantIds(int i) { result = input().splitAt("\n\n", 1).splitAt("\n", i).toBigInt() }

  predicate freshRange(int i, BigInt lb, BigInt ub) {
    lb = freshRangesRaw(i).splitAt("-", 0).toBigInt() and
    ub = freshRangesRaw(i).splitAt("-", 1).toBigInt()
  }

  BigInt freshIngrediantId(int i) {
    exists(BigInt lb, BigInt ub |
      result = ingrediantIds(i) and
      freshRange(_, lb, ub) and
      lb <= result and
      result <= ub
    )
  }

  int freshIngrediantCount() { result = count(int i | exists(freshIngrediantId(i))) }

  bindingset[lb1, ub1, lb2, ub2]
  predicate intervalOverlap(BigInt lb1, BigInt ub1, BigInt lb2, BigInt ub2) {
    lb1 <= ub2 and
    lb2 <= ub1
  }

  bindingset[lb1, ub1, lb2, ub2]
  predicate combineIntervals(BigInt lb1, BigInt ub1, BigInt lb2, BigInt ub2, BigInt lb, BigInt ub) {
    intervalOverlap(lb1, ub1, lb2, ub2) and
    lb = lb1.minimum(lb2) and
    ub = ub1.maximum(ub2)
  }

  predicate passedInterval(int i, int j, BigInt lb, BigInt ub) {
    j = -1 and
    freshRange(i, lb, ub)
    or
    exists(BigInt lb1, BigInt ub1, BigInt lb2, BigInt ub2 |
      passedInterval(i, j - 1, lb1, ub1) and
      interval(i - 1, j, lb2, ub2) and
      (
        not intervalOverlap(lb1, ub1, lb2, ub2) and
        lb = lb1 and
        ub = ub1
        or
        intervalOverlap(lb1, ub1, lb2, ub2) and
        combineIntervals(lb1, ub1, lb2, ub2, lb, ub)
      )
    )
  }

  predicate interval(int i, int j, BigInt lb, BigInt ub) {
    i = j and
    passedInterval(i, j - 1, lb, ub)
    or
    exists(BigInt lb1, BigInt ub1, BigInt lb2, BigInt ub2 |
      passedInterval(i, j - 1, lb1, ub1) and
      interval(i - 1, j, lb2, ub2) and
      (
        not intervalOverlap(lb1, ub1, lb2, ub2) and
        lb = lb2 and
        ub = ub2
        or
        intervalOverlap(lb1, ub1, lb2, ub2) and
        lb = 0.toBigInt() and
        ub = 0.toBigInt()
      )
    )
  }

  predicate finalInterval(int i, BigInt lb, BigInt ub) {
    exists(int maxRange |
      maxRange = max(int j | freshRange(j, _, _)) and
      interval(maxRange, i, lb, ub)
      and not
      (
        lb = 0.toBigInt() and
        ub = 0.toBigInt()
      )
    )
  }

  BigInt rangeTotal() {
    result =
      strictsum(int i, BigInt lb, BigInt ub |
        finalInterval(i, lb, ub)
      |
        ub - lb + 1.toBigInt()
      )
  }


}

select 1
