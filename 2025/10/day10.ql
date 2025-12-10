import input
import utils

string testData() { result = testData(2025, 10) }

string realData() { result = realData(2025, 10) }

module TestImpl = Impl<testData/0, maxEdgesTest/0>;

module RealImpl = Impl<realData/0, maxEdgesReal/0>;

int maxEdgesTest() { result = 10 }

int maxEdgesReal() { result = 1000 }

signature int intPred();

module Impl<inputSig/0 input, intPred/0 maxEdges> {
  import Helpers<input/0>

  string indicators(int n) { result = line(n).splitAt(" ", 0) }

  boolean indicatorInitialOn(int n, int k) {
    indicators(n).charAt(k + 1) = "." and result = false
    or
    indicators(n).charAt(k + 1) = "#" and result = true
  }

  string targetJoltages(int n) {
    result = line(n).splitAt(" ") and
    result.matches("{%}")
  }

  string wiring(int n, int wire) {
    result = line(n).splitAt(" ", wire + 1) and result.matches("(%)")
  }

  int targetJoltage(int n, int k) {
    result = targetJoltages(n).regexpCapture("\\{(.*)\\}", 1).splitAt(",", k).toInt()
  }

  int toggledByButton(int n, int wire) {
    result = wiring(n, wire).regexpCapture("\\((.*)\\)", 1).splitAt(",").trim().toInt()
  }

  int maxWiring() { result = max(int n | | strictcount(wiring(n, _))) }

  int combination(int n) { result in [0 .. 2.pow(strictcount(wiring(n, _))).floor() - 1] }

  predicate inCombination(int n, int comb, int wire) {
    comb = combination(n) and
    exists(wiring(n, wire)) and
    comb.bitAnd(2.pow(wire).floor()) != 0
  }

  int lightChangeCount(int n, int comb, int k) {
    comb = combination(n) and
    exists(indicatorInitialOn(n, k)) and
    result =
      count(int wire |
        inCombination(n, comb, wire) and
        k = toggledByButton(n, wire)
      )
  }

  predicate workingComb(int n, int comb) {
    comb = combination(n) and
    forall(int k, boolean b | indicatorInitialOn(n, k) = b |
      b = true and lightChangeCount(n, comb, k) % 2 = 1
      or
      b = false and lightChangeCount(n, comb, k) % 2 = 0
    )
  }

  int weight(int n, int comb) {
    workingComb(n, comb) and
    result = count(int k | k in [0 .. comb.log2().ceil()] and comb.bitAnd(2.pow(k).ceil()) != 0)
  }

  float maxState(int n) { result = strictsum(int k | | targetJoltage(n, k).log()).exp() }

  string wireName(int n, int wire) {
    result = "press_" + n + "_" + wire and
    exists(wiring(n, wire))
  }

  string declarations(int n, int wire) {
    result =
      "(declare-const " + wireName(n, wire) + " Int) (assert (<= 0 " + wireName(n, wire) + "))"
  }

  string constraint(int n, int k) {
    result =
      "(assert (= " + targetJoltage(n, k) + " (+ " +
        concat(int wire | toggledByButton(n, wire) = k | wireName(n, wire), " ") + ")))"
  }

  string totalN(int n) {
    result =
      "(declare-const total" + n + " Int) (assert (= total" + n + " (+ " +
        strictconcat(wireName(n, _), " ") + ")))"
  }

  string total() {
    result =
      "(declare-const total Int) (assert (= total (+ " +
        concat(int n | exists(wireName(n, _)) | "total" + n, " ") + ")))"
  }

  string smtString() {
    result =
      concat(declarations(_, _)) + concat(int n, int k | | constraint(n, k) order by n, k) +
        concat(totalN(_)) + total() + "(minimize total) (check-sat) (get-model) (get-value (total))"
  }
}

select 1
