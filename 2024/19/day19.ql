import input
import utils

string testData() { result = testData(2024, 19) }

string realData() { result = realData(2024, 19) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  string patterns() { result = line(0).splitAt(",", _).trim() }

  string targetPattern(int n) {
    n >= 0 and
    result = line(n + 2)
  }

  int maxTargetLength() { result = max(targetPattern(_).length()) }

  string partialTargets() {
    exists(string target |
      target = targetPattern(_) and
      result = target.prefix([0 .. target.length()])
    )
  }

  cached
  string reachablePrefix(string pattern) {
    result = partialTargets() and
    pattern = partialTargets() and
    pragma[only_bind_out](result) + patterns() = pattern
  }

  class BigInt = QlBuiltins::BigInt;

  language[monotonicAggregates]
  BigInt ways(string target) {
    target = "" and result = 1.toBigInt()
    or
    target != "" and
    target = partialTargets() and
    result = sum(string prefix | prefix = reachablePrefix(target) | ways(prefix))
  }

  BigInt totalWays() { result = sum(int n | | ways(targetPattern(n))) }

  string reachable() {
    result = ""
    or
    result = reachable() + patterns() and
    result = partialTargets()
  }

  int possibleDesigns() { result = count(int n | reachable() = targetPattern(n)) }
}

select 1
