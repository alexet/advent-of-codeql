import input
import utils

string testData() { result = testData(2024, 5) }

string realData() { result = realData(2024, 5) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  string sectionLines(int i, int j) { result = input().splitAt("\n\n", i).splitAt("\n", j) }

  predicate orderRule(int x, int y) {
    exists(int n |
      x = sectionLines(0, n).splitAt("|", 0).toInt() and
      y = sectionLines(0, n).splitAt("|", 1).toInt()
    )
  }

  int lineValue(int j, int n) { result = sectionLines(1, j).splitAt(",", n).toInt() }

  predicate inOrder(int j) {
    exists(sectionLines(1, j)) and
    not exists(int a, int b, int x, int y |
      a < b and
      x = lineValue(j, a) and
      y = lineValue(j, b) and
      orderRule(y, x)
    )
  }

  int middleNumber(int j) {
    exists(int maxNum |
      maxNum = max(int n | exists(lineValue(j, n))) and
      result = lineValue(j, maxNum / 2)
    )
  }
  


  int orderedLineValue(int j, int n) {
    result = lineValue(j, _) and
    n = count(int a, int x | x = lineValue(j, a) and orderRule(x, result))
  }

  int orderedMiddleNumber(int j) {
    exists(int maxNum |
      maxNum = max(int n | exists(orderedLineValue(j, n))) and
      result = orderedLineValue(j, maxNum / 2)
    )
  }
  int middleSum() { result = sum(int j | inOrder(j) | middleNumber(j)) }

  int middleSum2() { result = sum(int j | not inOrder(j) | orderedMiddleNumber(j)) }
}

select 1
