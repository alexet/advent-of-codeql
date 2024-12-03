extensible predicate testDay3(string data);

extensible predicate realDay3(string data);

import utils

module Impl<inputSig/1 input> {
  import Helpers<input/1>

  string findMul(int i) {
    exists(string s | input(s) | result = s.regexpFind("mul\\(\\d+,\\d+\\)", i, _))
  }

  int mulSides(int i, int j) {
    result = findMul(i).regexpCapture("mul\\((\\d+),(\\d+)\\)", j).toInt()
  }

  int mulResult(int i) { result = mulSides(i, 1) * mulSides(i, 2) }

  int total() { result = sum(int i | | mulResult(i)) }

  string findInst(int i) {
    exists(string s | input(s) |
      result = s.regexpFind("(mul\\(\\d+,\\d+\\)|do\\(\\)|don't\\(\\))", i, _)
    )
  }

  predicate isEnabled(int i) {
    i = 0
    or
    isEnabled(i - 1) and findInst(i - 1) != "don't()"
    or
    findInst(i - 1) = "do()"
  }

  int enabledMulSides(int i, int j) {
    isEnabled(i) and
    result = findInst(i).regexpCapture("mul\\((\\d+),(\\d+)\\)", j).toInt()
  }

  int enabledMulResult(int i) { result = enabledMulSides(i, 1) * enabledMulSides(i, 2) }


  int total2() { result = sum(int i | | enabledMulResult(i)) }

}

module TestImpl = Impl<testDay3/1>;

module RealImpl = Impl<realDay3/1>;

select 1
