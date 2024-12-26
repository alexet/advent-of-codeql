/**
 * @kind graph
 * @id aoc/2024/24
 */

import input
import utils

string testData() { result = testData(2024, 24) }

string realData() { result = realData(2024, 24) }

//module TestImpl = Impl<testData/0>;
module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  string constants() { result = input().splitAt("\n\n", 0) }

  boolean constant(string constant) {
    exists(string line |
      line = constants().splitAt("\n", _) and
      constant = line.splitAt(": ", 0) and
      result = intToBool(line.splitAt(": ", 1).toInt())
    )
  }

  boolean intToBool(int n) {
    n = 1 and result = true
    or
    n = 0 and result = false
  }

  int boolToInt(boolean b) { b = intToBool(result) }

  string rules() { result = input().splitAt("\n\n", 1) }

  string rule(int n) { result = rules().splitAt("\n", n) }

  string rulePart(int n, int k) { result = rule(n).splitAt(" ", k) }

  predicate rule(string lhs, string op, string rhs, string out) {
    exists(int n |
      lhs = rulePart(n, 0) and
      op = rulePart(n, 1) and
      rhs = rulePart(n, 2) and
      out = rulePart(n, 4)
    )
  }

  boolean value(string val) {
    result = constant(val)
    or
    exists(string lhs, string op, string rhs |
      rule(lhs, op, rhs, val) and
      (
        op = "AND" and result = value(lhs).booleanAnd(value(rhs))
        or
        op = "OR" and result = value(lhs).booleanOr(value(rhs))
        or
        op = "XOR" and result = value(lhs).booleanXor(value(rhs))
      )
    )
  }

  class BigInt = QlBuiltins::BigInt;

  BigInt value() {
    result =
      sum(string s, int n |
        value(s) = true and
        "z" + any(string s2 | s2.toInt() = n) = s
      |
        2.toBigInt().pow(n)
      )
  }

  predicate hasNode(string s) {
    exists(constant(s)) or
    rule(_, _, _, s)
  }

  newtype TNode =
    MkNode(string s) {
      exists(constant(s)) or
      rule(_, _, _, s)
    }

  class Node extends TNode {
    string rule;

    Node() { this = MkNode(rule) }

    string getKind() {
      result = constant(rule).toString() or
      rule(_, result, _, rule)
    }

    string toString() { result = rule + ": " + getKind() }

    string getRule() { result = rule }

    Node getInput() {
      rule(result.getRule(), _, _, rule) or
      rule(_, _, result.getRule(), rule)
    }
  }

  string xIn(int n) {
    exists(constant(result)) and
    "x" + any(string s2 | s2.toInt() = n) = result
  }

  string yIn(int n) {
    exists(constant(result)) and
    "y" + any(string s2 | s2.toInt() = n) = result
  }

  predicate swap(string a, string b) {
    a = "svm" and b = "nbc"
    or
    a = "kqk" and b = "z15"
    or
    a = "cgq" and b = "z23"
    or
    a = "fnr" and b = "z39"
  }

  string inSwap() {
    swap(_, result) or swap(result, _)
  }

  string p2() {
    result = concat(string s | s = inSwap()  | s, ",")
  }

  string swapped(string a) {
    swap(a, result)
    or
    swap(result, a)
    or
    not swap(a, _) and not swap(_, a) and result = a and hasNode(a)
  }

  predicate symRule(string lhs, string op, string rhs, string out) {
    rule(lhs, op, rhs, swapped(out)) or
    rule(rhs, op, lhs, swapped(out))
  }

  string halfCarry(int n) { symRule(xIn(n), "AND", yIn(n), result) }

  string halfAdder(int n) { symRule(xIn(n), "XOR", yIn(n), result) }

  string otherHalfCarry(int n) { symRule(halfAdder(n), "AND", carry(n - 1), result) }

  string carry(int n) {
    n = 0 and result = halfCarry(0)
    or
    symRule(halfCarry(n), "OR", otherHalfCarry(n), result)
  }
}

// 0011111101000
// 0011111101000
from RealImpl::Node n1, RealImpl::Node n2
where n2.getInput() = n1
select n1, n2
