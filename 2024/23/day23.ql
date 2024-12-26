/**
 * @kind graph
 * @id aoc/2024/23
 */

import input
import utils

string testData() { result = testData(2024, 23) }

string realData() { result = realData(2024, 23) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  predicate connected(string lhs, string rhs) {
    exists(string line |
      line = line(_) and
      lhs = line.splitAt("-", 0) and
      rhs = line.splitAt("-", 1)
    )
  }

  predicate connectedEither(string lhs, string rhs) { connected(lhs, rhs) or connected(rhs, lhs) }

  predicate triple(string a, string b, string c) {
    connectedEither(a, b) and
    connectedEither(b, c) and
    connectedEither(c, a) and
    a < b and
    b < c
  }

  int p1() {
    result =
      count(string a, string b, string c |
        triple(a, b, c) and
        (a.charAt(0) = "t" or b.charAt(0) = "t" or c.charAt(0) = "t")
      )
  }

  newtype TClique =
    Empty() or
    Add(string add, Clique rest) { add = rest.canAdd() }

  class Clique extends TClique {
    string toString() {
      this = Empty() and result = ""
      or
      exists(string add, Clique rest |
        this = Add(add, rest) and
        result = add + "," + rest.toString()
      )
    }

    string canAdd() {
      this = Empty() and connectedEither(result, _)
      or
      exists(string add, Clique rest |
        result = rest.canAdd() and
        result < add and
        this = Add(add, rest) and
        connectedEither(result, add)
      )
    }

    int length() {
      this = Empty() and result = 0
      or
      exists(string add, Clique rest |
        this = Add(add, rest) and
        result = 1 + rest.length()
      )
    }
  }

  Clique largestClique() {
    result = max(Clique c | | c order by c.length())
  }
}



from string lhs, string rhs
where TestImpl::connected(lhs, rhs)
select lhs, rhs
