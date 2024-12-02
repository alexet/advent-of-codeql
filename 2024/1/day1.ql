extensible predicate testDay1(string data);

extensible predicate realDay1(string data);

import utils

module Impl<inputSig/1 input> {
  import Helpers<input/1>

  int lhs(int i) { result = part(i, 1).toInt() }

  int rhs(int i) { result = part(i, 2).toInt() }

  int lhsRanked(int i) { result = rank[i](int j | | lhs(j) as res order by res, j) }

  int rhsRanked(int i) { result = rank[i](int j | | rhs(j) as res order by res, j) }

  int distance(int i) { result = (lhsRanked(i) - rhsRanked(i)).abs() }

  int totalDistance() { result = sum(int i | | distance(i)) }

  bindingset[i]
  int rhsOccurs(int i) { result = count(int j | rhs(j) = i) }

  int crossOccurFactor() { result = sum(int i | | lhs(i) * rhsOccurs(lhs(i))) }
}

module TestImpl = Impl<testDay1/1>;

module RealImpl = Impl<realDay1/1>;

from string s
where testDay1(s)
select s
