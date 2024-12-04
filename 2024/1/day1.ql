import input
import utils

string testData() { result = testData(2024, 1) }

string realData() { result = realData(2024, 1) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>


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

select 1