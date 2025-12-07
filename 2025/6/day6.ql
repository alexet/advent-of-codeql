import input
import utils

string testData() { result = testData(2025, 6) }

string realData() { result = realData(2025, 6) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  string part(int i, int j) { result = line(i).regexpFind("\\S+", j, _) }

  string type(int j) {
    exists(int index | index = max(int i | exists(part(i, j))) | result = part(index, j))
  }

  int inputs(int i, int j) { result = part(i, j).toInt() }

  BigInt partialProduct(int j, int i) {
    i = 0 and result = inputs(0, j).toBigInt()
    or
    result = partialProduct(j, i - 1) * inputs(i, j).toBigInt()
  }

  BigInt product(int j) { result = partialProduct(j, max(int i | exists(inputs(i, j)))) }

  BigInt exprResult(int j) {
    type(j) = "+" and
    result = sum(int i | | inputs(i, j).toBigInt())
    or
    type(j) = "*" and
    result = product(j)
  }

  BigInt totalSum() { result = sum(int j | | exprResult(j)) }

  predicate spacerColumn(int y) { forex(int x | exists(charGrid(y, x)) | charGrid(y, x) = " ") }

  int rankedSpacerColumn(int j) {
    result = rank[j](int y | spacerColumn(y))
    or
    j = 0 and result = -1
    or
    j = count(int y | spacerColumn(y)) +1 and result = line(0).length()
  }

  int maxRow() { result = max(int x | exists(charGrid(_, x))) }

  string type2(int j) {
    result =
      rank[j + 1](int y, string res | res = charGrid(y, maxRow()) and res != " " | res order by y)
  }

  int column(int y) {
    result = strictconcat(int x | x != maxRow() | charGrid(y, x) order by x).trim().toInt()
  }

  int inputs2(int j, int i) {
    result =
      rank[i + 1](int y |
        y in [rankedSpacerColumn(j) .. rankedSpacerColumn(j + 1)]
      |
        column(y) order by y
      )
  }

  BigInt partialProduct2(int j, int i) {
    i = 0 and result = inputs2(j,0).toBigInt()
    or
    result = partialProduct2(j, i - 1) * inputs2(j, i).toBigInt()
  }
  BigInt product2(int j) { result = partialProduct2(j, max(int i | exists(inputs2(j, i)))) }

  BigInt exprResult2(int j) {
    type2(j) = "+" and
    result = strictsum(int i | | inputs2(j, i).toBigInt())
    or
    type2(j) = "*" and
    result = product2(j)
  }

    BigInt totalSum2() { result = strictsum(int j | | exprResult2(j)) }
}

select 1
