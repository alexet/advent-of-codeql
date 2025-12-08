import input
import utils

string testData() { result = testData(2025, 8) }

string realData() { result = realData(2025, 8) }

module TestImpl = Impl<testData/0, maxEdgesTest/0>;

module RealImpl = Impl<realData/0, maxEdgesReal/0>;

int maxEdgesTest() { result = 10 }

int maxEdgesReal() { result = 1000 }

signature int intPred();

module Impl<inputSig/0 input, intPred/0 maxEdges> {
  import Helpers<input/0>

  predicate boxes(int n, BigInt x, BigInt y, BigInt z) {
    exists(string line | line = line(n) |
      x = line.splitAt(",", 0).toBigInt() and
      y = line.splitAt(",", 1).toBigInt() and
      z = line.splitAt(",", 2).toBigInt()
    )
  }

  BigInt squareDistanceBetween(int n1, int n2) {
    exists(BigInt x1, BigInt x2, BigInt y1, BigInt y2, BigInt z1, BigInt z2 |
      boxes(n1, x1, y1, z1) and
      boxes(n2, x2, y2, z2) and
      result = (x1 - x2).pow(2) + (y1 - y2).pow(2) + (z1 - z2).pow(2)
    )
  }

  newtype TDistinctBoxPair =
    MkPair(int n1, int n2) {
      n1 < n2 and
      boxes(n1, _, _, _) and
      boxes(n2, _, _, _)
    }

  class DistinctPair extends TDistinctBoxPair {
    int n1;
    int n2;

    DistinctPair() { this = MkPair(n1, n2) }

    string toString() { result = "(" + n1 + "," + n2 + ")" }

    BigInt squareDistanceBetween() {
      exists(BigInt x1, BigInt x2, BigInt y1, BigInt y2, BigInt z1, BigInt z2 |
        boxes(n1, x1, y1, z1) and
        boxes(n2, x2, y2, z2) and
        result = (x1 - x2).pow(2) + (y1 - y2).pow(2) + (z1 - z2).pow(2)
      )
    }

    int distanceRank() {
      this = rank[result](DistinctPair other | | other order by other.squareDistanceBetween())
    }

    predicate isConnected() { distanceRank() <= maxEdges() }

    int getN1() { result = n1 }

    int getN2() { result = n2 }
  }

  predicate connectedNodes(int n1, int n2) {
    exists(DistinctPair p | p.isConnected() | n1 = p.getN1() and n2 = p.getN2())
    or
    n1 = n2 and boxes(n1, _, _, _)
  }

  module CircuitM = QlBuiltins::EquivalenceRelation<int, connectedNodes/2>;

  class Circuit extends CircuitM::EquivalenceClass {
    int getMinBox() { result = min(this.getABox()) }

    int index() { this = rank[result](Circuit other | | other order by other.getMinBox()) }

    int getABox() { this = CircuitM::getEquivalenceClass(result) }

    int size() { result = count(this.getABox()) }

    string toString() {
      result = "{" + concat(int n | n = this.getABox() | n.toString(), "," order by n) + "}"
    }
  }

  int largest3Sizes(int r) {
    r in [1 .. 3] and
    result = rank[r](Circuit n | | n order by n.size() desc, n.index()).size()
  }

  int partialProduct(int n) {
    n = 0 and result = 1
    or
    result = partialProduct(n - 1) * largest3Sizes(n)
  }

  int circuitCount() { result = count(CircuitM::EquivalenceClass ec) }

  int pairCount() { result = count(DistinctPair p) }

  pragma[noinline]
  predicate notDone(int iter) { circuitRepInIter(iter, _) != 0 }

  cached
  int circuitRepInIter(int iter, int n) {
    iter = 0 and result = n and boxes(n, _, _, _)
    or
    notDone(iter - 1) and
    exists(DistinctPair p, int p1, int p2, int p1r, int p2r |
      p.distanceRank() = iter and
      p1 = p.getN1() and
      p2 = p.getN2() and
      p1r = circuitRepInIter(iter - 1, p1) and
      p2r = circuitRepInIter(iter - 1, p2)
    |
      exists(int uR, int prevR | uR = p1r.minimum(p2r) and prevR = circuitRepInIter(iter - 1, n) |
        prevR = p1r and
        result = uR
        or
        prevR = p2r and
        result = uR
        or
        prevR != p1r and
        prevR != p2r and
        result = prevR
      )
    )
  }

  int finalIter() { result = max(int i | notDone(i)) + 1 }

  DistinctPair finalPair() { result.distanceRank() = finalIter() }

  BigInt finalResult() {
    exists(int n1, int n2, BigInt x1, BigInt x2 |
      n1 = finalPair().getN1() and
      n2 = finalPair().getN2() and
      boxes(n1, x1, _, _) and
      boxes(n2, x2, _, _) and
      result = x1 * x2
    )
  }
}

select 1
