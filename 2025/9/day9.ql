import input
import utils

string testData() { result = testData(2025, 9) }

string realData() { result = realData(2025, 9) }

module TestImpl = Impl<testData/0, maxEdgesTest/0>;

module RealImpl = Impl<realData/0, maxEdgesReal/0>;

int maxEdgesTest() { result = 10 }

int maxEdgesReal() { result = 1000 }

signature int intPred();

module Impl<inputSig/0 input, intPred/0 maxEdges> {
  import Helpers<input/0>

  predicate redTile(int n, int x, int y) {
    exists(string tileString | tileString = line(n) |
      x = tileString.splitAt(",", 0).toInt() and
      y = tileString.splitAt(",", 1).toInt()
    )
  }

  BigInt maxDistance() {
    result =
      max(BigInt x1, BigInt x2, BigInt y1, BigInt y2 |
        redTile(_, x1.toInt(), y1.toInt()) and redTile(_, x2.toInt(), y2.toInt())
      |
        (((x1 - x2).abs() + 1.toBigInt()) * ((y1 - y2).abs() + 1.toBigInt()))
      )
  }

  newtype TTilePair =
    MkTilePair(int n1, int n2, int x1, int y1, int x2, int y2) {
      redTile(n1, x1, y1) and
      redTile(n2, x2, y2)
    }

  class TilePair extends TTilePair {
    int x1;
    int y1;
    int x2;
    int y2;
    int n1;
    int n2;

    TilePair() { this = MkTilePair(n1, n2, x1, y1, x2, y2) }

    string toString() { result = "(" + x1 + "," + y1 + "), (" + x2 + "," + y2 + ")" }

    BigInt rectangleSize() {
      result =
        ((x1.toBigInt() - x2.toBigInt()).abs() + 1.toBigInt()) *
          ((y1.toBigInt() - y2.toBigInt()).abs() + 1.toBigInt())
    }

    predicate isConsecutative() {
      n2 = n1 + 1
      or
      n1 = max(int n | redTile(n, _, _)) and
      n2 = 0
    }

    predicate isVerticalEdge() { x1 = x2 and isConsecutative() }

    int getX1() { result = x1 }

    int getX2() { result = x2 }

    int getY1() { result = y1 }

    int getY2() { result = y2 }

    predicate matchVert(int x, int ymin, int ymax) {
      ymin = y1.minimum(y2) and
      ymax = y1.maximum(y2) and
      x = x1 and
      x = x2
    }

    predicate matchHoriz(int xmin, int xmax, int y) {
      xmin = x1.minimum(x2) and
      xmax = x1.maximum(x2) and
      y = y1 and
      y = y2
    }

    predicate isHorizontalEdge() { y1 = y2 and isConsecutative() }

    pragma[noinline]
    string invalidRect() {
      hasVertIntersection(x1.minimum(x2), y1, y2) and result = "V1"
      or
      hasVertIntersection(x1.maximum(x2), y1, y2) and result = "V2"
      or
      hasHorizIntersection(x1, x2, y1.minimum(y2)) and result = "H1"
      or
      hasHorizIntersection(x1, x2, y1.minimum(y2)) and result = "H2"
    }

    predicate validRect() {
      not exists(invalidRect()) and
      isGreenOrRed(x1, y2) and
      isGreenOrRed(x2, y1)
    }
  }

  TilePair maxValidRect() {
    result = max(TilePair tp | tp.validRect() | tp order by tp.rectangleSize())
  }

  BigInt result2() { result = maxValidRect().rectangleSize() }

  int xCounts() { result = max(int x | | strictcount(int n | redTile(n, x, _))) }

  int yCounts() { result = max(int x | | strictcount(int n | redTile(n, x, _))) }

  // NOTE onyl possible edge cases come from point itself
  // no other coordinates match
  bindingset[x1, x2, y]
  predicate hasHorizIntersection(int x1, int x2, int y) {
    exists(TilePair t, int tx, int tymin, int tymax |
      t.matchVert(tx, tymin, tymax) and
      (
        tymin < y and
        y < tymax and
        x1.minimum(x2) < tx and
        tx < x1.maximum(x2)
      )
    )
  }

  // NOTE only possible edge cases come from point itself
  // no other coordinates match
  // So we just the two conrners as well
  bindingset[x, y1, y2]
  pragma[inline_late]
  predicate hasVertIntersection(int x, int y1, int y2) {
    exists(TilePair t, int txmin, int txmax, int ty |
      t.matchHoriz(txmin, txmax, ty) and
      (
        y1.minimum(y2) < ty and
        ty < y1.maximum(y2) and
        txmin < x and
        x < txmax
      )
    )
  }

  pragma[noinline]
  predicate isGreenOrRed(int x, int y) {
    exists(int case |
      redTile(_, _, y) and
      redTile(_, x, _) and
      sum(TilePair p |
        p.isVerticalEdge() and
        x < p.getX1()
      |
        lineWeight(p, y)
      ) = case and
      case != 0
    )
  }

  int lineWeight(TilePair t, int y) {
    redTile(_, _, y) and
    (
      // Down edge,
      //  G|.
      //  Gv.
      //  G|.
      // Inside (2) to outside (0)
      t.isVerticalEdge() and
      t.getY2() < y and
      y < t.getY1() and
      result = -2
      or
      // Up edge
      //  .|G
      //  .^G
      //  .|G
      // Outside (2) to inside (1)
      t.isVerticalEdge() and
      t.getY1() < y and
      y < t.getY2() and
      result = 2
      or
      // start corner down
      // ...
      // -*.
      // Gv.
      // or
      // GGG
      // G*-
      // Gv.
      t.isVerticalEdge() and
      y = t.getY1() and
      y > t.getY2() and
      result = -1
      or
      // start Corner up
      // .^G
      // -*G
      // GGG
      // or
      // .^G
      // .*-
      // ...
      t.isVerticalEdge() and
      y = t.getY1() and
      y < t.getY2() and
      result = 1
      or
      // end Corner down
      // Gv.
      // -*.
      // ...
      // or
      // Gv.
      // G*-
      // GGG
      t.isVerticalEdge() and
      y = t.getY2() and
      y < t.getY1() and
      result = -1
      or
      // end Corner up
      // GGG
      // -*G
      // .^G
      // or
      // ...
      // .*-
      // .^G
      t.isVerticalEdge() and
      y = t.getY2() and
      y > t.getY1() and
      result = 1
    )
  }
}

select 1
