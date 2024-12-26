import input
import utils

string testData() { result = testData(2024, 21) }

string realData() { result = realData(2024, 21) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  newtype TNumPadPos =
    MkNumPadPos(int x, int y) {
      x in [0 .. 2] and
      y in [0 .. 3] and
      not (x = 0 and y = 3)
    }

  class NumPadPos extends TNumPadPos {
    int x;
    int y;

    NumPadPos() { this = MkNumPadPos(x, y) }

    int getX() { result = x }

    int getY() { result = y }

    predicate canHorizThenVert(NumPadPos end) { not (end.getX() = 0 and this.getY() = 3) }

    predicate canVertThenHoriz(NumPadPos end) { not (this.getX() = 0 and end.getY() = 3) }

    string getValue() {
      if y < 3
      then result = ((x) + (2 - y) * 3 + 1).toString()
      else (
        x = 1 and result = "0"
        or
        x = 2 and result = "A"
      )
    }

    string toString() { result = x.toString() + ", " + y.toString() }
  }

  newtype TDirPadPos =
    MkDirPadPos(int x, int y) {
      x = 1 and y = 0
      or
      x = 2 and y = 0
      or
      x = 0 and y = 1
      or
      x = 1 and y = 1
      or
      x = 2 and y = 1
    }

  class DirPadPos extends TDirPadPos {
    int x;
    int y;

    DirPadPos() { this = MkDirPadPos(x, y) }

    int getX() { result = x }

    int getY() { result = y }

    string getValue() {
      x = 1 and y = 0 and result = "^"
      or
      x = 2 and y = 0 and result = "A"
      or
      x = 0 and y = 1 and result = "<"
      or
      x = 1 and y = 1 and result = "v"
      or
      x = 2 and y = 1 and result = ">"
    }

    predicate canHorizThenVert(DirPadPos end) { not (end.getX() = 0 and this.getY() = 0) }

    predicate canVertThenHoriz(DirPadPos end) { not (this.getX() = 0 and end.getY() = 0) }

    string toString() { result = x.toString() + ", " + y.toString() + "(" + getValue() + ")" }
  }

  class BigInt = QlBuiltins::BigInt;

  signature module CostModule {
    class Pos {
      int getX();

      int getY();

      predicate canHorizThenVert(Pos end);

      predicate canVertThenHoriz(Pos end);

      string toString();
    }

    BigInt cost(DirPadPos start, DirPadPos end);
  }

  module CostInfer<CostModule PrevCost> {
    class Pos = PrevCost::Pos;

    predicate prevCost = PrevCost::cost/2;

    BigInt prevCostS(string s1, string s2) { result = prevCost(getDirPadFor(s1), getDirPadFor(s2)) }

    predicate parts(
      Pos start, Pos end, string horizMove, string vertMove, BigInt horizAmount, BigInt vertAmount
    ) {
      (if start.getX() < end.getX() then horizMove = ">" else horizMove = "<") and
      (if start.getY() < end.getY() then vertMove = "v" else vertMove = "^") and
      horizAmount = (start.getX() - end.getX()).abs().toBigInt() and
      vertAmount = (start.getY() - end.getY()).abs().toBigInt()
    }

    BigInt possibleCost(Pos start, Pos end, string kind) {
      exists(string horizMove, string vertMove, BigInt horizAmount, BigInt vertAmount |
        parts(start, end, horizMove, vertMove, horizAmount, vertAmount) and
        (
          start.canHorizThenVert(end) and
          result =
            prevCostS("A", horizMove) + horizAmount + prevCostS(horizMove, vertMove) + vertAmount +
              prevCostS(vertMove, "A") and
          kind = "HV"
          or
          start.canVertThenHoriz(end) and
          result =
            prevCostS("A", vertMove) + vertAmount + prevCostS(vertMove, horizMove) + horizAmount +
              prevCostS(horizMove, "A") and
          kind = "VH"
          or
          horizAmount = 0.toBigInt() and
          result = prevCostS("A", vertMove) + vertAmount + prevCostS(vertMove, "A") and
          kind = "V"
          or
          vertAmount = 0.toBigInt() and
          result = prevCostS("A", horizMove) + horizAmount + prevCostS(horizMove, "A") and
          kind = "H"
          or
          horizAmount = 0.toBigInt() and
          vertAmount = 0.toBigInt() and
          result = 0.toBigInt() and
          kind = "0"
        )
      )
    }

    BigInt cost(Pos start, Pos end) { result = min(possibleCost(start, end, _)) }
  }

  module BaseCost implements CostModule {
    class Pos = DirPadPos;

    BigInt cost(DirPadPos start, DirPadPos end) {
      result.toInt() = (start.getX() - end.getX()).abs() + (start.getY() - end.getY()).abs()
    }
  }

  signature BigInt dirCost(DirPadPos start, DirPadPos end);

  module OneStep<dirCost/2 prev> {
    module Inner implements CostModule {
      class Pos = DirPadPos;

      predicate cost = prev/2;
    }

    predicate cost = CostInfer<Inner>::cost/2;
  }

  module TwoStep<dirCost/2 prev> {
    predicate cost = OneStep<OneStep<prev/2>::cost/2>::cost/2;
  }

  module FourStep<dirCost/2 prev> {
    predicate cost = TwoStep<TwoStep<prev/2>::cost/2>::cost/2;
  }

  module EightStep<dirCost/2 prev> {
    predicate cost = FourStep<FourStep<prev/2>::cost/2>::cost/2;
  }

  module SixteenStep<dirCost/2 prev> {
    predicate cost = EightStep<EightStep<prev/2>::cost/2>::cost/2;
  }

  module R25 implements CostModule {
    class Pos = NumPadPos;

    private predicate cost1 = BaseCost::cost/2;

    private predicate cost17 = SixteenStep<cost1/2>::cost/2;

    predicate cost = EightStep<cost17/2>::cost/2;
  }

  module R2 implements CostModule {
    class Pos = NumPadPos;

    private predicate cost1 = BaseCost::cost/2;

    predicate cost = OneStep<cost1/2>::cost/2;
  }

  predicate finalCost1 = CostInfer<R2>::cost/2;

  predicate finalCost2 = CostInfer<R25>::cost/2;

  DirPadPos getDirPadFor(string char) { result.getValue() = char }

  NumPadPos getNumPadFor(string char) { result.getValue() = char }

  BigInt runLength(int n) {
    exists(string s |
      s = line(n) and
      result =
        sum(int i |
          |
          any(BigInt partCost |
              i = 0 and
              partCost = finalCost1(getNumPadFor("A"), getNumPadFor(s.charAt(0))) + 1.toBigInt()
              or
              i > 0 and
              partCost =
                finalCost1(getNumPadFor(s.charAt(i - 1)), getNumPadFor(s.charAt(i))) + 1.toBigInt()
            )
        )
    )
  }

  BigInt runLength2(int n) {
    exists(string s |
      s = line(n) and
      result =
        sum(int i |
          |
          any(BigInt partCost |
              i = 0 and
              partCost = finalCost2(getNumPadFor("A"), getNumPadFor(s.charAt(0))) + 1.toBigInt()
              or
              i > 0 and
              partCost =
                finalCost2(getNumPadFor(s.charAt(i - 1)), getNumPadFor(s.charAt(i))) + 1.toBigInt()
            )
        )
    )
  }

  int numericPart(int n) { result = line(n).regexpCapture("(\\d+).*", 1).toInt() }

  BigInt score() { result = sum(int n | | runLength(n) * numericPart(n).toBigInt()) }

  BigInt score2() { result = sum(int n | | runLength2(n) * numericPart(n).toBigInt()) }
}

select 1
