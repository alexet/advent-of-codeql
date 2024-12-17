import input
import utils

string testData() { result = testData(2024, 13) }

string realData() { result = realData(2024, 13) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  string parts(int i) { result = input().splitAt("\n\n", i) }

  string buttonPart(int i, int j, int p) {
    result = parts(i).splitAt("\n", j).regexpCapture("Button ([A-Z]): X\\+(\\d+), Y\\+(\\d+)", p)
  }

  string prizePart(int i, int j, int p) {
    result = parts(i).splitAt("\n", j).regexpCapture("Prize: X=(\\d+), Y=(\\d+)", p)
  }

  int buttonIndex(int x, string button) { buttonPart(x, result, 1) = button }

  int buttonX(int i, string button) { result = buttonPart(i, buttonIndex(i, button), 2).toInt() }

  int buttonY(int i, string button) { result = buttonPart(i, buttonIndex(i, button), 3).toInt() }

  int prizeX(int i) { result = prizePart(i, _, 1).toInt() }

  int prizeY(int i) { result = prizePart(i, _, 2).toInt() }

  class BigInt = QlBuiltins::BigInt;

  BigInt prizeX2(int i) { result = prizePart(i, _, 1).toBigInt() + "10000000000000".toBigInt() }

  BigInt prizeY2(int i) { result = prizePart(i, _, 2).toBigInt() + "10000000000000".toBigInt() }

  int p1(int game) {
    exists(
      int xa, int ya, int xr, int xb, int yb, int yr, int divisor, int aDiv, int bDiv, int a, int b
    |
      xa = buttonX(game, "A") and
      ya = buttonY(game, "A") and
      xr = prizeX(game) and
      xb = buttonX(game, "B") and
      yb = buttonY(game, "B") and
      yr = prizeY(game) and
      divisor = xa * yb - xb * ya and
      aDiv = xr * yb - yr * xb and
      bDiv = yr * xa - xr * ya and
      a = aDiv / divisor and
      b = bDiv / divisor and
      bDiv % divisor = 0 and
      aDiv % divisor = 0 and
      result = 3 * a + b
    )
  }

  BigInt p2(int game) {
    exists(
      BigInt xa, BigInt ya, BigInt xr, BigInt xb, BigInt yb, BigInt yr, BigInt divisor, BigInt aDiv,
      BigInt bDiv, BigInt a, BigInt b
    |
      xa = buttonX(game, "A").toBigInt() and
      ya = buttonY(game, "A").toBigInt() and
      xr = prizeX2(game) and
      xb = buttonX(game, "B").toBigInt() and
      yb = buttonY(game, "B").toBigInt() and
      yr = prizeY2(game) and
      divisor = xa * yb - xb * ya and
      aDiv = xr * yb - yr * xb and
      bDiv = yr * xa - xr * ya and
      a = aDiv / divisor and
      b = bDiv / divisor and
      bDiv % divisor = 0.toBigInt() and
      aDiv % divisor = 0.toBigInt() and
      result = 3.toBigInt() * a + b and
      a > 0.toBigInt() and
      b > 0.toBigInt()
    )
  }

  int totalCost() { result = sum(int i | | p1(i)) }

  BigInt totalCost2() { result = sum(int i | | p2(i)) }
}

select 1
