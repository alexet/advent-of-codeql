import inputEC
import utils

string testData() { result = testData(2025, 2) }

string realData() { result = realData(2025, 2) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

class BigInt = QlBuiltins::BigInt;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  string rawAccum() { result = line(0).splitAt("=", 1) }

  string rawAccumStripped() { result = rawAccum().substring(1, rawAccum().length() - 1) }

  BigInt accumX() { result = rawAccumStripped().splitAt(",", 0).toBigInt() }

  BigInt accumY() { result = rawAccumStripped().splitAt(",", 1).toBigInt() }

  bindingset[x1, x2, y1, y2]
  predicate add(BigInt x1, BigInt y1, BigInt x2, BigInt y2, BigInt xres, BigInt yres) {
    xres = x1 + x2 and
    yres = y1 + y2
  }

  bindingset[x1, x2, y1, y2]
  predicate mult(BigInt x1, BigInt y1, BigInt x2, BigInt y2, BigInt xres, BigInt yres) {
    xres = x1 * x2 - y1 * y2 and
    yres = x1 * y2 + x2 * y1
  }

  bindingset[x1, x2, y1, y2]
  predicate div(BigInt x1, BigInt y1, BigInt x2, BigInt y2, BigInt xres, BigInt yres) {
    xres = x1 / x2 and
    yres = y1 / y2
  }

  int maxIter() { result = 3 }

  int maxIterP2() { result = 100 }

  predicate resultAfterIter(int iter, BigInt x, BigInt y) {
    iter = 0 and x = 0.toBigInt() and y = 0.toBigInt()
    or
    iter > 0 and
    iter <= maxIter() and
    exists(BigInt x1, BigInt x2, BigInt x3, BigInt y1, BigInt y2, BigInt y3 |
      resultAfterIter(iter - 1, x1, y1) and
      mult(x1, y1, x1, y1, x2, y2) and // R = R * R
      div(x2, y2, 10.toBigInt(), 10.toBigInt(), x3, y3) and // R = R / [10,10]
      add(x3, y3, accumX(), accumY(), x, y) // R = R + A
    )
  }

  predicate resultAtMaxIter(BigInt x, BigInt y) { resultAfterIter(maxIter(), x, y) }

  string resultString() {
    exists(BigInt x, BigInt y |
      resultAtMaxIter(x, y) and
      result = "[" + x.toString() + "," + y.toString() + "]"
    )
  }

  predicate pointP2(BigInt x, BigInt y) {
    x = accumX() + ([0 .. 100] * 10).toBigInt() and
    y = accumY() + ([0 .. 100] * 10).toBigInt()
  }

  predicate pointP3(BigInt x, BigInt y) {
    x = accumX() + ([0 .. 1000]).toBigInt() and
    y = accumY() + ([0 .. 1000]).toBigInt()
  }

  signature predicate pointSig(BigInt x, BigInt y);

  module IterP2 = IterImpl<pointP2/2>;

  module IterP3 = IterImpl<pointP3/2>;

  module IterImpl<pointSig/2 point> {
    bindingset[prevX, prevY, posX, posY]
    predicate iterStepP2(
      BigInt prevX, BigInt prevY, BigInt resX, BigInt resY, BigInt posX, BigInt posY
    ) {
      exists(BigInt x1, BigInt x2, BigInt y1, BigInt y2 |
        mult(prevX, prevY, prevX, prevY, x1, y1) and // R = R * R
        div(x1, y1, 100000.toBigInt(), 100000.toBigInt(), x2, y2) and // R = R / [100000,100000]
        add(x2, y2, posX, posY, resX, resY) // R = R + pos
      )
    }

    predicate resultAfterIterP2(int iter, BigInt posX, BigInt posY, BigInt x, BigInt y) {
      iter = 0 and x = 0.toBigInt() and y = 0.toBigInt() and point(posX, posY)
      or
      iter > 0 and
      iter <= maxIterP2() and
      exists(BigInt prevX, BigInt prevY |
        resultAfterIterP2(iter - 1, posX, posY, prevX, prevY) and
        exists(BigInt x1, BigInt x2, BigInt y1, BigInt y2 |
          mult(prevX, prevY, prevX, prevY, x1, y1) and // R = R * R
          div(x1, y1, 100000.toBigInt(), 100000.toBigInt(), x2, y2) and // R = R / [100000,100000]
          add(x2, y2, posX, posY, x, y) // R = R + pos
        ) and
        x < 1000000.toBigInt() and
        y < 1000000.toBigInt() and
        x > -1000000.toBigInt() and
        y > -1000000.toBigInt()
      )
    }

    predicate resultAtMaxIterP2(BigInt posX, BigInt posY, BigInt x, BigInt y) {
      resultAfterIterP2(maxIterP2(), posX, posY, x, y)
    }

    int resultCount() {
      result =
        count(BigInt posX, BigInt posY, BigInt x, BigInt y | resultAtMaxIterP2(posX, posY, x, y))
    }
  }
}

select 1
