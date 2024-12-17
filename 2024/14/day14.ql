import input
import utils

string testData() { result = testData(2024, 14) }

string realData() { result = realData(2024, 14) }

signature predicate size(int x, int y);

predicate testSize(int x, int y) { x = 11 and y = 7 }

predicate realSize(int x, int y) { x = 101 and y = 103 }

//module TestImpl = Impl<testData/0, testSize/2>;
module RealImpl = Impl<realData/0, realSize/2>;

module Impl<inputSig/0 input, size/2 roomSize> {
  import Helpers<input/0>

  string getPart(int n, int k) {
    result = line(n).regexpCapture("p=(\\d+),(\\d+) v=(-?\\d+),(-?\\d+)", k)
  }

  int roomWidth() { roomSize(result, _) }

  int roomHeight() { roomSize(_, result) }

  predicate isStart(int n, int x, int y) {
    x = getPart(n, 1).toInt() and
    y = getPart(n, 2).toInt()
  }

  predicate isVelocity(int n, int dx, int dy) {
    dx = getPart(n, 3).toInt() and
    dy = getPart(n, 4).toInt()
  }

  bindingset[x, y]
  int posMod(int x, int y) { result = ((x % y) + y) % y }

  int maxIter() { result = 10000 }

  predicate posAfter(int n, int i, int x, int y) {
    i in [0 .. maxIter()] and
    exists(int sx, int sy, int dx, int dy |
      isStart(n, sx, sy) and
      isVelocity(n, dx, dy) and
      x = posMod(sx + i * dx, roomWidth()) and
      y = posMod(sy + i * dy, roomHeight())
    )
  }

  predicate posAfter100(int n, int x, int y) { posAfter(n, 100, x, y) }

  int halfWidth() { result = roomWidth() / 2 }

  int halfHeight() { result = roomHeight() / 2 }

  bindingset[x, y]
  string sector(int x, int y) {
    x < halfWidth() and y < halfHeight() and result = "NW"
    or
    x > halfWidth() and y < halfHeight() and result = "NE"
    or
    x < halfWidth() and y > halfHeight() and result = "SW"
    or
    x > halfWidth() and y > halfHeight() and result = "SE"
  }

  string finalSector(int n) {
    exists(int x, int y |
      posAfter100(n, x, y) and
      sector(x, y) = result
    )
  }

  string sectorAt(int n, int k) {
    exists(int x, int y |
      posAfter(n, k, x, y) and
      sector(x, y) = result
    )
  }

  int sectorScore(string sector) {
    sector in ["NW", "NE", "SW", "SE"] and
    result = count(int n | finalSector(n) = sector)
  }

  int sectorScoreAt(int k, string sector) {
    sector in ["NW", "NE", "SW", "SE"] and
    k in [0 .. maxIter()] and
    result = count(int n | sectorAt(n, k) = sector)
  }

  int score() {
    result = sectorScore("NW") * sectorScore("NE") * sectorScore("SW") * sectorScore("SE")
  }

  int scoreAt(int k) {
    result = sectorScoreAt(k, "NW") * sectorScoreAt(k, "NE") * sectorScoreAt(k, "SW") * sectorScoreAt(k, "SE")
  }

  int robotCount(int i, int x, int y) {
    i in [0 .. maxIter()] and
    x in [0 .. roomWidth()] and
    y in [0 .. roomHeight()] and
    result = count(int n | posAfter(n, i, x, y))
  }

  string prettyCount(int i, int x, int y) {
    exists(int rCount |
      robotCount(i, x, y) = rCount and
      (
        rCount = 0 and result = " "
        or
        rCount = 1 and result = "#"
        or
        rCount > 1 and result = rCount.toString()
      )
    )
  }

  string image(int i) {
    result =
      strictconcat(int y |
        |
        strictconcat(int x | | prettyCount(i, x, y) order by x), "\n" order by y
      )
  }

  string allImages() {
    result = strictconcat(int i | | i.toString() + "\n" + image(i), "\n\n" order by i)
  }

  int highColumn(int i) {
    result = max(int x | | strictsum(int y | y in [0 .. roomHeight()] | robotCount(i, x, y)))
  }

  int highRow(int i) {
    result = max(int y | | strictsum(int x | x in [0 .. roomWidth()] | robotCount(i, x, y)))
  }
}

select 1
