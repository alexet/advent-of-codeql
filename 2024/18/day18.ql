import input
import utils

string testData() { result = testData(2024, 18) }

string realData() { result = realData(2024, 18) }

signature predicate size(int x, int y);

predicate testSize(int x, int y) { x = 6 and y = 6 }

predicate realSize(int x, int y) { x = 70 and y = 70 }

int testLimit() { result = 12 }

int realLimit() { result = 1024 }

signature int byteLimit();

module TestImpl = Impl<testData/0, testSize/2, testLimit/0>;

module RealImpl = Impl<realData/0, realSize/2, realLimit/0>;

module Impl<inputSig/0 input, size/2 memSize, byteLimit/0 byteLim> {
  import Helpers<input/0>

  predicate badByte(int x, int y) {
    exists(int n |
      x = line(n).splitAt(",", 0).toInt() and
      y = line(n).splitAt(",", 1).toInt() and
      n < byteLim()
    )
  }

  predicate usefulMem(int x, int y) {
    exists(int maxX, int maxY |
      memSize(maxX, maxY) and
      x in [0 .. maxX] and
      y in [0 .. maxY]
    ) and
    not badByte(x, y)
  }

  newtype TGoodMem = MkGoodMem(int x, int y) { usefulMem(x, y) }

  class GoodMem extends TGoodMem {
    int x;
    int y;

    GoodMem() { this = MkGoodMem(x, y) }

    int getX() { result = x }

    int getY() { result = y }

    GoodMem getANeighbour() {
      result = MkGoodMem(x + 1, y) or
      result = MkGoodMem(x - 1, y) or
      result = MkGoodMem(x, y + 1) or
      result = MkGoodMem(x, y - 1)
    }

    string toString() { result = "GoodMem(" + x + ", " + y + ")" }
  }

  GoodMem getANeighbour(GoodMem m) { result = m.getANeighbour() }

  GoodMem start() { result.getX() = 0 and result.getY() = 0 }

  GoodMem end() { memSize(result.getX(), result.getY()) }

  string image() {
    result =
      "\n" +
        concat(int y |
          |
          strictconcat(int x |
              |
              any(string s |
                  usefulMem(x, y) and s = "."
                  or
                  badByte(x, y) and s = "#"
                )
              order by
                x
            ), "\n"
          order by
            y
        )
  }

  int distance(GoodMem mem) = shortestDistances(start/0, getANeighbour/1)(_, mem, result)

  int finalDist() { result = distance(end()) }

  int maxBad() { result = max(int n | exists(line(n))) }

  newtype TPos =
    MkPos(int x, int y) {
      exists(int maxX, int maxY |
        memSize(maxX, maxY) and
        x in [0 .. maxX] and
        y in [0 .. maxY]
      )
    }

  class Pos extends TPos {
    int x;
    int y;

    Pos() { this = MkPos(x, y) }

    Pos getANeighbour() {
      result = MkPos(x + 1, y) or
      result = MkPos(x - 1, y) or
      result = MkPos(x, y + 1) or
      result = MkPos(x, y - 1)
    }

    int getX() { result = x }

    int getY() { result = y }

    predicate isEnd() {
      memSize(x, y)
    }

    predicate fallsAt(int n) {
      x = line(n).splitAt(",", 0).toInt() and
      y = line(n).splitAt(",", 1).toInt()
    }
    

    predicate badAt(int n) {
      exists(int n2 |
        this.fallsAt(n2) and
        n in [n2 .. maxBad()]
      )
    }

    string toString() { result = "Pos(" + x + ", " + y + ")" }
  }

  Pos reachable(int n) {
    result = MkPos(0, 0) and n in [0..maxBad()] 
    or
    result = reachable(n).getANeighbour() and not (result.badAt(n)  )
  }

  predicate reachedEnd(int iter) {
    reachable(iter).isEnd()
  }

  int maxReachable() {
    result = max(int n | reachedEnd(n))
  }

  Pos lastPos() {
    result.fallsAt(maxReachable() + 1)
  }

  string lastPosString() {
    result =lastPos().getX() + "," + lastPos().getY()
  }
  
}

select 1
