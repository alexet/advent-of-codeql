import input
import utils

string testData() { result = testData(2024, 20) }

string realData() { result = realData(2024, 20) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  newtype TPos = MkPos(int x, int y) { exists(charGrid(x, y)) }

  class Pos extends TPos {
    int x;
    int y;

    Pos() { this = MkPos(x, y) }

    string kind() { result = charGrid(x, y) }

    int getX() { result = x }

    int getY() { result = y }

    predicate isWall() { kind() = "#" }

    Pos getANeighbour() { result = getNeighbour(_) }

    Pos getNeighbour(Dir4 dir) { result = MkPos(x + dir.dx(), y + dir.dy()) }

    Pos getANonWallNeighbour() { result = getANeighbour() and not isWall() }

    pragma[inline]
    int getDistance(Pos p) { result = (x - p.getX()).abs() + (y - p.getY()).abs() }

    string toString() { result = x.toString() + ", " + y.toString() }
  }

  Pos start() { result.kind() = "S" }

  Pos end() { result.kind() = "E" }

  Pos getANonWallNeighbour(Pos p) { result = p.getANonWallNeighbour() }

  int distanceFromStart(Pos p) = shortestDistances(start/0, getANonWallNeighbour/1)(_, p, result)

  int distanceToEnd(Pos p) = shortestDistances(end/0, getANonWallNeighbour/1)(_, p, result)

  Pos wallCrossFrom(Pos p) {
    exists(Dir4 dir, Pos mid |
      mid = p.getNeighbour(dir) and
      mid.isWall() and
      mid.getNeighbour(dir) = result and
      not p.isWall() and
      not result.isWall()
    )
  }


  

  Pos cheatP2(Pos p) {
    not p.isWall() and
    not result.isWall() and 
    result.getDistance(p) in [2..20]
  }

  int cost() {
    result = distanceFromStart(end())
  }

  int cheatCost(Pos skipStart, Pos skipEnd) {
    wallCrossFrom(skipStart) = skipEnd and
    result = distanceFromStart(skipStart) + distanceToEnd(skipEnd) + 2
  }


  int cheatP2Cost(Pos skipStart, Pos skipEnd) {
    cheatP2(skipStart) = skipEnd and
    result = distanceFromStart(skipStart) + distanceToEnd(skipEnd) + skipStart.getDistance(skipEnd)
  }

  int cheatSaving(Pos skipStart, Pos skipEnd) {
    result = cost() - cheatCost(skipStart, skipEnd)
  }

  int cheatSavingP2(Pos skipStart, Pos skipEnd) {
    result = cost() - cheatP2Cost(skipStart, skipEnd)
  }

  int cheatSavignCount(int saving) {
    result = strictcount(Pos s1, Pos s2 |  saving = cheatSaving(s1, s2))
  }

  int cheatSavignCountP2(int saving) {
    result = strictcount(Pos s1, Pos s2 |  saving = cheatSavingP2(s1, s2))
  }

  int p1() {
    result = count(Pos s1, Pos s2 | cheatSaving(s1, s2) >= 100)
  }

  int p2() {
    result = count(Pos s1, Pos s2 | cheatSavingP2(s1, s2) >= 100)
  }
}

select 1
