import input
import utils

string testData() { result = testData(2024, 6) }

string realData() { result = realData(2024, 6) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  int height() { result = count(int n | exists(line(n))) }

  int width() { result = line(0).length() }

  predicate hasObstacle(int x, int y) { charGrid(x, y) = "#" }

  predicate start(int x, int y) { charGrid(x, y) = "^" }

  newtype TPos = MkPos(int x, int y) { exists(charGrid(x, y)) }

  class Pos extends TPos {
    int x;
    int y;

    Pos() { this = MkPos(x, y) }

    int getX() { result = x }

    int getY() { result = y }

    predicate hasXY(int ax, int ay) { ax = x and ay = y }

    Pos moveInDir(Dir4 dir) { result = MkPos(x + dir.dx(), y + dir.dy()) }

    predicate hasObstacle() { hasObstacle(x, y) }

    pragma[noinline]
    predicate moveHasObstacle(Dir4 dir) { moveInDir(dir).hasObstacle() }

    pragma[noinline]
    Pos clearMoveInDir(Dir4 dir) { result = moveInDir(dir) and not moveHasObstacle(dir) }

    predicate isStart() { start(x, y) }

    string toString() { result = "Pos(" + x + ", " + y + ")" }
  }

  predicate reaches(Pos pos, Dir4 dir) {
    pos.isStart() and dir = N().(Dir4)
    or
    exists(Dir4 pDir |
      reaches(pos, pDir) and
      pos.moveHasObstacle(pDir) and
      dir = pDir.rotateRight90()
    )
    or
    exists(Pos pPos |
      reaches(pPos, dir) and
      pos = pPos.clearMoveInDir(dir)
    )
  }

  predicate coveredInPath(Pos p) { reaches(p, _) }

  int covered() { result = count(Pos p | coveredInPath(p)) }

  predicate reachesObst(Pos extraObst, Pos pos, Dir4 dir) {
    pos.isStart() and dir = N().(Dir4) and coveredInPath(extraObst)
    or
    exists(Dir4 pDir |
      reachesObst(extraObst, pos, pDir) and
      (pos.moveHasObstacle(pDir) or pos.moveInDir(dir) = extraObst) and
      dir = pDir.rotateRight90()
    )
    or
    exists(Pos pPos |
      reachesObst(extraObst, pPos, dir) and
      pos = pPos.clearMoveInDir(dir) and
      pos != extraObst
    )
  }

  predicate exits(Pos extraObst) {
    exists(Pos p, Dir4 dir |
      reachesObst(extraObst, p, dir) and
      not exists(p.moveInDir(dir))
    )
  }

  predicate hasLoop(Pos extraObst) {
    not exits(extraObst) and
    coveredInPath(extraObst)
  }

  int loopCount() { result = count(Pos p | hasLoop(p)) }
}

select 1
