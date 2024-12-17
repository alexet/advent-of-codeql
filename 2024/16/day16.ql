import input
import utils

string testData() { result = testData(2024, 16) }

string realData() { result = realData(2024, 16) }

module TestImpl = Impl<testData/0>;
module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  newtype TPos = MkPos(int x, int y) { exists(charGrid(x, y)) }

  class Pos extends TPos {
    int x;
    int y;

    Pos() { this = MkPos(x, y) }

    int getX() { result = x }

    int getY() { result = y }

    string getInitial() { result = charGrid(x, y) }

    Pos move(Dir4 dir) {
      result.getX() = x + dir.dx() and
      result.getY() = y + dir.dy()
    }

    string toString() { result = "Pos(" + x + ", " + y + ")" }
  }

  newtype TState = MkState(Pos pos, Dir4 dir)

  class State extends TState {
    Pos pos;
    Dir4 dir;

    State() { this = MkState(pos, dir) }

    Pos getPos() { result = pos }

    Dir4 getDir() { result = dir }

    string toString() { result = "State(" + pos + ", " + dir + ")" }
  }

  State initialState() { result.getPos().getInitial() = "S" and result.getDir() = E() }

  State finalState() { result.getPos().getInitial() = "E" }

  predicate quickStep(State s1, State s2) {
    exists(Dir4 dir |
      s1.getDir() = dir and
      s2.getDir() = dir
    |
      s2.getPos() = s1.getPos().move(dir) and
      s1.getPos().getInitial() != "#" and
      s2.getPos().getInitial() != "#"
    )
  }

  predicate quickSteps(State s1, State s2) {
    quickStep*(s1, s2) and s1.getPos().getInitial() != "#"
  }

  predicate bigStep(State s1, State s2) {
    s1.getPos() = s2.getPos() and
    (
      s1.getDir() = s2.getDir().rotateLeft90() or
      s1.getDir() = s2.getDir().rotateRight90()
    )
  }

  predicate stepRel(State s1, State s2) {
    exists(State mid | quickSteps(s1, mid) and bigStep(mid, s2))
  }

  predicate nearGoal(State s) { quickSteps(s, finalState()) }

  int numberBigSteps(State s) = shortestDistances(initialState/0, stepRel/2)(_, s, result)

  int bigStepsToGoal() { result = min(State nearEnd | nearGoal(nearEnd) | numberBigSteps(nearEnd)) }

  newtype TExState =
    BasicState(State state) or
    TurningState(State target, int left) { left in [1 .. 999] }

  class ExState extends TExState {
    cached
    string toString() {
      exists(State u1, int left |
        this = TurningState(u1, left) and
        result = "TurningState(" + u1 + ", " + left + ")"
      )
      or
      exists(State u1 |
        this = BasicState(u1) and
        result = "BasicState(" + u1 + ")"
      )
    }
  }

  ExState step(ExState state) {
    exists(State u1, State u2 |
      state = BasicState(u1) and
      result = BasicState(u2) and
      exists(Dir4 dir |
        u1.getDir() = dir and
        u2.getDir() = dir and
        u1.getPos().move(dir) = u2.getPos() and
        u2.getPos().getInitial() != "#" and
        u1.getPos().getInitial() != "#"
      )
    )
    or
    exists(State u1, int left |
      state = TurningState(u1, left) and
      result = TurningState(u1, left - 1)
    )
    or
    exists(State u1 |
      state = TurningState(u1, 1) and
      result = BasicState(u1)
    )
    or
    exists(State u1, State u2 |
      state = BasicState(u1) and
      u1.getPos() = u2.getPos() and
      (
        u1.getDir() = u2.getDir().rotateLeft90() or
        u1.getDir() = u2.getDir().rotateRight90()
      ) and
      result = TurningState(u2, 999)
    )
  }

  ExState initial() { result = BasicState(initialState()) }

  int distanceTo(ExState state) = shortestDistances(initial/0, step/1)(_, state, result)

  int minDist() { result = min(distanceTo(BasicState(finalState()))) }

  predicate onMinPath(ExState state) {
    state = BasicState(finalState()) and distanceTo(state) = minDist()
    or
    exists(ExState next |
      distanceTo(state) + 1 = distanceTo(next) and
      step(state) = next and
      onMinPath(next)
    )
  }

  predicate posOnMinPath(Pos p) {
    onMinPath(BasicState(MkState(p, _)))
  }

  int minPathCount() {
    result = count(int x, int y | posOnMinPath(MkPos(x, y)))
  }

  int wStep(State s1, State s2) {
    exists(Dir4 dir |
      dir = s1.getDir() and
      dir = s2.getDir() and
      s1.getPos().move(dir) = s2.getPos() and
      s1.getPos().getInitial() != "#" and
      s2.getPos().getInitial() != "#"
    ) and
    result = 1
    or
    s1.getPos() = s2.getPos() and
    (
      s1.getDir() = s2.getDir().rotateLeft90() or
      s1.getDir() = s2.getDir().rotateRight90()
    ) and
    result = 1000
  }

  string badPair(State s1, State s2) {
    exists(int d1, int d2, int w |
      d1 = distanceTo(BasicState(s1)) and
      d2 = distanceTo(BasicState(s2)) and
      w = wStep(s1, s2) and
      d2 > d1 + w and
      result = "Bad pair: " + s1 + " -> " + s2 + " (" + d1 + " -> " + d2 + ") " + w + " " + (d1 + w)
    )
  }

  string char(Pos p) {
    if onMinPath(BasicState(MkState(p, _))) then result = "X" else result = p.getInitial()
  }

  string display() {
    result =
      strictconcat(int y | | strictconcat(int x | | char(MkPos(x, y)) order by x), "\n" order by y)
  }
}

select 1
