import input
import utils

string testData() { result = testData(2024, 15) }

string realData() { result = realData(2024, 15) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  string grid() { result = input().splitAt("\n\n", 0) }

  string instructions() { result = input().splitAt("\n\n", 1).regexpReplaceAll("\\s", "") }

  string instruction(int i) { result = instructions().charAt(i) }

  Dir4 instructionDir(int i) {
    exists(string instr | instr = instruction(i) |
      instr = "<" and result = W()
      or
      instr = ">" and result = E()
      or
      instr = "^" and result = N()
      or
      instr = "v" and result = S()
    )
  }

  module Part1 {
    string gridChar(int x, int y) { result = grid().splitAt("\n", y).charAt(x) }

    newtype TPos = MkPos(int x, int y) { exists(gridChar(x, y)) }

    class Pos extends TPos {
      int x;
      int y;

      Pos() { this = MkPos(x, y) }

      int getX() { result = x }

      int getY() { result = y }

      string toString() { result = "Pos(" + x + ", " + y + ")" }

      Pos move(Dir4 dir) {
        result.getY() = y + dir.dy() and
        result.getX() = x + dir.dx()
      }

      string getInitial() { result = gridChar(x, y) }

      int gps() { result = 100 * y + x }
    }

    Pos startPos() { result.getInitial() = "@" }

    boolean pushedInto(int iter, Pos p) {
      exists(Dir4 dir | dir = instructionDir(iter - 1) |
        not exists(p.move(dir.opposite())) and result = false
        or
        exists(Pos neighbor, string neighborState |
          dir = instructionDir(iter - 1) and
          neighbor = p.move(dir.opposite()) and
          neighborState = stateAt(iter - 1, neighbor)
        |
          neighborState = "O" and result = pushedInto(iter, neighbor)
          or
          neighborState = "@" and result = true
          or
          neighborState = "#" and result = false
          or
          neighborState = "." and result = false
        )
      )
    }

    boolean canMoveInto(int iter, Pos p) {
      exists(Dir4 dir, string state |
        dir = instructionDir(iter - 1) and
        state = stateAt(iter - 1, p)
      |
        not exists(p.move(dir)) and result = false
        or
        state = "#" and result = false
        or
        state = "O" and result = canMoveInto(iter, p.move(dir))
        or
        state = "@" and result = false
        or
        state = "." and result = true
      )
    }

    Pos getPos(int x, int y) { result = MkPos(x, y) }

    pragma[nomagic]
    string stateAt(int iter, Pos pos) {
      iter = 0 and result = pos.getInitial()
      or
      exists(string prevState, Dir4 dir |
        (
          dir = instructionDir(iter - 1) and
          prevState = stateAt(iter - 1, pos) and
          prevState = "@" and
          canMoveInto(iter, pos.move(dir)) = true and
          result = "."
          or
          dir = instructionDir(iter - 1) and
          prevState = stateAt(iter - 1, pos) and
          prevState = "@" and
          canMoveInto(iter, pos.move(dir)) = false and
          result = "@"
          or
          dir = instructionDir(iter - 1) and
          prevState = stateAt(iter - 1, pos) and
          prevState != "@" and
          pushedInto(iter, pos) = true and
          canMoveInto(iter, pos) = true and
          result = stateAt(iter - 1, pos.move(dir.opposite()))
          or
          dir = instructionDir(iter - 1) and
          prevState = stateAt(iter - 1, pos) and
          prevState != "@" and
          (
            pushedInto(iter, pos) = false
            or
            canMoveInto(iter, pos) = false
          ) and
          result = prevState
        )
      )
    }

    string iterString(int iter) {
      result =
        instruction(iter - 1) + "\n" +
          strictconcat(int y |
            |
            strictconcat(int x | | stateAt(iter, getPos(x, y)) order by x), "\n" order by y
          )
    }

    int maxIter() { result = instructions().length() }

    string finalState(Pos p) { result = stateAt(maxIter(), p) }

    int gpsScore() { result = sum(Pos p | finalState(p) = "O" | p.gps()) }
  }

  module Part2 {
    string gridChar(int x, int y) {
      exists(int prevX, string prevState, string expanded |
        prevState = Part1::gridChar(prevX, y) and
        (
          prevState = "#" and expanded = "##"
          or
          prevState = "O" and expanded = "[]"
          or
          prevState = "@" and expanded = "@."
          or
          prevState = "." and expanded = ".."
        ) and
        (
          x = prevX * 2 and result = expanded.charAt(0)
          or
          x = prevX * 2 + 1 and result = expanded.charAt(1)
        )
      )
    }

    newtype TPos = MkPos(int x, int y) { exists(gridChar(x, y)) }

    class Pos extends TPos {
      int x;
      int y;

      Pos() { this = MkPos(x, y) }

      int getX() { result = x }

      int getY() { result = y }

      string toString() { result = "Pos2(" + x + ", " + y + ")" }

      Pos move(Dir4 dir) {
        result.getY() = y + dir.dy() and
        result.getX() = x + dir.dx()
      }

      string getInitial() { result = gridChar(x, y) }

      int gps() { result = 100 * y + x }
    }

    Pos getPos(int x, int y) { result = MkPos(x, y) }

    boolean directPushedInto(int iter, Pos p) {
      exists(Dir4 dir | dir = instructionDir(iter - 1) |
        not exists(p.move(dir.opposite())) and result = false
        or
        exists(Pos neighbor, string neighborState |
          dir = instructionDir(iter - 1) and
          neighbor = p.move(dir.opposite()) and
          neighborState = stateAt(iter - 1, neighbor)
        |
          neighborState in ["[", "]"] and result = pushed(iter, neighbor)
        )
        or
        exists(Pos neighbor, string neighborState |
          dir = instructionDir(iter - 1) and
          neighbor = p.move(dir.opposite()) and
          neighborState = stateAt(iter - 1, neighbor)
        |
          neighborState = "@" and result = true
          or
          neighborState = "#" and result = false
          or
          neighborState = "." and result = false
        )
      )
    }

    boolean pushed(int iter, Pos p) {
      exists(Dir4 dir | dir = instructionDir(iter - 1) |
        (dir = E() or dir = W()) and
        result = directPushedInto(iter, p)
        or
        (dir = N() or dir = S()) and
        exists(string state |
          state = stateAt(iter - 1, p) and
          state in ["#", ".", "@"] and
          result = directPushedInto(iter, p)
          or
          state = "[" and
          state = stateAt(iter - 1, p) and
          result = directPushedInto(iter, p.move(E())).booleanOr(directPushedInto(iter, p))
          or
          state = stateAt(iter - 1, p) and
          state = "]" and
          result = directPushedInto(iter, p.move(W())).booleanOr(directPushedInto(iter, p))
        )
      )
    }

    boolean canMoveInto(int iter, Pos p) {
      exists(Dir4 dir, string state |
        dir = instructionDir(iter - 1) and
        state = stateAt(iter - 1, p) and
        (dir = E() or dir = W())
      |
        not exists(p.move(dir)) and result = false
        or
        state = "#" and result = false
        or
        state = "@" and result = false
        or
        state = "." and result = true
      )
      or
      exists(Dir4 dir, string state |
        dir = instructionDir(iter - 1) and
        state = stateAt(iter - 1, p) and
        (dir = E() or dir = W())
      |
        state in ["[", "]"] and result = canMoveInto(iter, p.move(dir))
      )
      or
      exists(Dir4 dir, string state |
        dir = instructionDir(iter - 1) and
        state = stateAt(iter - 1, p) and
        (dir = N() or dir = S())
      |
        not exists(p.move(dir)) and result = false
        or
        state = "#" and result = false
        or
        state = "@" and result = false
        or
        state = "." and result = true
      )
      or
      exists(Dir4 dir, string state |
        dir = instructionDir(iter - 1) and
        state = stateAt(iter - 1, p) and
        (dir = N() or dir = S())
      |
        state = "[" and
        result = canMoveInto(iter, p.move(dir)).booleanAnd(canMoveInto(iter, p.move(E()).move(dir)))
      )
      or
      exists(Dir4 dir, string state |
        dir = instructionDir(iter - 1) and
        state = stateAt(iter - 1, p) and
        (dir = N() or dir = S())
      |
        state = "]" and
        result = canMoveInto(iter, p.move(dir)).booleanAnd(canMoveInto(iter, p.move(W()).move(dir)))
      )
    }

    boolean moveAt(int iter) {
      exists(Pos rootPos, Dir4 instr |
        stateAt(iter - 1, rootPos) = "@" and
        instr = instructionDir(iter - 1) and
        result = canMoveInto(iter, rootPos.move(instr))
      )
    }

    pragma[nomagic]
    cached
    string stateAt(int iter, Pos pos) {
      iter = 0 and result = pos.getInitial()
      or
      exists(string prevState, Dir4 dir |
        dir = instructionDir(iter - 1) and
        prevState = stateAt(iter - 1, pos) and
        moveAt(iter) = true and
        prevState = "@" and
        result = "."
        or
        dir = instructionDir(iter - 1) and
        prevState = stateAt(iter - 1, pos) and
        moveAt(iter) = true and
        pushed(iter, pos) = true and
        directPushedInto(iter, pos) = true and
        result = stateAt(iter - 1, pos.move(dir.opposite()))
        or
        dir = instructionDir(iter - 1) and
        prevState = stateAt(iter - 1, pos) and
        moveAt(iter) = true and
        pushed(iter, pos) = true and
        directPushedInto(iter, pos) = false and
        result = "."
        or
        dir = instructionDir(iter - 1) and
        prevState = stateAt(iter - 1, pos) and
        moveAt(iter) = true and
        prevState != "@" and
        pushed(iter, pos) = false and
        result = prevState
        or
        dir = instructionDir(iter - 1) and
        prevState = stateAt(iter - 1, pos) and
        moveAt(iter) = true and
        not exists(pos.move(dir.opposite())) and
        result = prevState
        or
        dir = instructionDir(iter - 1) and
        prevState = stateAt(iter - 1, pos) and
        moveAt(iter) = false and
        result = prevState
      )
    }

    string iterString(int iter) {
      result =
        any(string s |
            s = instruction(iter - 1) + ", moved:" + moveAt(iter)
            or
            iter = 0 and s = "init"
          ) + "\n" +
          strictconcat(int y |
            |
            strictconcat(int x | | stateAt(iter, getPos(x, y)) order by x), "\n" order by y
          )
    }

    string pushState(int iter, Pos p) {
      exists(boolean canMoveInto, boolean directPush, boolean indirectPush |
        canMoveInto = canMoveInto(iter, p) and
        directPush = directPushedInto(iter, p) and
        indirectPush = pushed(iter, p)
      |
        canMoveInto = true and
        directPush = true and
        indirectPush = true and
        result = "p"
        or
        canMoveInto = true and
        directPush = true and
        indirectPush = false and
        result = "?"
        or
        canMoveInto = true and
        directPush = false and
        indirectPush = true and
        result = "P"
        or
        canMoveInto = true and
        directPush = false and
        indirectPush = false and
        result = "."
        or
        canMoveInto = false and
        result = "#"
      )
    }

    string pushString(int iter) {
      result =
        any(string s |
            s = instruction(iter - 1)
            or
            iter = 0 and s = "init"
          ) + "\n" +
          strictconcat(int y |
            |
            strictconcat(int x | | pushState(iter, getPos(x, y)) order by x), "\n" order by y
          )
    }

    int maxIter() { result = instructions().length() }

    string finalState(Pos p) { result = stateAt(maxIter(), p) }

    int gpsScore() { result = sum(Pos p | finalState(p) = "[" | p.gps()) }
  }
}

select 1
