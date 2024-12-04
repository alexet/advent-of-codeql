signature string inputSig();

module Helpers<inputSig/0 input> {
  string line(int i) { result = input().splitAt("\n", i) }

  string part(int i, int j) { result = leftover(i, j).regexpCapture("(\\d+)(|\\s.*)", 1) }

  string leftover(int i, int j) {
    j = 1 and result = line(i)
    or
    j > 1 and result = leftover(i, j - 1).regexpCapture("(\\S+)\\s+(\\S+)", 2)
  }

  int grid(int i, int j) { result = line(i).splitAt(" ", j).toInt() }
}

newtype TDir8 =
  N() or
  S() or
  E() or
  W() or
  NE() or
  NW() or
  SE() or
  SW()

class Dir8 extends TDir8 {
  string toString() {
    this = N() and result = "N"
    or
    this = S() and result = "S"
    or
    this = E() and result = "E"
    or
    this = W() and result = "W"
    or
    this = NE() and result = "NE"
    or
    this = NW() and result = "NW"
    or
    this = SE() and result = "SE"
    or
    this = SW() and result = "Sw"
  }

  int dx() {
    this = [W().(Dir8), NW().(Dir8), SW().(Dir8)] and result = -1
    or
    this = [E().(Dir8), NE().(Dir8), SE().(Dir8)] and result = 1
    or
    this = [N().(Dir8), S().(Dir8)] and result = 0
  }

  int dy() {
    this = [N().(Dir8), NW().(Dir8), NE().(Dir8)] and result = -1
    or
    this = [S().(Dir8), SW().(Dir8), SE().(Dir8)] and result = 1
    or
    this = [E().(Dir8), W().(Dir8)] and result = 0
  }
}
