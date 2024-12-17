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
  string charGrid(int x, int y) { result = line(y).charAt(x) }
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

  Dir8 rotateLeft90() {
    this = N() and result = W()
    or
    this = W() and result = S()
    or
    this = S() and result = E()
    or
    this = E() and result = N()
    or
    this = NE() and result = NW()
    or
    this = NW() and result = SW()
    or
    this = SW() and result = SE()
    or
    this = SE() and result = NE()
  }

  Dir8 rotateRight90() {
    result.rotateLeft90() = this
  }
}

class Dir4 extends Dir8 {
  Dir4() {
    this = N()
    or
    this = S()
    or
    this = E()
    or
    this = W()
  }

  override Dir4 rotateLeft90() {
    result = super.rotateLeft90()
  }

  override Dir4 rotateRight90() {
    result.rotateLeft90() = this
  }

  Dir4 opposite() {
    this = N() and result = S()
    or
    this = S() and result = N()
    or
    this = E() and result = W()
    or
    this = W() and result = E()
  }
}

signature module IntMaxInput {
  class Key;
  predicate range(Key key, int start, int end);
  int getWeight(Key key, int i);
}

module ComputeMaxOverRange<IntMaxInput Input> {
  class Key = Input::Key;
  private predicate nonEmptyRange(Key key, int start, int end) {
    start < end and
    Input::range(key, start, end)
  }

  int maxUpTo(Key key, int i) {
    exists(int start, int end | nonEmptyRange(key, start, end) |
      i = start and result = i
      or
      i <= end and
      exists (int prevMax |
        maxUpTo(key, i-1) = prevMax |
        Input::getWeight(key, i) > Input::getWeight(key, prevMax) and
        result = i
        or
        Input::getWeight(key, i) <= Input::getWeight(key, prevMax) and
        result = prevMax
      )
    )
  }

  int getMax(Key key) {
    exists(int end | nonEmptyRange(key, _, end) | result = maxUpTo(key, end))
  }
}