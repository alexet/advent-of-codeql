import input
import utils

string testData() { result = testData(2024, 17) }

string realData() { result = realData(2024, 17) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  int aStart() { result = line(0).splitAt(" ", 2).toInt() }

  int bStart() { result = line(1).splitAt(" ", 2).toInt() }

  int cStart() { result = line(2).splitAt(" ", 2).toInt() }

  int opcode(int n) { result = line(4).splitAt(" ", 1).splitAt(",", n).toInt() }

  bindingset[comboType, aPrev, bPrev, cPrev]
  int operand(int comboType, int aPrev, int bPrev, int cPrev) {
    comboType in [0 .. 3] and result = comboType
    or
    comboType = 4 and result = aPrev
    or
    comboType = 5 and result = bPrev
    or
    comboType = 6 and result = cPrev
  }

  string decode(int opcode) {
    opcode = 0 and result = "adv"
    or
    opcode = 1 and result = "bxl"
    or
    opcode = 2 and result = "bst"
    or
    opcode = 3 and result = "jnz"
    or
    opcode = 4 and result = "bxc"
    or
    opcode = 5 and result = "out"
    or
    opcode = 6 and result = "bdv"
    or
    opcode = 7 and result = "cdv"
  }

  string decodeOperand(int operand) {
    operand in [0 .. 3] and result = operand.toString()
    or
    operand = 4 and result = "a"
    or
    operand = 5 and result = "b"
    or
    operand = 6 and result = "c"
    or
    operand = 7 and result = "E"
  }

  /**
   * b = a % 8
   * b = b ^ 2
   * c = a / 2^b
   * b = b^3
   * b = b^c
   * out b
   * a = a/8
   * if a != 0 goto start
   */
  string printCode() {
    result =
      concat(int i |
        |
        any(string s |
            exists(int opCode | opCode = opcode(i) and i % 2 = 0 |
              opCode = [1, 3] and s = decode(opCode) + " " + opcode(i + 1).toString()
              or
              opCode = [0, 2, 5, 6, 7] and s = decode(opCode) + " " + decodeOperand(opcode(i + 1))
              or
              opCode = 4 and s = decode(opCode)
            )
          ), ", "
        order by
          i
      )
  }

  predicate stateAt(int iter, int a, int b, int c, int ip) {
    iter = 0 and a = aStart() and b = bStart() and c = cStart() and ip = 0
    or
    exists(
      int op, int literalOperand, int comboOperand, int aPrev, int bPrev, int cPrev, int prevIP
    |
      stateAt(iter - 1, aPrev, bPrev, cPrev, prevIP) and
      op = opcode(prevIP) and
      literalOperand = opcode(prevIP + 1) and
      comboOperand = operand(literalOperand, aPrev, bPrev, cPrev)
    |
      op = 0 and
      a = aPrev.bitShiftRight(comboOperand) and
      b = bPrev and
      c = cPrev and
      ip = prevIP + 2
      or
      op = 1 and
      a = aPrev and
      b = bPrev.bitXor(literalOperand) and
      c = cPrev and
      ip = prevIP + 2
      or
      op = 2 and
      a = aPrev and
      b = bPrev % 8 and
      c = cPrev and
      ip = prevIP + 2
      or
      op = 3 and
      aPrev = 0 and
      a = aPrev and
      b = bPrev and
      c = cPrev and
      ip = prevIP + 2
      or
      op = 3 and
      aPrev != 0 and
      a = aPrev and
      b = bPrev and
      c = cPrev and
      ip = literalOperand
      or
      op = 4 and
      a = aPrev and
      b = bPrev.bitXor(cPrev) and
      c = cPrev and
      ip = prevIP + 2
      or
      op = 5 and
      a = aPrev and
      b = bPrev and
      c = cPrev and
      ip = prevIP + 2
      or
      op = 6 and
      a = aPrev and
      b = aPrev.bitShiftRight(comboOperand) and
      c = cPrev and
      ip = prevIP + 2
      or
      op = 7 and
      a = aPrev and
      b = bPrev and
      c = aPrev.bitShiftRight(comboOperand) and
      ip = prevIP + 2
    )
  }

  int outputAt(int iter) {
    exists(int op, int comboType, int operand, int aPrev, int bPrev, int cPrev, int prevIP |
      stateAt(iter - 1, aPrev, bPrev, cPrev, prevIP) and
      op = opcode(prevIP) and
      comboType = opcode(prevIP + 1) and
      operand = operand(comboType, aPrev, bPrev, cPrev) and
      op = 5 and
      result = operand % 8
    )
  }

  int rawOutputAt(int iter) {
    exists(int op, int comboType, int operand, int aPrev, int bPrev, int cPrev, int prevIP |
      stateAt(iter - 1, aPrev, bPrev, cPrev, prevIP) and
      op = opcode(prevIP) and
      comboType = opcode(prevIP + 1) and
      operand = operand(comboType, aPrev, bPrev, cPrev) and
      op = 5 and
      result = operand
    )
  }

  string outString() { result = concat(int iter | | outputAt(iter).toString(), "," order by iter) }

  string rawOutString() {
    result = concat(int iter | | rawOutputAt(iter).toString(), "," order by iter)
  }
}

select 1
