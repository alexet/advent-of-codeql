import inputEC
import utils

string testData() { result = testData(2025, 1) }

string realData() { result = realData(2025, 1) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  string name(int i) { result = line(0).splitAt(",", i) }

  string instruction(int i) { result = line(2).splitAt(",", i) }

  string dir(int i) { result = instruction(i).charAt(0) }

  int steps(int i) { result = instruction(i).suffix(1).toInt() }

  int totalNames() { result = count(int i | exists(name(i))) }

  int maxNameIndex() { result = totalNames() - 1 }

  int signedStep(int i) {
    dir(i) = "L" and result = -steps(i)
    or
    dir(i) = "R" and result = steps(i)
  }

  int resolvedPosP3(int i) {
    dir(i) = "L" and result = ((-steps(i) % totalNames()) + totalNames()) % totalNames()
    or
    dir(i) = "R" and result = steps(i) % totalNames()
  }

  int posAt(int i) {
    i = 0 and result = 0
    or
    i > 0 and result = (posAt(i - 1) + signedStep(i - 1)).minimum(maxNameIndex()).maximum(0)
  }

  int posAtP2(int i) {
    i = 0 and result = 0
    or
    i > 0 and
    result = (posAtP2(i - 1) + signedStep(i - 1) + totalNames()) % totalNames()
  }

  string nameAt(int step, int pos) {
    step = 0 and result = name(pos)
    or
    step > 0 and pos != 0 and pos != resolvedPosP3(step - 1) and result = nameAt(step - 1, pos)
    or
    step > 0 and pos = resolvedPosP3(step - 1) and result = nameAt(step - 1, 0)
    or
    step > 0 and pos = 0 and result = nameAt(step - 1, resolvedPosP3(step - 1))
  }



  string names(int i) { result = name(posAtP2(i)) }

  int finalPosition() { result = posAt(count(int i | exists(instruction(i)))) }

  int finalPositionP2() { result = posAtP2(count(int i | exists(instruction(i)))) }

  string finalName() { result = name(finalPosition()) }

  string finalNameP2() { result = name(finalPositionP2()) }


  string finalNameP3() { result = nameAt(count(int i | exists(instruction(i))), 0) }
}

select RealImpl::finalName(), RealImpl::finalNameP2()
