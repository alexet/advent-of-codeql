import input
import utils

string testData() { result = testData(2024, 25) }

string realData() { result = realData(2024, 25) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  string lockOrKey(int n) { result = input().splitAt("\n\n", n) }

  string grid(int n, int x, int y) { result = lockOrKey(n).splitAt("\n", y).splitAt("", x) }

  predicate isLock(int n) { forex(int x | x in [0 .. 4] | grid(n, x, 0) = "#") }

  predicate isKey(int n) { exists(lockOrKey(n)) and not isLock(n) }

  int lockHeight(int n, int x) {
    isLock(n) and
    result = max(int y | grid(n, x, y) = "#")
  }

  int keyHeight(int n, int x) {
    isKey(n) and
    result = 5 - max(int y | grid(n, x, y) != "#")
  }

  predicate keyOverlap(int lock, int key) {
    isLock(lock) and
    isKey(key) and
    exists(int x | keyHeight(key, x) + lockHeight(lock, x) > 5)
  }

  predicate lockWorks(int lock, int key) {
    isLock(lock) and
    isKey(key) and
    not keyOverlap(lock, key)
  }

  int p1() { result = count(int lock, int key | lockWorks(lock, key)) }
}

select 1
