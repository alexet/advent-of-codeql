import input
import utils

string testData() { result = testData(2024, 22) }

string realData() { result = realData(2024, 22) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

bindingset[input, secret]
int mix(int input, int secret) { result = input.bitXor(secret) }

bindingset[secret]
int prune(int secret) { result = secret.bitAnd(16777216 - 1) }

bindingset[secret]
int nextSecret(int secret) {
  exists(int s1, int s2 |
    s1 = prune(mix(secret * 64, secret)) and
    s2 = prune(mix(s1 / 32, s1)) and
    result = prune(mix(s2 * 2048, s2))
  )
}

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  int initialSecret(int i) { result = line(i).toInt() }

  int secretAt(int iter, int n) {
    iter = 0 and result = initialSecret(n)
    or
    iter <= 2000 and result = nextSecret(secretAt(iter - 1, n))
  }

  int secret2000(int n) { result = secretAt(2000, n) }

  int onesAt(int iter, int n) { result = secretAt(iter, n) % 10 }

  int diffAt(int iter, int n) { result = onesAt(iter, n) - onesAt(iter - 1, n) }

  predicate viableSeq4(int iter, int n, int a, int b, int c, int d) {
    a = diffAt(iter, n) and
    b = diffAt(iter + 1, n) and
    c = diffAt(iter + 2, n) and
    d = diffAt(iter + 3, n)
  }

  newtype TSeq4 = MkSeq4(int a, int b, int c, int d) { viableSeq4(_, _, a, b, c, d) }

  class Seq4 extends TSeq4 {
    int a;
    int b;
    int c;
    int d;

    Seq4() { this = MkSeq4(a, b, c, d) }

    int getA() { result = a }

    int getB() { result = b }

    int getC() { result = c }

    int getD() { result = d }

    predicate foundAt(int n, int iter) { viableSeq4(iter, n, a, b, c, d) }

    int firstFoundAt(int n) { result = min(int i2 | foundAt(n, i2)) }

    int valueFor(int n) { result = onesAt(firstFoundAt(n) + 3, n) }

    int totalValue() { result = sum(int i | | valueFor(i)) }

    string toString() {
      result = a.toString() + ", " + b.toString() + ", " + c.toString() + ", " + d.toString()
    }
  }

  QlBuiltins::BigInt p1() { result = sum(int i | | secret2000(i).toBigInt()) }

  int p2() { result = max(any(Seq4 a).totalValue()) }
}

select 1
