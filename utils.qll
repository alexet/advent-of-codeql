
signature predicate inputSig(string s);

module Helpers<inputSig/1 input> {
    string line(int i) { exists(string input | input(input) | result = input.splitAt("\n", i)) }

    

    string part(int i, int j) { result = leftover(i, j).regexpCapture("(\\d+)(|\\s.*)", 1) }

    string leftover(int i, int j) {
        j = 1 and result = line(i)
        or
        j > 1 and result = leftover(i, j - 1).regexpCapture("(\\S+)\\s+(\\S+)", 2)
    }

    int grid(int i, int j) { result = line(i).splitAt(" ", j).toInt() }

}