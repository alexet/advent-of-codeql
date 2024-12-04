
import input
import utils

string testData() {
    result = testData(2020,1)
}

string realData() {
    result = realData(2020,1)
}


module Impl<inputSig/0 input> {
    import Helpers<input/0>

    int number(int i) {
        result = line(i).toInt()
    }

    predicate sumsTo2020(int x, int y) {
        number(x) + number(y) = 2020
    }

    int product() {
        exists(int x, int y | sumsTo2020(x, y)  | result = number(x) * number(y))
    }

    predicate sumsTo2020(int x, int y, int z) {
        number(x) + number(y) + number(z) = 2020
    }

    int product2() {
        exists(int x, int y, int z | sumsTo2020(x, y, z)  | result = number(x) * number(y) * number(z))
    }



}


module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

select 1