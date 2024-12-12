import input
import utils

string testData() { result = testData(2024, 12) }

string realData() { result = realData(2024, 12) }

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

    string plant() { result = charGrid(x, y) }

    int edgeCount() {
      result = 4 - count(Pos p | p = this.getANeighbour() and p.plant() = this.plant())
    }

    predicate hasEdge(Dir4 dir) {
      not exists(Pos p | p = this.getNeighbour(dir) and p.plant() = this.plant())
    }

    predicate isRootEdge(Dir4 dir) {
      hasEdge(dir)  
      and
      not exists(Pos p2 | 
        p2 = this.getNeighbour(dir.rotateLeft90()) and
        p2.plant() = this.plant() and
        p2.hasEdge(dir)        
      )
    }

    int rootSides() {
      result = count(Dir4 dir | isRootEdge(dir))
    }

    Pos getANeighbour() {
      result = MkPos(x + 1, y) or
      result = MkPos(x - 1, y) or
      result = MkPos(x, y + 1) or
      result = MkPos(x, y - 1)
    }

    Pos getNeighbour(Dir4 dir) {
      result = MkPos(x + dir.dx(), y + dir.dy())
    }

    string toString() { result = "(" + x.toString() + ", " + y.toString() + ")" }
  }

  predicate neighbourOfSameKind(Pos p1, Pos p2) {
    p1 = p2.getANeighbour() and
    p1.plant() = p2.plant()
    or
    p1 = p2
  }

  module Eq = QlBuiltins::EquivalenceRelation<Pos, neighbourOfSameKind/2>;

  class Region extends Eq::EquivalenceClass {
    Pos getAPos() { this = Eq::getEquivalenceClass(result) }

    string plant() { result = getAPos().plant() }

    int perimeter() {
      result = sum(Pos p | p = getAPos() | p.edgeCount())
    }

    int sides() {
      result = sum(Pos p | p = getAPos() | p.rootSides())
    }
    int area() {
      result = count(Pos p | p = getAPos())
    }

    int price() { result = area() * perimeter() }

    int price2() { result = area() * sides() }

    string toString() {
      result = "{" + concat(Pos p | | p.toString(), "," order by p.getX(), p.getY()) + "}"
    }
  }

  int totalPrice() {
    result = sum(Region r | | r.price())
    
  }

  int totalPrice2() {
    result = sum(Region r | | r.price2())
  }
}


select 1
