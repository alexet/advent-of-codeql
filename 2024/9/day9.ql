import input
import utils

string testData() { result = testData(2024, 9) }

string realData() { result = realData(2024, 9) }

module TestImpl = Impl<testData/0>;

module RealImpl = Impl<realData/0>;

module Impl<inputSig/0 input> {
  import Helpers<input/0>

  int maxId() { result = (input().length() - 1) / 2 }

  newtype TBlockType =
    Empty() or
    File(int id) { id in [0 .. maxId()] }

  class BlockType extends TBlockType {
    string toString() {
      this = Empty() and result = "Empty"
      or
      exists(int id | this = File(id) and result = "File " + id)
    }

    string toShortId() {
      exists(int chars | chars = maxId().toString().length() |
        this = Empty() and result = "________".prefix(chars)
        or
        exists(int i |
          this = File(i) and
          result = "00000".prefix(chars - i.toString().length()) + i.toString()
        )
      )
    }
  }

  int sectionSize(int i) { result = input().charAt(i).toInt() }

  int sectionStart(int i) {
    i = 0 and result = 0
    or
    result = sectionStart(i - 1) + sectionSize(i - 1)
  }

  BlockType blockType(int i) {
    exists(int sectionId |
      i in [sectionStart(sectionId) .. sectionStart(sectionId + 1) - 1] and
      (
        sectionId % 2 = 0 and
        result = File(sectionId / 2)
        or
        sectionId % 2 = 1 and result = Empty()
      )
    )
  }

  int emptyLengths(int i) {
    i in [0 .. maxId()] and
    result = sectionSize(i * 2 + 1)
  }

  int fileLengths(int i) {
    i in [0 .. maxId()] and
    result = sectionSize(i * 2)
  }

  int reverseBlockIds(int i) {
    result =
      rank[i](int sectionId | blockType(sectionId) != Empty() | sectionId order by sectionId desc)
  }

  int emptyIdOff(int i) {
    result = rank[i](int sectionId | blockType(sectionId) = Empty() | sectionId)
  }

  int crossOver() {
    exists(int index |
      index = min(int i | reverseBlockIds(i) < emptyIdOff(i)) and
      result = reverseBlockIds(index)
    )
  }

  int fileAfterRearranging(int i) {
    i <= crossOver() and
    (
      File(result) = blockType(i)
      or
      exists(int index | i = emptyIdOff(index) and File(result) = blockType(reverseBlockIds(index)))
    )
  }

  QlBuiltins::BigInt checksum() {
    result = sum(int i | | i.toBigInt() * fileAfterRearranging(i).toBigInt())
  }

  language[monotonicAggregates]
  pragma[nomagic]
  int bestLoc(int i) {
    result =
      min(int j |
        j < i and fileLengths(i) <= emptyLengths(j)
      |
        j
        order by
          any(int res |
            bestLoc([i + 1 .. maxId()]) = j and res = 100000000
            or
            forall(int k | k in [i + 1 .. maxId()] | bestLoc(i) != j) and
            res = i
          |
            res
          )
      )
  }

  cached
  int fileIdForBlank(int blankId, int blankOrder) {
    adjPriority(blankId, blankOrder, result) != -1 and
    result = fileIdForBlankInner(blankId, blankOrder)
  }

  language[monotonicAggregates]
  pragma[nomagic]
  int fileIdForBlankInner(int blankId, int blankOrder) {
    iter(blankId, blankOrder) and
    result =
      max(int i | i in [blankId + 1 .. maxId()] | i order by adjPriority(blankId, blankOrder, i))
  }

  // newtype TIter =
  //   MkIter(int blankId, int blankOrder) {
  //     iter(blankId, blankOrder) and
  //     blankId < 10 and
  //     blankOrder < 10
  //   }
  // class Iter extends TIter {
  //   string toString() {
  //     exists(int blankId, int blankOrder | this = MkIter(blankId, blankOrder) |
  //       result = "Iter(" + blankId + ", " + blankOrder + ")"
  //     )
  //   }
  // }
  // predicate test = ComputeMaxOverRange<MaxCfg>::maxUpTo/2;
  // module MaxCfg implements IntMaxInput {
  //   class Key = Iter;
  //   predicate range(Key key, int start, int end) {
  //     exists(int blankId, int blankOrder | key = MkIter(blankId, blankOrder) |
  //       start = blankId + 1 and end = maxId()
  //     )
  //   }
  //   int getWeight(Key key, int i) {
  //     exists(int blankId, int blankOrder | key = MkIter(blankId, blankOrder) |
  //       result = adjPriority(blankId, blankOrder, i)
  //     )
  //   }
  // }
  pragma[inline]
  int emptyLengths(int blankId, int blankOrder) {
    blankOrder = 0 and result = emptyLengths(blankId)
    or
    result = emptyLengthsInner(blankId, blankOrder)
  }

  pragma[noinline]
  int emptyLengthsInner(int blankId, int blankOrder) {
    result =
      emptyLengths(blankId, blankOrder - 1) - fileLengths(fileIdForBlank(blankId, blankOrder - 1))
  }

  predicate blankDone(int blankId, int blankOrder) {
    iter(blankId, blankOrder) and
    adjPriority(blankId, blankOrder, fileIdForBlankInner(blankId, blankOrder)) = -1
  }

  pragma[noinline]
  predicate iter(int blankId, int blankOrder) { exists(priority(blankId, blankOrder, _)) }

  pragma[noinline]
  int adjPriority(int blankId, int blankOrder, int fileId) {
    emptyLengths(blankId, blankOrder) >= fileLengths(fileId) and
    result = priority(blankId, blankOrder, fileId)
    or
    emptyLengths(blankId, blankOrder) < fileLengths(fileId) and
    exists(priority(blankId, blankOrder, fileId)) and
    result = -1
  }

  predicate confused(int blankId, int blankOrder) {
    blankDone(blankId, blankOrder) and
    exists(fileIdForBlank(blankId, blankOrder))
  }

  predicate confused2(int blankId, int blankOrder) {
    iter(blankId, blankOrder) and
    not blankDone(blankId, blankOrder) and
    not exists(fileIdForBlank(blankId, blankOrder))
  }

  predicate confused3(int blankId, int blankOrder) {
    strictcount(fileIdForBlank(blankId, blankOrder)) >= 2
  }

  cached
  int priority(int blankId, int blankOrder, int fileId) {
    (
      blankId = 0 and blankOrder = 0 and result = fileId and exists(fileLengths(fileId))
      or
      exists(int prevBlankId, int prevBlankOrder |
        blankOrder = 0 and
        prevBlankId = blankId - 1 and
        blankDone(prevBlankId, prevBlankOrder) and
        result = priority(prevBlankId, prevBlankOrder, fileId)
        or
        prevBlankId = blankId and
        prevBlankOrder = blankOrder - 1 and
        (
          fileIdForBlank(prevBlankId, prevBlankOrder) = fileId and result = -1
          or
          fileIdForBlank(prevBlankId, prevBlankOrder) != fileId and
          result = priority(prevBlankId, prevBlankOrder, fileId)
        )
      )
    ) and
    blankId < 7000
  }

  predicate doublePriorityErr(int blankId, int blankOrder, int fileId) {
    strictcount(adjPriority(blankId, blankOrder, fileId)) > 1
  }

  int files(int i) {
    i in [0 .. input().length() - 1] and
    (
      i % 2 = 0 and not result = fileIdForBlank(_, _) and result = i / 2
      or
      i % 2 = 1 and result = fileIdForBlank(i / 2, _)
    )
  }

  int oFiles(int i, int j) { result = rank[j + 1](int k | files(i) = k | k order by k desc) }

  int sectionStart2(int i, int j) {
    j = 0 and result = sectionStart(i) and exists(oFiles(i, j))
    or
    result = sectionStart2(i, j - 1) + fileLengths(oFiles(i, j - 1)) and exists(oFiles(i, j))
  }

  int expandedFiles(int pos) {
    exists(int i, int j |
      pos in [sectionStart2(i, j) .. sectionStart2(i, j) + fileLengths(result) - 1] and
      result = oFiles(i, j)
    )
  }

  BlockType getExpandedFull(int pos) {
    result = File(expandedFiles(pos))
    or
    not exists(expandedFiles(pos)) and result = Empty() and exists(blockType(pos))
  }

  string inputAsString() { result = concat(int i | | blockType(i).toShortId(), "," order by i) }

  string resAsString() { result = concat(int i | | getExpandedFull(i).toShortId(), "," order by i) }

  QlBuiltins::BigInt checksum2() {
    result = sum(int i | | i.toBigInt() * expandedFiles(i).toBigInt())
  }
}

select RealImpl::checksum2().toString()
