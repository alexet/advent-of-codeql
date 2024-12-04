private extensible predicate test(string year, string day, string data);

private extensible predicate real(string year, string day, string data);

string testData(int year, int day) {
  test(any(string s | s.toInt() = year), any(string s | s.toInt() = day), result)
}

string realData(int year, int day) {
  real(any(string s | s.toInt() = year), any(string s | s.toInt() = day), result)
}
