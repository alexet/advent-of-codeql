private extensible predicate test_everybody_codes(string year, string day, string data);

private extensible predicate real_everybody_codes(string year, string day, string data);

string testData(int year, int day) {
  test_everybody_codes(any(string s | s.toInt() = year), any(string s | s.toInt() = day), result)
}

string realData(int year, int day) {
  real_everybody_codes(any(string s | s.toInt() = year), any(string s | s.toInt() = day), result)
}
