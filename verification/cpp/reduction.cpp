// reduction.cpp -- Lemmas 2.1 and 2.2 by enumeration.
//
// Enumerates all w in {1,...,9}^5, checks that s(w) <= 8 forces every entry to be at most 7, counts the
// dihedral classes with s(w) <= 8 and n(w) = 16 or 17 (36 and 26), compares them with the files
// verification/data/wits16.txt and cands17.txt, and checks that every w with s(w) <= 8 lies above a
// 17-vertex class when n(w) >= 17 and below a 16-vertex class when n(w) <= 16. It also checks the
// edge counts quoted in the introduction (71 to 80 edges for the 17-vertex graphs, at most 6n - 12 = 90).
//
//   c++ -O2 -std=c++17 -o reduction reduction.cpp && ./reduction ../data
#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>

using W = std::array<int, 5>;

static std::vector<W> symmetries(const W& w) {
  std::vector<W> out;
  for (int r = 0; r < 5; r++) {
    W x, y;
    for (int i = 0; i < 5; i++) x[i] = w[(i + r) % 5];
    for (int i = 0; i < 5; i++) y[i] = x[4 - i];
    out.push_back(x);
    out.push_back(y);
  }
  return out;
}
static W canon(const W& w) { auto s = symmetries(w); return *std::min_element(s.begin(), s.end()); }
static int s_of(const W& w) { int m = 0; for (int i = 0; i < 5; i++) m = std::max(m, w[i] + w[(i + 1) % 5]); return m; }
static int n_of(const W& w) { int t = 0; for (int x : w) t += x; return t; }
static int edges(const W& w) { int e = 0; for (int i = 0; i < 5; i++) e += w[i] * (w[i] - 1) / 2 + w[i] * w[(i + 1) % 5]; return e; }
static bool le(const W& a, const W& b) { for (int i = 0; i < 5; i++) if (a[i] > b[i]) return false; return true; }

static std::vector<W> read(const std::string& path) {
  std::ifstream f(path);
  std::vector<W> out;
  std::string line;
  while (std::getline(f, line)) {
    if (line.empty() || line[0] == '#') continue;
    std::istringstream is(line);
    W w;
    for (int& x : w) is >> x;
    out.push_back(w);
  }
  return out;
}

int main(int argc, char** argv) {
  std::string dir = argc > 1 ? argv[1] : "../data";
  auto c17 = read(dir + "/cands17.txt"), c16 = read(dir + "/wits16.txt");
  bool ok = true;
  auto check = [&](bool c, const std::string& msg) { std::cout << (c ? "ok   " : "FAIL ") << msg << "\n"; ok = ok && c; };

  std::vector<W> all;
  bool bounded = true;
  for (int a = 1; a <= 9; a++) for (int b = 1; b <= 9; b++) for (int c = 1; c <= 9; c++)
    for (int d = 1; d <= 9; d++) for (int e = 1; e <= 9; e++) {
      W w{a, b, c, d, e};
      if (s_of(w) > 8) continue;
      if (*std::max_element(w.begin(), w.end()) > 7) bounded = false;
      all.push_back(w);
    }
  check(bounded, "s(w) <= 8 forces entries <= 7");

  std::set<W> k16, k17, f16, f17;
  for (auto& w : all) { if (n_of(w) == 16) k16.insert(canon(w)); if (n_of(w) == 17) k17.insert(canon(w)); }
  for (auto& w : c16) f16.insert(canon(w));
  for (auto& w : c17) f17.insert(canon(w));
  check(k16.size() == 36 && k16 == f16 && c16.size() == 36, "36 classes with n = 16 equal wits16.txt");
  check(k17.size() == 26 && k17 == f17 && c17.size() == 26, "26 classes with n = 17 equal cands17.txt");

  bool up = true, down = true;
  for (auto& w : all) {
    auto sy = symmetries(w);
    if (n_of(w) >= 17) {
      bool f = false;
      for (auto& c : c17) for (auto& g : sy) f = f || le(c, g);
      up = up && f;
    } else {
      bool f = false;
      for (auto& c : c16) for (auto& g : sy) f = f || le(g, c);
      down = down && f;
    }
  }
  check(up, "n(w) >= 17: w lies above a 17-vertex class");
  check(down, "n(w) <= 16: w lies below a 16-vertex class");

  int emin = 1000, emax = 0;
  for (auto& w : c17) { emin = std::min(emin, edges(w)); emax = std::max(emax, edges(w)); }
  check(emin == 71 && emax == 80 && emax <= 6 * 17 - 12, "the 17-vertex graphs have 71 to 80 edges, below 6n - 12 = 90");

  std::cout << (ok ? "ALL CHECKS PASSED" : "SOME CHECKS FAILED") << "\n";
  return ok ? 0 : 1;
}
