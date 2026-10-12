/* drawings.c -- check the 36 biplanar witnesses of Proposition 2.3 with exact integer arithmetic.
 *
 * Reads verification/data/witnesses16.txt. For each weight vector w it checks that the two edge lists
 * are exactly the edges of C5[w], that each list has a plane straight-line drawing at the given lattice
 * points (distinct points, no vertex inside a segment, no two disjoint segments meeting), and that the
 * colouring is a proper colouring with colours 0..7.
 *
 *   cc -O2 -o drawings drawings.c && ./drawings ../data/witnesses16.txt
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 16
#define MAXE 120

typedef struct { long x, y; } pt;

static long orient(pt a, pt b, pt c) { return (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x); }
static long lmin(long a, long b) { return a < b ? a : b; }
static long lmax(long a, long b) { return a > b ? a : b; }
static int on_seg(pt a, pt b, pt p) {
  return orient(a, b, p) == 0 && lmin(a.x, b.x) <= p.x && p.x <= lmax(a.x, b.x) &&
         lmin(a.y, b.y) <= p.y && p.y <= lmax(a.y, b.y);
}
static int sgn(long v) { return (v > 0) - (v < 0); }
static int meet(pt a, pt b, pt c, pt d) {
  int d1 = sgn(orient(c, d, a)), d2 = sgn(orient(c, d, b)), d3 = sgn(orient(a, b, c)), d4 = sgn(orient(a, b, d));
  if (d1 * d2 < 0 && d3 * d4 < 0) return 1;
  return on_seg(c, d, a) || on_seg(c, d, b) || on_seg(a, b, c) || on_seg(a, b, d);
}

static int plane(int n, int m, int E[][2], pt *P) {
  for (int u = 0; u < n; u++)
    for (int v = u + 1; v < n; v++)
      if (P[u].x == P[v].x && P[u].y == P[v].y) return 0;
  for (int e = 0; e < m; e++)
    for (int x = 0; x < n; x++)
      if (x != E[e][0] && x != E[e][1] && on_seg(P[E[e][0]], P[E[e][1]], P[x])) return 0;
  for (int e = 0; e < m; e++)
    for (int f = e + 1; f < m; f++) {
      int a = E[e][0], b = E[e][1], c = E[f][0], d = E[f][1];
      if (a == c || a == d || b == c || b == d) continue;
      if (meet(P[a], P[b], P[c], P[d])) return 0;
    }
  return 1;
}

static void expect(FILE *f, const char *word) {
  char buf[64];
  if (fscanf(f, "%63s", buf) != 1 || strcmp(buf, word) != 0) {
    fprintf(stderr, "parse error: expected %s\n", word);
    exit(2);
  }
}

int main(int argc, char **argv) {
  FILE *f = fopen(argc > 1 ? argv[1] : "../data/witnesses16.txt", "r");
  if (!f) { perror("witnesses16.txt"); return 2; }
  char line[512];
  while (fgets(line, sizeof line, f) && line[0] == '#') ;
  int count = atoi(line), bad = 0;
  for (int k = 0; k < count; k++) {
    int w[5], n = 0, bag[MAXN], adj[MAXN][MAXN] = {{0}}, cov[MAXN][MAXN] = {{0}};
    expect(f, "w");
    for (int i = 0; i < 5; i++) { if (fscanf(f, "%d", &w[i]) != 1) return 2; for (int j = 0; j < w[i]; j++) bag[n++] = i; }
    for (int u = 0; u < n; u++)
      for (int v = 0; v < n; v++) {
        int d = ((bag[u] - bag[v]) % 5 + 5) % 5;
        adj[u][v] = u != v && (d == 0 || d == 1 || d == 4);
      }
    int ok = 1;
    for (int j = 1; j <= 2; j++) {
      int jj, m, np, E[MAXE][2];
      pt P[MAXN];
      expect(f, "layer");
      if (fscanf(f, "%d %d", &jj, &m) != 2 || m > MAXE) return 2;
      for (int e = 0; e < m; e++) {
        if (fscanf(f, "%d %d", &E[e][0], &E[e][1]) != 2) return 2;
        if (!adj[E[e][0]][E[e][1]]) ok = 0;
        cov[E[e][0]][E[e][1]] = cov[E[e][1]][E[e][0]] = 1;
      }
      expect(f, "pos");
      if (fscanf(f, "%d %d", &jj, &np) != 2 || np != n) return 2;
      for (int v = 0; v < n; v++) if (fscanf(f, "%ld %ld", &P[v].x, &P[v].y) != 2) return 2;
      if (!plane(n, m, E, P)) ok = 0;
    }
    for (int u = 0; u < n; u++)
      for (int v = 0; v < n; v++)
        if (adj[u][v] && !cov[u][v]) ok = 0;
    int col[MAXN];
    expect(f, "colouring");
    for (int v = 0; v < n; v++) { if (fscanf(f, "%d", &col[v]) != 1) return 2; if (col[v] < 0 || col[v] > 7) ok = 0; }
    for (int u = 0; u < n; u++)
      for (int v = 0; v < n; v++)
        if (adj[u][v] && col[u] == col[v]) ok = 0;
    printf("%s w = %d,%d,%d,%d,%d\n", ok ? "ok  " : "FAIL", w[0], w[1], w[2], w[3], w[4]);
    bad += !ok;
  }
  printf("%d witnesses, %d failures\n", count, bad);
  return bad != 0 || count != 36;
}
