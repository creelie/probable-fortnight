/-!
# Straight-line drawings with integer coordinates

A *drawing* of a graph with vertex set `{0, …, n-1}` and edge list `E` places vertex `v` at the lattice
point `pos[v]`. It is *plane* when the points are distinct, no vertex lies on an edge it does not belong
to, and two edges without a common endpoint have disjoint (closed) segments. Two edges with a common
endpoint then meet only there. A graph with a plane drawing is planar, so a graph whose edges are
covered by two edge lists, each with a plane drawing, is biplanar. All tests are exact integer
arithmetic.
-/

namespace Biplanar

abbrev Pt := Int × Int

/-- twice the signed area of the triangle `abc` -/
def orient (a b c : Pt) : Int := (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- `p` lies on the closed segment `ab` -/
def onSeg (a b p : Pt) : Bool :=
  orient a b p == 0 && min a.1 b.1 ≤ p.1 && p.1 ≤ max a.1 b.1 &&
    min a.2 b.2 ≤ p.2 && p.2 ≤ max a.2 b.2

/-- the closed segments `ab` and `cd` meet -/
def segsMeet (a b c d : Pt) : Bool :=
  let d1 := orient c d a; let d2 := orient c d b
  let d3 := orient a b c; let d4 := orient a b d
  ((d1 > 0 && d2 < 0) || (d1 < 0 && d2 > 0)) && ((d3 > 0 && d4 < 0) || (d3 < 0 && d4 > 0)) ||
    onSeg c d a || onSeg c d b || onSeg a b c || onSeg a b d

/-- `pos` is a plane straight-line drawing of the graph `(n, E)` -/
def isPlaneDrawing (n : Nat) (E : List (Nat × Nat)) (pos : List Pt) : Bool :=
  pos.length == n &&
  (E.all fun (u, v) => u < n && v < n && u != v) &&
  ((List.range n).all fun u => (List.range n).all fun v => u == v || pos[u]! != pos[v]!) &&
  (E.all fun (u, v) => (List.range n).all fun x =>
      x == u || x == v || !onSeg pos[u]! pos[v]! pos[x]!) &&
  (E.all fun (u, v) => E.all fun (s, t) =>
      u == s || u == t || v == s || v == t || !segsMeet pos[u]! pos[v]! pos[s]! pos[t]!)

/-- clique blow-up `C_k[w]`: vertex lists of the bags, in order -/
def bags (w : List Nat) : List Nat := Id.run do
  let mut b : List Nat := []
  for i in [0:w.length] do
    b := b ++ List.replicate w[i]! i
  return b

def blowupEdges (w : List Nat) : List (Nat × Nat) :=
  let b := bags w; let n := b.length; let k := w.length
  (List.range n).flatMap fun u => ((List.range n).filter fun v => u < v &&
    (let d := (b[u]! + k - b[v]!) % k; d == 0 || d == 1 || d == k - 1)).map fun v => (u, v)

/-- the edges of `C_k[w]` are covered by two edge lists with plane drawings -/
def BiplanarWitness (w : List Nat) (L0 L1 : List (Nat × Nat)) (p0 p1 : List Pt) : Bool :=
  let n := (bags w).length
  ((blowupEdges w).all fun e => L0.contains e || L1.contains e) &&
  isPlaneDrawing n L0 p0 && isPlaneDrawing n L1 p1

end Biplanar
