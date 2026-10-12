/-!
# The finite reduction

`cands17` lists the 26 weight vectors with 17 vertices and clique number at most 8, and `wits16` the 36
with 16 vertices, each up to rotation and reflection of the 5-cycle. Every weight vector with positive
entries and clique number at most 8 dominates (entrywise, after a symmetry of the cycle) a member of
`cands17` when it has at least 17 vertices, and is dominated by a member of `wits16` otherwise.
-/

namespace Biplanar

def cands17 : List (List Nat) :=
  [[1, 1, 7, 1, 7],
  [1, 2, 6, 1, 7],
  [1, 2, 6, 2, 6],
  [1, 3, 5, 1, 7],
  [1, 3, 5, 2, 6],
  [1, 3, 5, 3, 5],
  [1, 4, 4, 1, 7],
  [1, 4, 4, 2, 6],
  [1, 4, 4, 3, 5],
  [1, 4, 4, 4, 4],
  [1, 5, 3, 2, 6],
  [1, 5, 3, 3, 5],
  [1, 6, 2, 2, 6],
  [2, 2, 5, 2, 6],
  [2, 2, 5, 3, 5],
  [2, 3, 4, 2, 6],
  [2, 3, 4, 3, 5],
  [2, 3, 4, 4, 4],
  [2, 3, 5, 2, 5],
  [2, 3, 5, 3, 4],
  [2, 4, 3, 3, 5],
  [2, 4, 3, 4, 4],
  [2, 4, 4, 2, 5],
  [3, 3, 3, 3, 5],
  [3, 3, 3, 4, 4],
  [3, 3, 4, 3, 4]]

def wits16 : List (List Nat) :=
  [[1, 1, 6, 1, 7],
  [1, 1, 6, 2, 6],
  [1, 2, 5, 1, 7],
  [1, 2, 5, 2, 6],
  [1, 2, 5, 3, 5],
  [1, 2, 6, 1, 6],
  [1, 2, 6, 2, 5],
  [1, 3, 4, 1, 7],
  [1, 3, 4, 2, 6],
  [1, 3, 4, 3, 5],
  [1, 3, 4, 4, 4],
  [1, 3, 5, 1, 6],
  [1, 3, 5, 2, 5],
  [1, 3, 5, 3, 4],
  [1, 4, 3, 2, 6],
  [1, 4, 3, 3, 5],
  [1, 4, 3, 4, 4],
  [1, 4, 4, 1, 6],
  [1, 4, 4, 2, 5],
  [1, 5, 2, 2, 6],
  [1, 5, 2, 3, 5],
  [2, 2, 4, 2, 6],
  [2, 2, 4, 3, 5],
  [2, 2, 4, 4, 4],
  [2, 2, 5, 2, 5],
  [2, 3, 3, 2, 6],
  [2, 3, 3, 3, 5],
  [2, 3, 3, 4, 4],
  [2, 3, 3, 5, 3],
  [2, 3, 4, 2, 5],
  [2, 3, 4, 3, 4],
  [2, 3, 4, 4, 3],
  [2, 3, 5, 2, 4],
  [2, 4, 2, 4, 4],
  [2, 4, 3, 3, 4],
  [3, 3, 3, 3, 4]]

def rot (w : List Nat) (r : Nat) : List Nat := w.drop r ++ w.take r
def symmetries (w : List Nat) : List (List Nat) :=
  (List.range w.length).flatMap fun r => [rot w r, (rot w r).reverse]
def leAll (a b : List Nat) : Bool := a.length == b.length && (List.zipWith Nat.ble a b).all id
def maxAdj (w : List Nat) : Nat :=
  ((List.range w.length).map fun i => w[i]! + w[(i + 1) % w.length]!).foldl max 0

/-- the 26 vectors are pairwise inequivalent, have 17 vertices and clique number at most 8 -/
theorem cands17_spec : (cands17.length == 26 &&
    cands17.all (fun w => w.length == 5 && w.sum == 17 && maxAdj w ≤ 8 && w.all (1 ≤ ·)) &&
    (List.range 26).all fun i => (List.range 26).all fun j =>
      i == j || !((symmetries cands17[i]!).contains cands17[j]!)) = true := by decide

/-- the 36 vectors are pairwise inequivalent, have 16 vertices and clique number at most 8 -/
theorem wits16_spec : (wits16.length == 36 &&
    wits16.all (fun w => w.length == 5 && w.sum == 16 && maxAdj w ≤ 8 && w.all (1 ≤ ·)) &&
    (List.range 36).all fun i => (List.range 36).all fun j =>
      i == j || !((symmetries wits16[i]!).contains wits16[j]!)) = true := by decide

/-- the property checked for one weight vector: when it is positive with clique number at most 8,
it is above a member of `cands17` (at least 17 vertices) or below a member of `wits16` (otherwise) -/
def reduces (w : List Nat) : Bool :=
  !(w.all (1 ≤ ·) && maxAdj w ≤ 8) ||
    (if 17 ≤ w.sum then cands17.any (fun v => (symmetries w).any (leAll v))
     else wits16.any (fun v => (symmetries w).any (fun u => leAll u v)))

/-- the table for a fixed first entry -/
def reducesRow (a : Nat) : Bool :=
  (List.range 8).all fun b => (List.range 8).all fun c => (List.range 8).all fun d =>
    (List.range 8).all fun e => reduces [a, b, c, d, e]

theorem reducesRow_0 : reducesRow 0 = true := by decide +kernel

theorem reducesRow_1 : reducesRow 1 = true := by decide +kernel

theorem reducesRow_2 : reducesRow 2 = true := by decide +kernel

theorem reducesRow_3 : reducesRow 3 = true := by decide +kernel

theorem reducesRow_4 : reducesRow 4 = true := by decide +kernel

theorem reducesRow_5 : reducesRow 5 = true := by decide +kernel

theorem reducesRow_6 : reducesRow 6 = true := by decide +kernel

theorem reducesRow_7 : reducesRow 7 = true := by decide +kernel


theorem reduction (a b c d e : Nat) (ha : a < 8) (hb : b < 8) (hc : c < 8) (hd : d < 8)
    (he : e < 8) : reduces [a, b, c, d, e] = true := by
  have h : reducesRow a = true := by
    match a, ha with
    | 0, _ => exact reducesRow_0
    | 1, _ => exact reducesRow_1
    | 2, _ => exact reducesRow_2
    | 3, _ => exact reducesRow_3
    | 4, _ => exact reducesRow_4
    | 5, _ => exact reducesRow_5
    | 6, _ => exact reducesRow_6
    | 7, _ => exact reducesRow_7
  simp only [reducesRow, List.all_eq_true, List.mem_range] at h
  exact h b hb c hc d hd e he

/-- with positive entries, clique number at most 8 forces every entry below 8 -/
theorem entries_lt_8 (a b c d e : Nat) (hb : 1 ≤ b) (he : 1 ≤ e) (h1 : a + b ≤ 8) (h2 : b + c ≤ 8)
    (_h3 : c + d ≤ 8) (h4 : d + e ≤ 8) (h5 : e + a ≤ 8) (_hd : 1 ≤ d) (ha : 1 ≤ a) (hc : 1 ≤ c) :
    a < 8 ∧ b < 8 ∧ c < 8 ∧ d < 8 ∧ e < 8 := by omega

end Biplanar
