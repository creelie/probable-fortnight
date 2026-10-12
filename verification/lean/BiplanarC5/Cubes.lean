import Std.Tactic.BVDecide
open Std.Sat

/-!
# Splitting a formula along a decision tree

A cube is a list of DIMACS literals (nonzero integers; the variable `x` of `encode` is the DIMACS
variable `x + 1`). `withCube f c` adds the unit clauses of `c` to `f`. If the cubes in `S` are the
leaves of a binary decision tree (`complete d S`, depth at most `d`) and `f` with each leaf is
unsatisfiable, then `f` is unsatisfiable (`unsat_of_complete`).
-/

namespace Biplanar

/-- The literal of `encode` named by the DIMACS literal `x`. -/
def litOf (x : Int) : Literal Nat := (x.natAbs - 1, decide (0 < x))

/-- `f` together with the unit clauses of the cube `c`. -/
def withCube (f : CNF Nat) (c : List Int) : CNF Nat :=
  { clauses := f.clauses ++ (c.map fun x => [litOf x]).toArray }

/-- The cubes whose first literal is `x`, with that literal removed. -/
def branch (x : Int) (S : List (List Int)) : List (List Int) :=
  S.filterMap fun c => match c with
    | y :: t => if y = x then some t else none
    | [] => none

/-- `S` lists the leaves of a binary decision tree of depth at most `d`. -/
def complete : Nat → List (List Int) → Bool
  | _, [[]] => true
  | d + 1, (x :: t) :: S =>
      x != 0 && ((x :: t) :: S).all (fun c => match c with
        | y :: _ => y == x || y == -x
        | [] => false) &&
      complete d (branch x ((x :: t) :: S)) && complete d (branch (-x) ((x :: t) :: S))
  | _, _ => false

theorem eval_withCube_append (a : Nat → Bool) (f : CNF Nat) (p : List Int) (x : Int) :
    (withCube f (p ++ [x])).eval a = ((withCube f p).eval a && a (litOf x).1 == (litOf x).2) := by
  simp [withCube, CNF.eval, List.map_append, Bool.and_assoc]

theorem mem_branch {x : Int} {S : List (List Int)} {t : List Int} :
    t ∈ branch x S ↔ (x :: t) ∈ S := by
  unfold branch
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, h⟩
    match c, h with
    | y :: t', h =>
      by_cases hy : y = x
      · subst hy; simp at h; subst h; exact hc
      · simp [hy] at h
  · intro h
    exact ⟨x :: t, h, by simp⟩

/-- The decision on the literal `x`: an assignment satisfies `x` or `-x`. -/
theorem lit_or_neg (a : Nat → Bool) (x : Int) (hx : x ≠ 0) :
    (a (litOf x).1 == (litOf x).2) = true ∨ (a (litOf (-x)).1 == (litOf (-x)).2) = true := by
  simp only [litOf, Int.natAbs_neg]
  rcases Int.lt_or_gt_of_ne hx with h | h
  · have h1 : ¬ (0 < x) := by omega
    have h2 : 0 < -x := by omega
    cases ha : a (x.natAbs - 1) <;> simp [h1] <;> omega
  · have h1 : ¬ (0 < -x) := by omega
    cases ha : a (x.natAbs - 1) <;> simp [h] <;> omega

theorem unsat_of_complete (f : CNF Nat) (d : Nat) :
    ∀ (S : List (List Int)) (p : List Int), complete d S = true →
      (∀ c ∈ S, (withCube f (p ++ c)).Unsat) → (withCube f p).Unsat := by
  induction d with
  | zero =>
    intro S p hc h
    unfold complete at hc
    split at hc
    · simpa using h [] (by simp)
    all_goals first | omega | simp at hc
  | succ d ih =>
    intro S p hc h
    unfold complete at hc
    split at hc
    · simpa using h [] (by simp)
    · rename_i d' x t S' heq
      have hd : d = d' := by omega
      subst hd
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
      obtain ⟨⟨⟨hx, _⟩, hpos⟩, hneg⟩ := hc
      have hb : ∀ y, complete d (branch y ((x :: t) :: S')) = true →
          (withCube f (p ++ [y])).Unsat := fun y hy =>
        ih _ (p ++ [y]) hy fun u hu => by
          have := h (y :: u) (mem_branch.mp hu)
          simpa using this
      have h1 := hb x hpos
      have h2 := hb (-x) hneg
      intro a
      rcases lit_or_neg a x hx with hl | hl
      · have := h1 a
        rw [eval_withCube_append, hl, Bool.and_true] at this
        exact this
      · have := h2 a
        rw [eval_withCube_append, hl, Bool.and_true] at this
        exact this
    · simp at hc

/-- With the empty prefix: the leaves of a complete tree refute `f`. -/
theorem unsat_of_leaves (f : CNF Nat) (d : Nat) (S : List (List Int)) (hc : complete d S = true)
    (h : ∀ c ∈ S, (withCube f c).Unsat) : f.Unsat := by
  have := unsat_of_complete f d S [] hc (by simpa using h)
  intro a
  simpa [withCube, CNF.eval] using this a

end Biplanar
