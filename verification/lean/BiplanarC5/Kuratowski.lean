import BiplanarC5.Encode
import BiplanarC5.Cubes
open Std.Sat

/-!
# Kuratowski clauses

A Kuratowski clause is a DIMACS clause `¬lay l a₁ b₁ ∨ … ∨ ¬lay l aₖ bₖ` whose edges `aᵢbᵢ` form a
subdivision of `K₅` or `K₃,₃` inside `C₅[w]`: it says that these edges do not all lie in layer `l`.
A planar graph contains no such subdivision, so every biplanar drawing satisfies these clauses, and
`withKur (encode w) K` is satisfiable whenever `C₅[w]` is biplanar and `kurOK w K` holds. The check
`isKuratowski` follows, from every vertex of degree at least three, each path through vertices of
degree two to its other end, and compares the resulting multigraph with `K₅` and `K₃,₃`.
-/

namespace Biplanar

/-- the number of edges of `S` at `v` -/
def degIn (S : List (Nat × Nat)) (v : Nat) : Nat := S.countP fun e => e.1 == v || e.2 == v

/-- the vertices of `S` -/
def vertsOf (S : List (Nat × Nat)) : List Nat := (S.flatMap fun e => [e.1, e.2]).eraseDups

/-- Leave `v` along the edge `e` and continue through vertices of degree two in `S`; return the first
vertex of another degree (at most `fuel` steps). -/
def follow (S : List (Nat × Nat)) : Nat → Nat → Nat × Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, v, e =>
    let x := if e.1 == v then e.2 else e.1
    if degIn S x != 2 then some x
    else match S.find? (fun f => f != e && (f.1 == x || f.2 == x)) with
      | some f => follow S fuel x f
      | none => none

/-- the ends of the paths that leave the branch vertex `b` -/
def endsFrom (S : List (Nat × Nat)) (b : Nat) : List (Option Nat) :=
  (S.filter fun e => e.1 == b || e.2 == b).map fun e => follow S S.length b e

/-- `ends` lists each vertex of `T` once and nothing else -/
def isPermOf (ends : List (Option Nat)) (T : List Nat) : Bool :=
  ends.length == T.length && (ends.all fun o => match o with
    | some x => T.contains x
    | none => false) && (ends.filterMap id).Nodup

/-- `S` (distinct edges `a < b`) contains a subdivision of `K₅` or `K₃,₃` whose branch vertices are
the vertices of degree at least three, all other vertices having degree two -/
def isKuratowski (S : List (Nat × Nat)) : Bool :=
  let V := vertsOf S
  let B := V.filter fun v => degIn S v ≥ 3
  S.Nodup && (S.all fun e => e.1 < e.2) && (V.all fun v => degIn S v ≥ 3 || degIn S v == 2) &&
  ((B.length == 5 && B.all fun b => degIn S b == 4 && isPermOf (endsFrom S b) (B.erase b)) ||
   (B.length == 6 && match B with
    | b₀ :: _ =>
      let Y := (endsFrom S b₀).filterMap id
      let X := B.filter fun v => !Y.contains v
      B.all (fun b => degIn S b == 3) && X.length == 3 && Y.length == 3 &&
        (X.all fun x => isPermOf (endsFrom S x) Y) && (Y.all fun y => isPermOf (endsFrom S y) X)
    | [] => false))

/-- The edge and layer of the variable `lay l a b` of `encode w` (DIMACS numbering), if it is one. -/
def layOf (I : Inst) (x : Nat) : Option (Nat × Nat × Nat) :=
  if 6 * I.n * I.n + 1 ≤ x ∧ x ≤ 8 * I.n * I.n then
    let r := x - 1 - 6 * I.n * I.n
    some (r / (I.n * I.n), (r / I.n) % I.n, r % I.n)
  else none

/-- `c` is the Kuratowski clause of a subdivision of `K₅` or `K₃,₃` in `C₅[w]` and one layer -/
def kurClauseOK (I : Inst) (c : List Int) : Bool :=
  match c.head? with
  | none => false
  | some x₀ =>
    match layOf I x₀.natAbs with
    | none => false
    | some (l, _, _) =>
      let es := c.filterMap fun (x : Int) =>
        if x < 0 then
          match layOf I x.natAbs with
          | some (l', a, b) => if l' == l && a < b && I.adj a b then some (a, b) else none
          | none => none
        else none
      es.length == c.length && isKuratowski es

def kurOK (w : List Nat) (K : List (List Int)) : Bool :=
  K.all (kurClauseOK (mkInst w))

/-- `f` together with the clauses `K` (DIMACS literals) -/
def withKur (f : CNF Nat) (K : List (List Int)) : CNF Nat :=
  { clauses := f.clauses ++ (K.map fun c => c.map litOf).toArray }

/-- Parse DIMACS clause lines (each ending in `0`). -/
def parseClauses (s : String) : List (List Int) :=
  let toks (l : String) : List String := (l.splitOn " ").filter fun t => !t.isEmpty && t != "0"
  ((s.splitOn "\n").map toks).filter (!·.isEmpty) |>.map (·.map String.toInt!)

/-- `a` satisfies `encode w` and every Kuratowski clause of `C₅[w]`. Every biplanar drawing of `C₅[w]`
gives such an assignment: Schnyder's theorem for `encode w`, and the planarity of each layer for the
Kuratowski clauses. -/
def KurModel (w : List Nat) (a : Nat → Bool) : Prop :=
  (encode w).eval a = true ∧
    ∀ c, kurClauseOK (mkInst w) c = true → (c.any fun x => a (litOf x).1 == (litOf x).2) = true

/-- `g` has no model satisfying `P` -/
def UnsatOn (P : (Nat → Bool) → Prop) (g : CNF Nat) : Prop := ∀ a, P a → g.eval a = false

theorem eval_withKur (a : Nat → Bool) (f : CNF Nat) (K : List (List Int)) :
    (withKur f K).eval a =
      (f.eval a && K.all fun c => c.any fun x => a (litOf x).1 == (litOf x).2) := by
  simp [withKur, CNF.eval, CNF.Clause.eval, List.all_map, List.any_map, Function.comp_def]

theorem eval_withCube (a : Nat → Bool) (f : CNF Nat) (c : List Int) :
    (withCube f c).eval a = (f.eval a && c.all fun x => a (litOf x).1 == (litOf x).2) := by
  simp [withCube, CNF.eval, CNF.Clause.eval, List.all_map, Function.comp_def]

theorem kurModel_eval {w : List Nat} {a : Nat → Bool} {K : List (List Int)} (h : KurModel w a)
    (hK : kurOK w K = true) : (withKur (encode w) K).eval a = true := by
  rw [eval_withKur, h.1, Bool.true_and, List.all_eq_true]
  intro c hc
  exact h.2 c (List.all_eq_true.mp hK c hc)

/-- No `KurModel` exists when `encode w` together with Kuratowski clauses is unsatisfiable. -/
theorem no_kurModel {w : List Nat} {K : List (List Int)} (hK : kurOK w K = true)
    (hU : (withKur (encode w) K).Unsat) (a : Nat → Bool) : ¬ KurModel w a := fun h => by
  have := hU a
  rw [kurModel_eval h hK] at this
  exact Bool.false_ne_true this.symm

theorem unsatOn_of_complete (P : (Nat → Bool) → Prop) (f : CNF Nat) (d : Nat) :
    ∀ (S : List (List Int)) (p : List Int), complete d S = true →
      (∀ c ∈ S, UnsatOn P (withCube f (p ++ c))) → UnsatOn P (withCube f p) := by
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
          UnsatOn P (withCube f (p ++ [y])) := fun y hy =>
        ih _ (p ++ [y]) hy fun u hu => by
          have := h (y :: u) (mem_branch.mp hu)
          simpa using this
      have h1 := hb x hpos
      have h2 := hb (-x) hneg
      intro a ha
      rcases lit_or_neg a x hx with hl | hl
      · have := h1 a ha
        rw [eval_withCube_append, hl, Bool.and_true] at this
        exact this
      · have := h2 a ha
        rw [eval_withCube_append, hl, Bool.and_true] at this
        exact this
    · simp at hc

/-- If the leaves of a complete decision tree are each refuted together with Kuratowski clauses of
`C₅[w]`, then no `KurModel` exists, so `C₅[w]` is not biplanar. -/
theorem no_kurModel_of_leaves (w : List Nat) (d : Nat) (S : List (List Int))
    (hc : complete d S = true)
    (h : ∀ c ∈ S, ∃ K, kurOK w K = true ∧ (withCube (withKur (encode w) K) c).Unsat)
    (a : Nat → Bool) : ¬ KurModel w a := by
  have hl : ∀ c ∈ S, UnsatOn (KurModel w) (withCube (encode w) ([] ++ c)) := by
    intro c hcS b hb
    obtain ⟨K, hK, hU⟩ := h c hcS
    have := hU b
    rw [eval_withCube, kurModel_eval hb hK, Bool.true_and] at this
    rw [List.nil_append, eval_withCube, hb.1, Bool.true_and]
    exact this
  intro ha
  have := unsatOn_of_complete (KurModel w) (encode w) d S [] hc hl a ha
  rw [eval_withCube, ha.1] at this
  simp at this

end Biplanar
