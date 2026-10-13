/-!
# Clique blow-ups of odd cycles

`C_{2k+1}[w]` has bags `0, 1, …, 2k` on a cycle; bag `i` is a clique on `w i` vertices and the
cliques of consecutive bags are joined completely. Vertex `(i, j)` exists when `i < 2k+1` and
`j < w i`. We prove that `C_{2k+1}[w]` has a proper colouring with `c` colours exactly when
`w i + w (i+1) ≤ c` for all consecutive bags and `n ≤ k * c`, where `n` is the number of vertices.
This is formula (5) of Trivedi's Question 7.1, `χ = max(max_i (w i + w (i+1)), ⌈n / k⌉)`, for every
`k ≥ 1`. With the two planarity facts as hypotheses, it gives `χ ≤ 9` for every biplanar
`C_{2k+1}[w]` with `k ≥ 3`.
-/

namespace Biplanar.OddCycle

/-- `sumTo f n = f 0 + ⋯ + f (n-1)` -/
def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo f n + f n

/-- `maxTo f n = max (f 0) … (f (n-1))`, and `0` for `n = 0` -/
def maxTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => max (maxTo f n) (f n)

/-- bags `i` and `i'` of the cycle on `L` bags are equal or consecutive -/
def Near (L i i' : Nat) : Prop :=
  i = i' ∨ i' = i + 1 ∨ i = i' + 1 ∨ (i = 0 ∧ i' + 1 = L) ∨ (i' = 0 ∧ i + 1 = L)

/-- `col` is a proper colouring of `C_L[w]` with colours below `c` -/
def Proper (L : Nat) (w : Nat → Nat) (c : Nat) (col : Nat → Nat → Nat) : Prop :=
  (∀ i j, i < L → j < w i → col i j < c) ∧
  (∀ i j i' j', i < L → j < w i → i' < L → j' < w i' → Near L i i' → (i ≠ i' ∨ j ≠ j') →
    col i j ≠ col i' j')

/-- the conditions of formula (5) for `c` colours on `C_{2k+1}[w]` -/
def Fits (k : Nat) (w : Nat → Nat) (c : Nat) : Prop :=
  (∀ i, i < 2 * k → w i + w (i + 1) ≤ c) ∧ w (2 * k) + w 0 ≤ c ∧ sumTo w (2 * k + 1) ≤ k * c

/-! ### Finite sums -/

theorem sumTo_succ (f : Nat → Nat) (n : Nat) : sumTo f (n + 1) = sumTo f n + f n := rfl

theorem sumTo_congr (f g : Nat → Nat) (n : Nat) (h : ∀ x, x < n → f x = g x) :
    sumTo f n = sumTo g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumTo_succ, sumTo_succ, ih (fun x hx => h x (by omega)), h n (by omega)]

theorem sumTo_add (f g : Nat → Nat) (n : Nat) :
    sumTo (fun x => f x + g x) n = sumTo f n + sumTo g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumTo_succ, sumTo_succ, sumTo_succ, ih]; omega

theorem sumTo_le (f g : Nat → Nat) (n : Nat) (h : ∀ x, x < n → f x ≤ g x) :
    sumTo f n ≤ sumTo g n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    have h1 := ih (fun x hx => h x (by omega))
    have h2 := h n (by omega)
    rw [sumTo_succ, sumTo_succ]
    omega

theorem sumTo_const (a n : Nat) : sumTo (fun _ => a) n = n * a := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => rw [sumTo_succ, ih, Nat.add_mul, Nat.one_mul]

theorem sumTo_shift (f : Nat → Nat) (n : Nat) :
    sumTo f (n + 1) = f 0 + sumTo (fun x => f (x + 1)) n := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => rw [sumTo_succ, ih, sumTo_succ]; omega

theorem sumTo_comm (g : Nat → Nat → Nat) (a b : Nat) :
    sumTo (fun i => sumTo (fun x => g i x) b) a = sumTo (fun x => sumTo (fun i => g i x) a) b := by
  induction a with
  | zero =>
    have h := sumTo_const 0 b
    simp only [sumTo] at h ⊢
    omega
  | succ a ih =>
    rw [sumTo_succ, ih]
    exact (sumTo_add (fun x => sumTo (fun i => g i x) a) (fun x => g a x) b).symm

/-- going once round the cycle counts every bag twice -/
theorem cycle_pairs (f : Nat → Nat) (n : Nat) :
    sumTo (fun i => f i + f (i + 1)) n + (f n + f 0) = 2 * sumTo f (n + 1) := by
  rw [sumTo_add]
  have e1 := sumTo_shift f n
  have e2 := sumTo_succ f n
  omega

/-- an independent set of the cycle `C_{2k+1}` has at most `k` elements -/
theorem cycle_indep (k : Nat) (f : Nat → Nat) (h : ∀ i, i < 2 * k → f i + f (i + 1) ≤ 1)
    (hw : f (2 * k) + f 0 ≤ 1) : sumTo f (2 * k + 1) ≤ k := by
  have h1 := sumTo_le (fun i => f i + f (i + 1)) (fun _ => 1) (2 * k) h
  rw [sumTo_const] at h1
  have h2 := cycle_pairs f (2 * k)
  omega

/-! ### Counting the colours of a bag -/

/-- `hits f x a` says that `x = f j` for some `j < a` -/
def hits (f : Nat → Nat) (x : Nat) : Nat → Bool
  | 0 => false
  | a + 1 => hits f x a || f a == x

theorem hits_iff (f : Nat → Nat) (x a : Nat) : hits f x a = true ↔ ∃ j, j < a ∧ f j = x := by
  induction a with
  | zero => simp [hits]
  | succ a ih =>
    simp only [hits, Bool.or_eq_true, beq_iff_eq, ih]
    constructor
    · rintro (⟨j, hj, h⟩ | h)
      · exact ⟨j, by omega, h⟩
      · exact ⟨a, by omega, h⟩
    · rintro ⟨j, hj, h⟩
      by_cases hja : j = a
      · subst hja; exact Or.inr h
      · exact Or.inl ⟨j, by omega, h⟩

/-- `ind f a x = 1` when colour `x` is used by `f` on `0, …, a-1`, and `0` otherwise -/
def ind (f : Nat → Nat) (a x : Nat) : Nat := if hits f x a then 1 else 0

theorem ind_le (f : Nat → Nat) (a x : Nat) : ind f a x ≤ 1 := by
  unfold ind; split <;> omega

theorem sumTo_single (y c : Nat) :
    sumTo (fun x => if y = x then 1 else 0) c = if y < c then 1 else 0 := by
  induction c with
  | zero => simp [sumTo]
  | succ c ih =>
    rw [sumTo_succ, ih]
    by_cases h1 : y < c
    · have h2 : y ≠ c := by omega
      simp [h1, h2, show y < c + 1 by omega]
    · by_cases h2 : y = c
      · subst h2; simp
      · have h3 : ¬ y < c + 1 := by omega
        simp [h1, h2, h3]

/-- an injective map from `0, …, a-1` into `0, …, c-1` uses exactly `a` colours -/
theorem count_image (f : Nat → Nat) (c : Nat) : ∀ a, (∀ j, j < a → f j < c) →
    (∀ j j', j < a → j' < a → f j = f j' → j = j') → sumTo (ind f a) c = a := by
  intro a
  induction a with
  | zero =>
    intro _ _
    rw [sumTo_congr _ (fun _ => 0) c (fun x _ => by simp [ind, hits]), sumTo_const, Nat.mul_zero]
  | succ a ih =>
    intro hlt hinj
    have hsplit : ∀ x, ind f (a + 1) x = ind f a x + (if f a = x then 1 else 0) := by
      intro x
      by_cases hx : f a = x
      · have hn : hits f x a = false := by
          cases h : hits f x a with
          | false => rfl
          | true =>
            obtain ⟨j, hj, hfj⟩ := (hits_iff f x a).1 h
            have := hinj j a (by omega) (by omega) (by rw [hfj, hx])
            omega
        simp [ind, hits, hn, hx]
      · simp [ind, hits, hx]
    rw [sumTo_congr _ _ c (fun x _ => hsplit x)]
    rw [sumTo_add (ind f a) (fun x => if f a = x then 1 else 0) c]
    rw [ih (fun j hj => hlt j (by omega))
      (fun j j' hj hj' h => hinj j j' (by omega) (by omega) h), sumTo_single]
    simp [hlt a (by omega)]

/-! ### Lower bound: every proper colouring satisfies the conditions -/

theorem fits_of_proper (k : Nat) (hk : 1 ≤ k) (w : Nat → Nat) (c : Nat) (col : Nat → Nat → Nat)
    (hp : Proper (2 * k + 1) w c col) : Fits k w c := by
  obtain ⟨hlt, hne⟩ := hp
  -- bag `i` uses exactly `w i` colours
  have hbag : ∀ i, i < 2 * k + 1 → sumTo (ind (col i) (w i)) c = w i := by
    intro i hi
    apply count_image (col i) c (w i) (fun j hj => hlt i j hi hj)
    intro j j' hj hj' h
    apply Classical.byContradiction
    intro hjj
    exact hne i j i j' hi hj hi hj' (Or.inl rfl) (Or.inr hjj) h
  -- two different near bags share no colour
  have hpair : ∀ i i', i < 2 * k + 1 → i' < 2 * k + 1 → Near (2 * k + 1) i i' → i ≠ i' →
      ∀ x, ind (col i) (w i) x + ind (col i') (w i') x ≤ 1 := by
    intro i i' hi hi' hn hii x
    unfold ind
    cases h1 : hits (col i) x (w i) with
    | false => simp only [Bool.false_eq_true, ite_false, Nat.zero_add]; split <;> omega
    | true =>
      cases h2 : hits (col i') x (w i') with
      | false => simp
      | true =>
        obtain ⟨j, hj, e⟩ := (hits_iff _ _ _).1 h1
        obtain ⟨j', hj', e'⟩ := (hits_iff _ _ _).1 h2
        exact absurd (e.trans e'.symm) (hne i j i' j' hi hj hi' hj' hn (Or.inl hii))
  -- so two near bags use at most `c` colours together
  have hsum : ∀ i i', i < 2 * k + 1 → i' < 2 * k + 1 → Near (2 * k + 1) i i' → i ≠ i' →
      w i + w i' ≤ c := by
    intro i i' hi hi' hn hii
    have h := sumTo_le (fun x => ind (col i) (w i) x + ind (col i') (w i') x) (fun _ => 1) c
      (fun x _ => hpair i i' hi hi' hn hii x)
    rw [sumTo_add, sumTo_const, hbag i hi, hbag i' hi'] at h
    omega
  refine ⟨fun i hi => hsum i (i + 1) (by omega) (by omega) (Or.inr (Or.inl rfl)) (by omega),
    hsum (2 * k) 0 (by omega) (by omega) (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
      (by omega), ?_⟩
  -- each colour is used on at most `k` bags, since those bags are independent in `C_{2k+1}`
  have hcol : ∀ x, sumTo (fun i => ind (col i) (w i) x) (2 * k + 1) ≤ k := by
    intro x
    apply cycle_indep k
    · intro i hi
      exact hpair i (i + 1) (by omega) (by omega) (Or.inr (Or.inl rfl)) (by omega) x
    · exact hpair (2 * k) 0 (by omega) (by omega) (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
        (by omega) x
  have e1 : sumTo w (2 * k + 1) =
      sumTo (fun i => sumTo (fun x => ind (col i) (w i) x) c) (2 * k + 1) :=
    sumTo_congr _ _ _ (fun i hi => (hbag i hi).symm)
  rw [e1, sumTo_comm]
  have h := sumTo_le _ (fun _ => k) c (fun x _ => hcol x)
  rw [sumTo_const, Nat.mul_comm c k] at h
  exact h

/-! ### Upper bound: the arc colouring -/

/-- `cap w m i = Σ_{t<i} (m - w t - w (t+1))`, the room left between the first `i+1` arcs -/
def cap (w : Nat → Nat) (m : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => cap w m i + (m - w i - w (i + 1))

/-- the first colour of bag `i`: the arcs are packed in order, and the `k * m - n` spare colours
are spent on the first gaps -/
def start (k : Nat) (w : Nat → Nat) (m i : Nat) : Nat :=
  sumTo w i + min (k * m - sumTo w (2 * k + 1)) (cap w m i)

/-- bag `i` gets the colours `start i, …, start i + w i - 1`, read modulo `m` -/
def arcCol (k : Nat) (w : Nat → Nat) (m : Nat) (i j : Nat) : Nat := (start k w m i + j) % m

theorem mod_ne (a b m : Nat) (hab : a < b) (hbm : b < a + m) : a % m ≠ b % m := by
  intro h
  have h1 : (b - a) % m = 0 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
  have h2 : m ≤ b - a := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero h1)
  omega

theorem cap_eq (k : Nat) (w : Nat → Nat) (m : Nat) (h : ∀ i, i < 2 * k → w i + w (i + 1) ≤ m) :
    ∀ i, i ≤ 2 * k → cap w m i + sumTo w i + sumTo w (i + 1) = i * m + w 0 := by
  intro i
  induction i with
  | zero => intro _; simp [cap, sumTo]
  | succ i ih =>
    intro hi
    have e := ih (by omega)
    have hw := h i (by omega)
    rw [sumTo_succ] at e
    simp only [cap, sumTo_succ]
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem start_step (k : Nat) (w : Nat → Nat) (m i : Nat) (hi : w i + w (i + 1) ≤ m) :
    start k w m i + w i ≤ start k w m (i + 1) ∧
      start k w m (i + 1) + w (i + 1) ≤ start k w m i + m := by
  simp only [start, cap, sumTo_succ]
  omega

theorem start_zero (k : Nat) (w : Nat → Nat) (m : Nat) : start k w m 0 = 0 := by
  simp [start, cap, sumTo]

theorem start_last (k : Nat) (w : Nat → Nat) (m : Nat) (h : ∀ i, i < 2 * k → w i + w (i + 1) ≤ m)
    (hn : sumTo w (2 * k + 1) ≤ k * m) : start k w m (2 * k) + w (2 * k) = k * m := by
  have e := cap_eq k w m h (2 * k) (Nat.le_refl _)
  have e2 := sumTo_succ w (2 * k)
  have e3 : 2 * k * m = 2 * (k * m) := Nat.mul_assoc 2 k m
  simp only [start]
  omega

/-- the last arc ends at `k * m`, so it sits at the top of `0, …, m-1` and misses the first arc -/
theorem wrap_ne (k : Nat) (hk : 1 ≤ k) (w : Nat → Nat) (m : Nat) (hf : Fits k w m) (j j' : Nat)
    (hj : j < w 0) (hj' : j' < w (2 * k)) : arcCol k w m 0 j ≠ arcCol k w m (2 * k) j' := by
  obtain ⟨h, hw, hn⟩ := hf
  have hl := start_last k w m h hn
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_mul, Nat.one_mul] at hl
  have e : start (k' + 1) w m (2 * (k' + 1)) + j' = (m - w (2 * (k' + 1)) + j') + k' * m := by
    omega
  unfold arcCol
  rw [start_zero, e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (show m - w (2 * (k' + 1)) + j' < m by omega),
    Nat.zero_add, Nat.mod_eq_of_lt (show j < m by omega)]
  omega

theorem proper_of_fits (k : Nat) (hk : 1 ≤ k) (w : Nat → Nat) (m : Nat) (hf : Fits k w m) :
    Proper (2 * k + 1) w m (arcCol k w m) := by
  have hf' := hf
  obtain ⟨h, hw, hn⟩ := hf'
  have hwm : ∀ i, i < 2 * k + 1 → w i ≤ m := by
    intro i hi
    by_cases hi' : i < 2 * k
    · have := h i hi'; omega
    · have : i = 2 * k := by omega
      subst this; omega
  refine ⟨fun i j hi hj => Nat.mod_lt _ (by have := hwm i hi; omega), ?_⟩
  intro i j i' j' hi hj hi' hj' hnear hd
  have hm1 := hwm i hi
  have hm2 := hwm i' hi'
  unfold Near at hnear
  rcases hnear with e | e | e | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · -- the same bag
    subst e
    have hjj : j ≠ j' := by rcases hd with hd | hd <;> omega
    unfold arcCol
    rcases Nat.lt_or_gt_of_ne hjj with hlt | hlt
    · exact mod_ne _ _ m (by omega) (by omega)
    · exact fun e => mod_ne _ _ m (by omega) (by omega) e.symm
  · -- bag `i'` follows bag `i`
    subst e
    have st := start_step k w m i (h i (by omega))
    unfold arcCol
    exact mod_ne _ _ m (by omega) (by omega)
  · -- bag `i` follows bag `i'`
    subst e
    have st := start_step k w m i' (h i' (by omega))
    unfold arcCol
    exact fun e => mod_ne _ _ m (by omega) (by omega) e.symm
  · -- bag `i` is the first and bag `i'` the last
    subst e1
    have : i' = 2 * k := by omega
    subst this
    exact wrap_ne k hk w m hf j j' hj hj'
  · -- bag `i` is the last and bag `i'` the first
    subst e1
    have : i = 2 * k := by omega
    subst this
    exact fun e => wrap_ne k hk w m hf j' j hj' hj e.symm

/-- `C_{2k+1}[w]` has a proper colouring with `c` colours exactly when every two consecutive bags
have at most `c` vertices together and `n ≤ k * c` -/
theorem colourable_iff (k : Nat) (hk : 1 ≤ k) (w : Nat → Nat) (c : Nat) :
    (∃ col, Proper (2 * k + 1) w c col) ↔ Fits k w c :=
  ⟨fun ⟨col, h⟩ => fits_of_proper k hk w c col h, fun h => ⟨_, proper_of_fits k hk w c h⟩⟩

/-! ### Formula (5) -/

theorem le_maxTo (f : Nat → Nat) (n i : Nat) (hi : i < n) : f i ≤ maxTo f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [maxTo]
    by_cases h : i < n
    · have := ih h; omega
    · have : i = n := by omega
      subst this; omega

theorem maxTo_le (f : Nat → Nat) (n c : Nat) (h : ∀ i, i < n → f i ≤ c) : maxTo f n ≤ c := by
  induction n with
  | zero => simp [maxTo]
  | succ n ih =>
    simp only [maxTo]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h n (by omega)
    omega

/-- the largest number of vertices in two consecutive bags -/
def pairMax (k : Nat) (w : Nat → Nat) : Nat :=
  max (maxTo (fun i => w i + w (i + 1)) (2 * k)) (w (2 * k) + w 0)

/-- `⌈n / k⌉ ≤ c` exactly when `n ≤ k * c` -/
theorem ceil_le (n k c : Nat) (hk : 1 ≤ k) : (n + k - 1) / k ≤ c ↔ n ≤ k * c := by
  have h := @Nat.div_lt_iff_lt_mul k (n + k - 1) (c + 1) (by omega)
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm c k] at h
  constructor
  · intro h1; have := h.1 (by omega); omega
  · intro h1; have := h.2 (by omega); omega

theorem fits_iff (k : Nat) (hk : 1 ≤ k) (w : Nat → Nat) (c : Nat) :
    Fits k w c ↔ max (pairMax k w) ((sumTo w (2 * k + 1) + k - 1) / k) ≤ c := by
  rw [Nat.max_le, ceil_le _ _ _ hk]
  unfold Fits pairMax
  rw [Nat.max_le]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨maxTo_le _ _ _ h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨fun i hi => Nat.le_trans (le_maxTo (fun i => w i + w (i + 1)) _ i hi) h1, h2, h3⟩

/-- Formula (5): `χ(C_{2k+1}[w]) = max(max_i (w i + w (i+1)), ⌈n / k⌉)` for every `k ≥ 1`.
The maximum is a number of colours that suffices, and no smaller number does. -/
theorem chromatic (k : Nat) (hk : 1 ≤ k) (w : Nat → Nat) :
    (∃ col, Proper (2 * k + 1) w (max (pairMax k w) ((sumTo w (2 * k + 1) + k - 1) / k)) col) ∧
    ∀ c col, Proper (2 * k + 1) w c col →
      max (pairMax k w) ((sumTo w (2 * k + 1) + k - 1) / k) ≤ c :=
  ⟨(colourable_iff k hk w _).2 ((fits_iff k hk w _).2 (Nat.le_refl _)),
    fun c col h => (fits_iff k hk w c).1 (fits_of_proper k hk w c col h)⟩

/-! ### Consequences for biplanar blow-ups

A biplanar graph contains no `K_9`, so every two consecutive bags have at most `8` vertices
together; and the edges between bags form a triangle-free graph (the cycle has length at least
five), which has at most `2n - 4` edges in each of the two planar layers. These two facts are
hypotheses here. -/

/-- `k ≥ 4`: clique number at most `8` already gives `9` colours -/
theorem nine_of_long (k : Nat) (hk : 4 ≤ k) (w : Nat → Nat)
    (h : ∀ i, i < 2 * k → w i + w (i + 1) ≤ 8) (hw : w (2 * k) + w 0 ≤ 8) :
    ∃ col, Proper (2 * k + 1) w 9 col := by
  apply (colourable_iff k (by omega) w 9).2
  refine ⟨fun i hi => by have := h i hi; omega, by omega, ?_⟩
  have h1 := sumTo_le (fun i => w i + w (i + 1)) (fun _ => 8) (2 * k) h
  rw [sumTo_const] at h1
  have h2 := cycle_pairs w (2 * k)
  omega

/-- `k = 3`: clique number at most `8` and at most `4n - 8` edges between bags give `9` colours -/
theorem nine_of_seven (w : Nat → Nat) (h : ∀ i, i < 6 → w i + w (i + 1) ≤ 8) (hw : w 6 + w 0 ≤ 8)
    (hx : sumTo (fun i => w i * w (i + 1)) 6 + w 6 * w 0 + 8 ≤ 4 * sumTo w 7) :
    ∃ col, Proper (2 * 3 + 1) w 9 col := by
  apply (colourable_iff 3 (by omega) w 9).2
  refine ⟨fun i hi => by have := h i hi; omega, by show w 6 + w 0 ≤ 9; omega, ?_⟩
  show sumTo w 7 ≤ 27
  have h0 : w 0 + w 1 ≤ 8 := h 0 (by omega)
  have h1 : w 1 + w 2 ≤ 8 := h 1 (by omega)
  have h2 : w 2 + w 3 ≤ 8 := h 2 (by omega)
  have h3 : w 3 + w 4 ≤ 8 := h 3 (by omega)
  have h4 : w 4 + w 5 ≤ 8 := h 4 (by omega)
  have h5 : w 5 + w 6 ≤ 8 := h 5 (by omega)
  simp only [sumTo, Nat.zero_add, Nat.reduceAdd] at hx ⊢
  -- `n ≥ 28` would force every two consecutive bags to have exactly `8` vertices, so `w = 4^7`,
  -- which has `7 * 16 = 112 > 104` edges between bags
  apply Classical.byContradiction
  intro hlt
  have e : w 0 = 4 ∧ w 1 = 4 ∧ w 2 = 4 ∧ w 3 = 4 ∧ w 4 = 4 ∧ w 5 = 4 ∧ w 6 = 4 := by omega
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := e
  rw [e0, e1, e2, e3, e4, e5, e6] at hx
  omega

end Biplanar.OddCycle
