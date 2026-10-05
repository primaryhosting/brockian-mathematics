/-
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-! ## A clocked model of computation

Programs are natural numbers (their own Gödel numbers).  A code `c` is decoded
on the fly:

* `0` : the constant `0`
* `1` : the successor function
* `2` : first projection of the Cantor pairing
* `3` : second projection of the Cantor pairing
* `4` : the *clocked universal machine*: on input `⟪c', y, k⟫` it simulates the
  program `c'` on input `y` for `k` steps and outputs the result (or `0` if
  the simulation did not finish);  this costs `k + 1` steps
* `5` : the boolean complement `x ↦ if x = 0 then 1 else 0`
* `6` : the identity
* `7 + 4 * ⟪i, j⟫ + 0` : pairing of the results of `i` and `j`
* `7 + 4 * ⟪i, j⟫ + 1` : composition `i ∘ j`
* `7 + 4 * ⟪i, j⟫ + 2` : primitive recursion
* `7 + 4 * ⟪i, j⟫ + 3` : unbounded search (`rfind`)

`eval s c x` runs the program `c` on input `x` with a budget of `s` steps and
returns `none` if the budget is exhausted.  Every constructor consumes one unit
of the budget, so `eval` is a genuine (if coarse) cost model. -/
def eval : ℕ → ℕ → ℕ → Option ℕ
  | 0, _, _ => none
  | s+1, c, x =>
    if c = 0 then some 0
    else if c = 1 then some (x + 1)
    else if c = 2 then some (Nat.unpair x).1
    else if c = 3 then some (Nat.unpair x).2
    else if c = 4 then
      (if _h : (Nat.unpair (Nat.unpair x).2).2 ≤ s then
        some ((eval (Nat.unpair (Nat.unpair x).2).2 (Nat.unpair x).1
                (Nat.unpair (Nat.unpair x).2).1).getD 0)
      else none)
    else if c = 5 then some (if x = 0 then 1 else 0)
    else if c = 6 then some x
    else
      if (c - 7) % 4 = 0 then
        (eval s (Nat.unpair ((c - 7) / 4)).1 x).bind fun a =>
          (eval s (Nat.unpair ((c - 7) / 4)).2 x).map fun b => Nat.pair a b
      else if (c - 7) % 4 = 1 then
        (eval s (Nat.unpair ((c - 7) / 4)).2 x).bind fun b =>
          eval s (Nat.unpair ((c - 7) / 4)).1 b
      else if (c - 7) % 4 = 2 then
        (match (Nat.unpair x).2 with
         | 0 => eval s (Nat.unpair ((c - 7) / 4)).1 (Nat.unpair x).1
         | n+1 => (eval s c (Nat.pair (Nat.unpair x).1 n)).bind fun v =>
                    eval s (Nat.unpair ((c - 7) / 4)).2 (Nat.pair (Nat.unpair x).1 (Nat.pair n v)))
      else
        (eval s (Nat.unpair ((c - 7) / 4)).1 x).bind fun v =>
          if v = 0 then some (Nat.unpair x).2
          else eval s c (Nat.pair (Nat.unpair x).1 ((Nat.unpair x).2 + 1))
termination_by s => s

/-- Code of the clocked universal machine. -/
def cUniv : ℕ := 4
/-- Code of the boolean complement. -/
def cNot : ℕ := 5
/-- Code of the identity. -/
def cId : ℕ := 6
/-- Code of the pairing of two programs. -/
def cPair (i j : ℕ) : ℕ := 7 + 4 * Nat.pair i j
/-- Code of the composition of two programs. -/
def cComp (i j : ℕ) : ℕ := 7 + 4 * Nat.pair i j + 1
/-- Code of primitive recursion. -/
def cPrec (i j : ℕ) : ℕ := 7 + 4 * Nat.pair i j + 2
/-- Code of unbounded search. -/
def cRfind (i j : ℕ) : ℕ := 7 + 4 * Nat.pair i j + 3

/-! ### Unfolding lemmas -/

@[simp] theorem eval_zero_fuel (c x : ℕ) : eval 0 c x = none := by
  rw [eval]

@[simp] theorem eval_c0 (s x : ℕ) : eval (s+1) 0 x = some 0 := by
  rw [eval]; norm_num

@[simp] theorem eval_c1 (s x : ℕ) : eval (s+1) 1 x = some (x + 1) := by
  rw [eval]; norm_num

@[simp] theorem eval_c2 (s x : ℕ) : eval (s+1) 2 x = some (Nat.unpair x).1 := by
  rw [eval]; norm_num

@[simp] theorem eval_c3 (s x : ℕ) : eval (s+1) 3 x = some (Nat.unpair x).2 := by
  rw [eval]; norm_num

@[simp] theorem eval_cNot (s x : ℕ) : eval (s+1) cNot x = some (if x = 0 then 1 else 0) := by
  rw [cNot, eval]; norm_num

@[simp] theorem eval_cId (s x : ℕ) : eval (s+1) cId x = some x := by
  rw [cId, eval]; norm_num

theorem eval_cUniv_def (s x : ℕ) :
    eval (s+1) cUniv x =
      (if (Nat.unpair (Nat.unpair x).2).2 ≤ s then
        some ((eval (Nat.unpair (Nat.unpair x).2).2 (Nat.unpair x).1
                (Nat.unpair (Nat.unpair x).2).1).getD 0)
      else none) := by
  rw [cUniv, eval]; norm_num

/-- The clocked universal machine simulates `c` on `y` for `k` steps, at a cost of `k+1`. -/
theorem eval_cUniv (s c y k : ℕ) (hk : k ≤ s) :
    eval (s+1) cUniv (Nat.pair c (Nat.pair y k)) = some ((eval k c y).getD 0) := by
  rw [eval_cUniv_def]
  simp [Nat.unpair_pair, hk]

theorem eval_cPair (s i j x : ℕ) :
    eval (s+1) (cPair i j) x =
      (eval s i x).bind fun a => (eval s j x).map fun b => Nat.pair a b := by
  have hu : Nat.unpair (Nat.pair i j) = (i, j) := Nat.unpair_pair i j
  simp only [cPair]
  generalize Nat.pair i j = p at hu ⊢
  rw [eval]
  simp only [hu, show (7 + 4*p - 7) % 4 = 0 from by omega,
    show (7 + 4*p - 7) / 4 = p from by omega,
    show ¬ (7+4*p = 0) from by omega, show ¬ (7+4*p = 1) from by omega,
    show ¬ (7+4*p = 2) from by omega, show ¬ (7+4*p = 3) from by omega,
    show ¬ (7+4*p = 4) from by omega, show ¬ (7+4*p = 5) from by omega,
    show ¬ (7+4*p = 6) from by omega, if_false, if_true]

theorem eval_cComp (s i j x : ℕ) :
    eval (s+1) (cComp i j) x = (eval s j x).bind fun b => eval s i b := by
  have hu : Nat.unpair (Nat.pair i j) = (i, j) := Nat.unpair_pair i j
  simp only [cComp]
  generalize Nat.pair i j = p at hu ⊢
  rw [eval]
  simp only [hu, show (7 + 4*p + 1 - 7) % 4 = 1 from by omega,
    show (7 + 4*p + 1 - 7) / 4 = p from by omega,
    show ¬ (7+4*p+1 = 0) from by omega, show ¬ (7+4*p+1 = 1) from by omega,
    show ¬ (7+4*p+1 = 2) from by omega, show ¬ (7+4*p+1 = 3) from by omega,
    show ¬ (7+4*p+1 = 4) from by omega, show ¬ (7+4*p+1 = 5) from by omega,
    show ¬ (7+4*p+1 = 6) from by omega, one_ne_zero, if_false, if_true]

theorem eval_cPrec_zero (s i j x : ℕ) (hx : (Nat.unpair x).2 = 0) :
    eval (s+1) (cPrec i j) x = eval s i (Nat.unpair x).1 := by
  have hu : Nat.unpair (Nat.pair i j) = (i, j) := Nat.unpair_pair i j
  simp only [cPrec]
  generalize Nat.pair i j = p at hu ⊢
  rw [eval]
  simp only [hu, hx, show (7 + 4*p + 2 - 7) % 4 = 2 from by omega,
    show (7 + 4*p + 2 - 7) / 4 = p from by omega,
    show ¬ (7+4*p+2 = 0) from by omega, show ¬ (7+4*p+2 = 1) from by omega,
    show ¬ (7+4*p+2 = 2) from by omega, show ¬ (7+4*p+2 = 3) from by omega,
    show ¬ (7+4*p+2 = 4) from by omega, show ¬ (7+4*p+2 = 5) from by omega,
    show ¬ (7+4*p+2 = 6) from by omega, OfNat.ofNat_ne_zero, if_false, if_true,
    show (2:ℕ) ≠ 1 from by omega]

theorem eval_cPrec_succ (s i j x n : ℕ) (hx : (Nat.unpair x).2 = n + 1) :
    eval (s+1) (cPrec i j) x =
      (eval s (cPrec i j) (Nat.pair (Nat.unpair x).1 n)).bind fun v =>
        eval s j (Nat.pair (Nat.unpair x).1 (Nat.pair n v)) := by
  have hu : Nat.unpair (Nat.pair i j) = (i, j) := Nat.unpair_pair i j
  simp only [cPrec]
  generalize Nat.pair i j = p at hu ⊢
  rw [eval]
  simp only [hu, hx, show (7 + 4*p + 2 - 7) % 4 = 2 from by omega,
    show (7 + 4*p + 2 - 7) / 4 = p from by omega,
    show ¬ (7+4*p+2 = 0) from by omega, show ¬ (7+4*p+2 = 1) from by omega,
    show ¬ (7+4*p+2 = 2) from by omega, show ¬ (7+4*p+2 = 3) from by omega,
    show ¬ (7+4*p+2 = 4) from by omega, show ¬ (7+4*p+2 = 5) from by omega,
    show ¬ (7+4*p+2 = 6) from by omega, OfNat.ofNat_ne_zero, if_false, if_true,
    show (2:ℕ) ≠ 1 from by omega]

theorem eval_cRfind (s i j x : ℕ) :
    eval (s+1) (cRfind i j) x =
      (eval s i x).bind fun v =>
        if v = 0 then some (Nat.unpair x).2
        else eval s (cRfind i j) (Nat.pair (Nat.unpair x).1 ((Nat.unpair x).2 + 1)) := by
  have hu : Nat.unpair (Nat.pair i j) = (i, j) := Nat.unpair_pair i j
  simp only [cRfind]
  generalize Nat.pair i j = p at hu ⊢
  rw [eval]
  simp only [hu, show (7 + 4*p + 3 - 7) % 4 = 3 from by omega,
    show (7 + 4*p + 3 - 7) / 4 = p from by omega,
    show ¬ (7+4*p+3 = 0) from by omega, show ¬ (7+4*p+3 = 1) from by omega,
    show ¬ (7+4*p+3 = 2) from by omega, show ¬ (7+4*p+3 = 3) from by omega,
    show ¬ (7+4*p+3 = 4) from by omega, show ¬ (7+4*p+3 = 5) from by omega,
    show ¬ (7+4*p+3 = 6) from by omega, OfNat.ofNat_ne_zero, if_false,
    show (3:ℕ) ≠ 1 from by omega, show (3:ℕ) ≠ 2 from by omega]

/-- Every code is one of the seven atomic codes or a compound code. -/
theorem code_cases (c : ℕ) :
    c ≤ 6 ∨ ∃ i j, c = cPair i j ∨ c = cComp i j ∨ c = cPrec i j ∨ c = cRfind i j := by
  by_cases h : c ≤ 6
  · exact Or.inl h
  · right
    refine ⟨(Nat.unpair ((c - 7) / 4)).1, (Nat.unpair ((c - 7) / 4)).2, ?_⟩
    have hp : Nat.pair (Nat.unpair ((c - 7) / 4)).1 (Nat.unpair ((c - 7) / 4)).2 = (c - 7) / 4 :=
      Nat.pair_unpair _
    simp only [cPair, cComp, cPrec, cRfind, hp]
    omega

/-! ### Monotonicity in the step budget -/

theorem eval_mono_succ : ∀ s c x v, eval s c x = some v → eval (s+1) c x = some v := by
  intro s
  induction s with
  | zero => intro c x v h; simp at h
  | succ s ih =>
    intro c x v h
    rcases code_cases c with hc | ⟨i, j, hc⟩
    · interval_cases c
      · simpa using h
      · simpa using h
      · simpa using h
      · simpa using h
      · rw [show (4:ℕ) = cUniv from rfl, eval_cUniv_def] at h ⊢
        by_cases hk : (Nat.unpair (Nat.unpair x).2).2 ≤ s
        · rw [if_pos hk] at h
          rw [if_pos (by omega)]
          exact h
        · rw [if_neg hk] at h
          exact absurd h (by simp)
      · rw [show (5:ℕ) = cNot from rfl] at h ⊢
        simpa using h
      · rw [show (6:ℕ) = cId from rfl] at h ⊢
        simpa using h
    · rcases hc with hc | hc | hc | hc <;> subst hc
      · rw [eval_cPair] at h ⊢
        simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
        obtain ⟨a, ha, b, hb, hab⟩ := h
        exact ⟨a, ih _ _ _ ha, b, ih _ _ _ hb, hab⟩
      · rw [eval_cComp] at h ⊢
        simp only [Option.bind_eq_some_iff] at h ⊢
        obtain ⟨b, hb, hv⟩ := h
        exact ⟨b, ih _ _ _ hb, ih _ _ _ hv⟩
      · rcases hx : (Nat.unpair x).2 with _ | n
        · rw [eval_cPrec_zero _ _ _ _ hx] at h ⊢
          exact ih _ _ _ h
        · rw [eval_cPrec_succ _ _ _ _ _ hx] at h ⊢
          simp only [Option.bind_eq_some_iff] at h ⊢
          obtain ⟨b, hb, hv⟩ := h
          exact ⟨b, ih _ _ _ hb, ih _ _ _ hv⟩
      · rw [eval_cRfind] at h ⊢
        simp only [Option.bind_eq_some_iff] at h ⊢
        obtain ⟨b, hb, hv⟩ := h
        refine ⟨b, ih _ _ _ hb, ?_⟩
        split_ifs at hv ⊢ with hb0
        · exact hv
        · exact ih _ _ _ hv

theorem eval_mono {s s' c x v : ℕ} (hs : s ≤ s') (h : eval s c x = some v) :
    eval s' c x = some v := by
  induction s', hs using Nat.le_induction with
  | base => exact h
  | succ n hn ih => exact eval_mono_succ _ _ _ _ ih


/-! ## Time-bounded complexity classes and the hierarchy theorem -/

/-- A language over `ℕ` is decided by the program `c` within the time bound `t` if,
for every input `x`, running `c` on `x` with a budget of `t x` steps outputs
`1` when `x` is in the language and `0` otherwise. -/
def TIME (t : ℕ → ℕ) : Set (ℕ → Bool) :=
  {L | ∃ c, ∀ x, eval (t x) c x = some (if L x then 1 else 0)}

/-- Larger time bounds decide at least as many languages. -/
theorem TIME_mono {t T : ℕ → ℕ} (h : ∀ x, t x ≤ T x) : TIME t ⊆ TIME T := by
  rintro L ⟨c, hc⟩
  exact ⟨c, fun x => eval_mono (h x) (hc x)⟩

/-- The diagonal language: `x` belongs to it iff the program with code `x`,
run on the input `x` for `t x` steps, fails to output a nonzero value. -/
def diag (t : ℕ → ℕ) : ℕ → Bool := fun x => decide ((eval (t x) x x).getD 0 = 0)

/-- The diagonal language is not decidable within time `t`: this is the
diagonalization step. -/
theorem diag_not_mem_TIME (t : ℕ → ℕ) : diag t ∉ TIME t := by
  rintro ⟨c, hc⟩
  have h := hc c
  have hv : (eval (t c) c c).getD 0 = if diag t c then 1 else 0 := by rw [h]; rfl
  have hd : diag t c = true ↔ (eval (t c) c c).getD 0 = 0 := by simp [diag]
  by_cases hb : diag t c = true
  · have h0 : (eval (t c) c c).getD 0 = 0 := hd.mp hb
    rw [hb] at hv
    simp only [if_true] at hv
    omega
  · have h0 : (eval (t c) c c).getD 0 ≠ 0 := fun hz => hb (hd.mpr hz)
    simp only [Bool.not_eq_true] at hb
    rw [hb] at hv
    simp only [Bool.false_eq_true, if_false] at hv
    exact h0 hv

/-- The code of the diagonalizing program: given a program `ct` that maps `x` to the
triple `⟪x, x, t x⟫`, first build that triple, then run the clocked universal
machine on it, then complement the answer. -/
def cDiag (ct : ℕ) : ℕ := cComp cNot (cComp cUniv ct)

/-- The diagonalizing program decides the diagonal language in
`τ x + t x + 3` steps, where `τ` bounds the cost of computing `⟪x, x, t x⟫`. -/
theorem eval_cDiag (t τ : ℕ → ℕ) (ct : ℕ)
    (hct : ∀ x, eval (τ x) ct x = some (Nat.pair x (Nat.pair x (t x)))) (x : ℕ) :
    eval (τ x + t x + 3) (cDiag ct) x = some (if diag t x then 1 else 0) := by
  have hsim : eval (τ x + t x + 2) (cComp cUniv ct) x = some ((eval (t x) x x).getD 0) := by
    rw [show τ x + t x + 2 = (τ x + t x + 1) + 1 from rfl, eval_cComp]
    rw [eval_mono (show τ x ≤ τ x + t x + 1 by omega) (hct x)]
    simpa using eval_cUniv (τ x + t x) x x (t x) (by omega)
  rw [cDiag, show τ x + t x + 3 = (τ x + t x + 2) + 1 from rfl, eval_cComp, hsim]
  simp only [Option.bind_some, eval_cNot, diag]
  by_cases hz : (eval (t x) x x).getD 0 = 0 <;> simp [hz]

/-- **Time hierarchy theorem.**  Let `t` be a time bound such that the map
`x ↦ ⟪x, x, t x⟫` is computable by the program `ct` within `τ x` steps (a
time-constructibility hypothesis), and let `T` be any time bound exceeding
`τ + t + 3`.  Then strictly more languages are decidable in time `T` than in
time `t`: the diagonal language `diag t` witnesses the strict inclusion. -/
theorem time_hierarchy (t T τ : ℕ → ℕ) (ct : ℕ)
    (hct : ∀ x, eval (τ x) ct x = some (Nat.pair x (Nat.pair x (t x))))
    (hT : ∀ x, τ x + t x + 3 ≤ T x) :
    TIME t ⊂ TIME T := by
  have hsub : TIME t ⊆ TIME T := TIME_mono (fun x => by have := hT x; omega)
  rw [Set.ssubset_iff_of_subset hsub]
  refine ⟨diag t, ⟨cDiag ct, fun x => ?_⟩, diag_not_mem_TIME t⟩
  exact eval_mono (hT x) (eval_cDiag t τ ct hct x)

/-! ## The hypotheses are satisfiable: constant time bounds

To see that the hierarchy theorem is not vacuous we exhibit, for every constant
time bound, a program computing the required triple `⟪x, x, t x⟫`. -/

/-- A program computing the constant `n`. -/
def cConst : ℕ → ℕ
  | 0 => 0
  | n+1 => cComp 1 (cConst n)

theorem eval_cConst (n : ℕ) : ∀ x, eval (n+1) (cConst n) x = some n := by
  induction n with
  | zero => intro x; simp [cConst]
  | succ n ih =>
    intro x
    rw [cConst, show n + 1 + 1 = (n+1) + 1 from rfl, eval_cComp, ih x]
    simp

/-- A program mapping `x` to the triple `⟪x, x, N⟫`. -/
def cTriple (N : ℕ) : ℕ := cPair cId (cPair cId (cConst N))

theorem eval_cTriple (N x : ℕ) :
    eval (N + 3) (cTriple N) x = some (Nat.pair x (Nat.pair x N)) := by
  have h1 : eval (N + 2) (cPair cId (cConst N)) x = some (Nat.pair x N) := by
    rw [show N + 2 = (N+1) + 1 from rfl, eval_cPair, eval_cConst N x]
    simp
  rw [cTriple, show N + 3 = (N+2) + 1 from rfl, eval_cPair, h1]
  simp

/-- **Time hierarchy theorem, constant bounds.**  Strictly more languages can be
decided in `2 * N + 6` steps than in `N` steps. -/
theorem time_hierarchy_const (N : ℕ) :
    TIME (fun _ => N) ⊂ TIME (fun _ => 2 * N + 6) :=
  time_hierarchy (fun _ => N) (fun _ => 2 * N + 6) (fun _ => N + 3) (cTriple N)
    (fun x => eval_cTriple N x) (fun _ => by simp; omega)

end CS

