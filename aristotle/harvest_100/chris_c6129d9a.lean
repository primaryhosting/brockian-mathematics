/-
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The required header above is a plain block comment rather than a module
-- docstring `/-! ... -/` because Lean 4 does not allow any command, including a
-- module docstring, to precede the `import` lines.)

import Mathlib

/-!
## Overview

This file formalises **Ladner's theorem**: if `P ≠ NP` then there is an
*NP-intermediate* language, i.e. a language that lies in `NP`, is not in `P`,
and is not `NP`-complete.

Mathlib contains no development of time-bounded complexity classes, so the
complexity-theoretic setting is packaged as an explicit `CS.Framework`
structure whose fields are exactly the standard facts about `P`, `NP` and
polynomial-time many-one reductions that Ladner's argument uses:

* `P` is exactly the collection of languages decided by one of the machines of a
  fixed enumeration `dec` of polynomial-time deciders;
* polynomial-time many-one reductions are exactly the functions of a fixed
  enumeration `red`;
* `P ⊆ NP`, `∅ ∈ P`, `P` is closed under finite variants and downwards under
  many-one reductions;
* `SAT` is `NP`-complete;
* the enumerations come with *clocked* simulations `decT`, `haltsDec`, `redT`
  which are sound, monotone in the clock, and eventually converge (this is the
  usual efficient universal simulation, and it is what makes the delayed
  diagonalisation below effective);
* `holes_mem_NP`: the language obtained from `SAT` by punching holes according
  to the (explicitly defined) Ladner stage function lies in `NP`.  This single
  field records the effectiveness content of Ladner's construction, namely that
  the stage function is polynomial-time computable.

Strings are encoded as natural numbers, and the length of the string coded by
`x` is `Nat.size x` (the number of binary digits of `x`).  All searches in the
construction range over inputs of length at most `Nat.log 2 n` at stage `n`, and
all simulations are clocked by `n`, exactly as in the classical proof.

Everything apart from the framework's fields — the construction of the stage
function, its unboundedness, and the three defining properties of the
intermediate language — is proved.
-/

namespace CS

attribute [local instance] Classical.propDecidable

/-- A language: a set of natural numbers (binary strings encoded as numbers). -/
abbrev Lang := Set ℕ

/-- The machine data of a complexity-theoretic setting: enumerations of the
polynomial-time deciders and of the polynomial-time functions, clocked versions
of both, and a distinguished language `SAT`. -/
structure Machines where
  /-- `dec i x` : value computed by the `i`-th polynomial-time decider on `x`. -/
  dec : ℕ → ℕ → Bool
  /-- `red i x` : value of the `i`-th polynomial-time function on `x`. -/
  red : ℕ → ℕ → ℕ
  /-- `decT i x t` : the `i`-th decider simulated on `x` for `t` steps. -/
  decT : ℕ → ℕ → ℕ → Bool
  /-- `haltsDec i x t` : whether that simulation has finished within `t` steps. -/
  haltsDec : ℕ → ℕ → ℕ → Bool
  /-- `redT i x t` : the `i`-th function simulated on `x` for `t` steps. -/
  redT : ℕ → ℕ → ℕ → Option ℕ
  /-- A distinguished `NP`-complete language. -/
  SAT : Lang

namespace Machines

/-- The "bump condition" driving Ladner's delayed diagonalisation.

At stage `n`, with current counter `k`, and with the already-computed values of
the stage function on `[0, n]` given by `g`:

* if `k = 2 i` is even we look for a short input `x` on which the `i`-th
  polynomial-time decider provably disagrees with the language
  `{x | x ∈ SAT ∧ Even (g (Nat.size x))}`;
* if `k = 2 i + 1` is odd we look for a short input `x` witnessing that the
  `i`-th polynomial-time function is not a many-one reduction of `SAT` to that
  language.

All searches are bounded: only inputs of length at most `Nat.log 2 n` are
considered, and simulations are run for at most `n` steps. -/
def bump (M : Machines) (k n : ℕ) (g : ℕ → ℕ) : Prop :=
  if Even k then
    ∃ x, Nat.size x ≤ Nat.log 2 n ∧ M.haltsDec (k / 2) x n = true ∧
      ¬ ((x ∈ M.SAT ∧ Even (g (Nat.size x))) ↔ M.decT (k / 2) x n = true)
  else
    ∃ x, Nat.size x ≤ Nat.log 2 n ∧ ∃ y, Nat.size y ≤ n ∧ M.redT (k / 2) x n = some y ∧
      ¬ (x ∈ M.SAT ↔ (y ∈ M.SAT ∧ Even (g (Nat.size y))))

/-- `clamp M n` is the stage function computed up to time `n` (and held constant
afterwards).  It is defined by structural recursion on `n`. -/
noncomputable def clamp (M : Machines) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | (n + 1), m =>
      if m ≤ n then clamp M n m
      else if bump M (clamp M n n) n (clamp M n) then clamp M n n + 1 else clamp M n n

/-- Ladner's stage function. -/
noncomputable def stage (M : Machines) (n : ℕ) : ℕ := clamp M n n

end Machines

/-- A complexity-theoretic framework: machine data together with the standard
structural facts about `P`, `NP` and polynomial-time many-one reductions. -/
structure Framework where
  /-- The machine data. -/
  M : Machines
  /-- The class `P`. -/
  P : Set Lang
  /-- The class `NP`. -/
  NP : Set Lang
  /-- `P` is exactly the class of languages decided by an enumerated decider. -/
  mem_P : ∀ L : Lang, L ∈ P ↔ ∃ i, ∀ x, x ∈ L ↔ M.dec i x = true
  /-- `P ⊆ NP`. -/
  P_sub_NP : P ⊆ NP
  /-- The empty language is in `P`. -/
  empty_mem_P : (∅ : Lang) ∈ P
  /-- `P` is closed under finite variants. -/
  P_finite_variant : ∀ (K L : Lang) (N : ℕ), K ∈ P →
    (∀ x, N ≤ x → (x ∈ K ↔ x ∈ L)) → L ∈ P
  /-- `P` is closed downwards under polynomial-time many-one reductions. -/
  P_red_closed : ∀ (A B : Lang), (∃ i, ∀ x, x ∈ A ↔ M.red i x ∈ B) → B ∈ P → A ∈ P
  /-- `SAT` is in `NP`. -/
  SAT_mem_NP : M.SAT ∈ NP
  /-- `SAT` is `NP`-hard. -/
  SAT_hard : ∀ L ∈ NP, ∃ i, ∀ x, x ∈ L ↔ M.red i x ∈ M.SAT
  /-- A halted clocked simulation returns the true value. -/
  decT_sound : ∀ i x t, M.haltsDec i x t = true → M.decT i x t = M.dec i x
  /-- Halting is monotone in the clock. -/
  haltsDec_mono : ∀ i x t t', t ≤ t' → M.haltsDec i x t = true → M.haltsDec i x t' = true
  /-- Every enumerated decider halts on every input, given enough steps. -/
  haltsDec_ex : ∀ i x, ∃ t, M.haltsDec i x t = true
  /-- A converged clocked function simulation returns the true value. -/
  redT_sound : ∀ i x t y, M.redT i x t = some y → y = M.red i x
  /-- Convergence of the clocked function simulation is monotone in the clock. -/
  redT_mono : ∀ i x t t' y, t ≤ t' → M.redT i x t = some y → M.redT i x t' = some y
  /-- Every enumerated function converges on every input, given enough steps. -/
  redT_ex : ∀ i x, ∃ t, M.redT i x t = some (M.red i x)
  /-- Effectiveness of the construction: the language obtained from `SAT` by
  punching holes according to the stage function is in `NP`.  In the intended
  interpretation this holds because the stage function is polynomial-time
  computable. -/
  holes_mem_NP : {x | x ∈ M.SAT ∧ Even (M.stage (Nat.size x))} ∈ NP

namespace Framework

variable (F : Framework)

/-- Polynomial-time many-one reducibility. -/
def Reduces (A B : Lang) : Prop := ∃ i, ∀ x, x ∈ A ↔ F.M.red i x ∈ B

/-- `NP`-completeness. -/
def NPComplete (L : Lang) : Prop := L ∈ F.NP ∧ ∀ K ∈ F.NP, F.Reduces K L

/-- A language is `NP`-intermediate if it is in `NP`, is not in `P`, and is not
`NP`-complete. -/
def NPIntermediate (L : Lang) : Prop := L ∈ F.NP ∧ L ∉ F.P ∧ ¬ F.NPComplete L

/-- The language produced by Ladner's construction. -/
def ladnerLang : Lang := {x | x ∈ F.M.SAT ∧ Even (F.M.stage (Nat.size x))}

end Framework

/-! ### Basic properties of the stage function -/

namespace Machines

variable (M : Machines)

lemma clamp_of_le : ∀ (n m : ℕ), m ≤ n → M.clamp n m = M.stage m := by
  intro n
  induction n with
  | zero => intro m hm; interval_cases m; rfl
  | succ n ih =>
      intro m hm
      rcases Nat.lt_or_ge m (n + 1) with h | h
      · have hmn : m ≤ n := Nat.lt_succ_iff.mp h
        rw [clamp, if_pos hmn]
        exact ih m hmn
      · have : m = n + 1 := le_antisymm hm h
        subst this
        rfl

lemma clamp_of_ge : ∀ (n m : ℕ), n ≤ m → M.clamp n m = M.stage n := by
  intro n
  induction n with
  | zero => intro m _; rfl
  | succ n _ =>
      intro m hm
      have h1 : ¬ (m ≤ n) := by omega
      have h2 : ¬ (n + 1 ≤ n) := by omega
      have hst : M.stage (n + 1) =
          if M.bump (M.clamp n n) n (M.clamp n) then M.clamp n n + 1 else M.clamp n n := by
        show M.clamp (n + 1) (n + 1) = _
        rw [clamp, if_neg h2]
      rw [clamp, if_neg h1, hst]

lemma clamp_eq_stage_min (n m : ℕ) : M.clamp n m = M.stage (min m n) := by
  rcases le_total m n with h | h
  · rw [clamp_of_le M n m h, min_eq_left h]
  · rw [clamp_of_ge M n m h, min_eq_right h]

lemma bump_congr {k n : ℕ} {g g' : ℕ → ℕ} (h : ∀ m ≤ n, g m = g' m) :
    M.bump k n g ↔ M.bump k n g' := by
  have hlog : ∀ x : ℕ, Nat.size x ≤ Nat.log 2 n → Nat.size x ≤ n :=
    fun x hx => le_trans hx (Nat.log_le_self 2 n)
  unfold bump
  by_cases hk : Even k
  · simp only [if_pos hk]
    constructor
    · rintro ⟨x, hx, h1, h2⟩
      exact ⟨x, hx, h1, by rwa [← h _ (hlog x hx)]⟩
    · rintro ⟨x, hx, h1, h2⟩
      exact ⟨x, hx, h1, by rwa [h _ (hlog x hx)]⟩
  · simp only [if_neg hk]
    constructor
    · rintro ⟨x, hx, y, hy, h1, h2⟩
      exact ⟨x, hx, y, hy, h1, by rwa [← h _ hy]⟩
    · rintro ⟨x, hx, y, hy, h1, h2⟩
      exact ⟨x, hx, y, hy, h1, by rwa [h _ hy]⟩

/-- The bump condition at stage `n`, phrased in terms of the stage function. -/
def bumpAt (n : ℕ) : Prop := M.bump (M.stage n) n M.stage

lemma stage_zero : M.stage 0 = 0 := rfl

lemma stage_succ (n : ℕ) :
    M.stage (n + 1) = if M.bumpAt n then M.stage n + 1 else M.stage n := by
  have hc : M.clamp n n = M.stage n := clamp_of_le M n n le_rfl
  have hb : M.bump (M.clamp n n) n (M.clamp n) ↔ M.bumpAt n := by
    rw [hc]
    exact bump_congr M (fun m hm => clamp_of_le M n m hm)
  show M.clamp (n + 1) (n + 1) = _
  rw [clamp, if_neg (by omega : ¬ (n + 1 ≤ n))]
  by_cases h : M.bumpAt n
  · rw [if_pos (hb.mpr h), if_pos h, hc]
  · rw [if_neg (fun hh => h (hb.mp hh)), if_neg h, hc]

lemma stage_le_succ (n : ℕ) : M.stage n ≤ M.stage (n + 1) := by
  rw [stage_succ]; split <;> omega

lemma stage_succ_le (n : ℕ) : M.stage (n + 1) ≤ M.stage n + 1 := by
  rw [stage_succ]; split <;> omega

lemma stage_mono : Monotone M.stage :=
  monotone_nat_of_le_succ (stage_le_succ M)

lemma bumpAt_of_lt {n : ℕ} (h : M.stage n < M.stage (n + 1)) : M.bumpAt n := by
  by_contra hb
  rw [stage_succ, if_neg hb] at h
  omega

end Machines

/-! ### The diagonalisation arguments -/

namespace Framework

variable (F : Framework)

lemma SAT_not_mem_P (h : F.P ≠ F.NP) : F.M.SAT ∉ F.P := by
  intro hs
  exact h (Set.Subset.antisymm F.P_sub_NP
    (fun L hL => F.P_red_closed L F.M.SAT (F.SAT_hard L hL) hs))

lemma ladnerLang_mem_NP : F.ladnerLang ∈ F.NP := F.holes_mem_NP

/-- Above `2 ^ N`, every string has length at least `N`. -/
private lemma size_ge_of_ge (N x : ℕ) (hx : 2 ^ N ≤ x) : N ≤ Nat.size x :=
  le_of_lt (Nat.lt_size.mpr hx)

/-- If the stage function is eventually constant with an **even** value then the
constructed language belongs to `P` and agrees with `SAT` almost everywhere, so
`SAT ∈ P`. -/
lemma stage_stab_even (N k : ℕ) (hk : Even k) (hN : ∀ n, N ≤ n → F.M.stage n = k)
    (hnb : ∀ n, N ≤ n → ¬ F.M.bumpAt n) : F.M.SAT ∈ F.P := by
  set i := k / 2 with hi
  have hLP : F.ladnerLang ∈ F.P := by
    rw [F.mem_P]
    refine ⟨i, fun x => ?_⟩
    obtain ⟨t, ht⟩ := F.haltsDec_ex i x
    set n := max (max N (2 ^ Nat.size x)) t with hn
    have hnN : N ≤ n := le_trans (le_max_left _ _) (le_max_left _ _)
    have hnx : 2 ^ Nat.size x ≤ n := le_trans (le_max_right _ _) (le_max_left _ _)
    have hnt : t ≤ n := le_max_right _ _
    have hxlog : Nat.size x ≤ Nat.log 2 n := by
      have h1 := Nat.log_mono_right (b := 2) hnx
      rwa [Nat.log_pow (by norm_num) (Nat.size x)] at h1
    have hhalt : F.M.haltsDec i x n = true := F.haltsDec_mono i x t n hnt ht
    have hb := hnb n hnN
    rw [Machines.bumpAt, hN n hnN, Machines.bump, if_pos hk] at hb
    push_neg at hb
    have hkey := hb x hxlog hhalt
    rw [F.decT_sound i x n hhalt] at hkey
    exact hkey
  refine F.P_finite_variant F.ladnerLang F.M.SAT (2 ^ N) hLP ?_
  intro x hx
  have hsz : N ≤ Nat.size x := size_ge_of_ge N x hx
  simp only [Framework.ladnerLang, Set.mem_setOf_eq, hN _ hsz]
  exact ⟨fun hh => hh.1, fun hh => ⟨hh, hk⟩⟩

/-- If the stage function is eventually constant with an **odd** value then the
constructed language is finite while `SAT` reduces to it, so `SAT ∈ P`. -/
lemma stage_stab_odd (N k : ℕ) (hk : ¬ Even k) (hN : ∀ n, N ≤ n → F.M.stage n = k)
    (hnb : ∀ n, N ≤ n → ¬ F.M.bumpAt n) : F.M.SAT ∈ F.P := by
  set i := k / 2 with hi
  have hred : ∀ x, x ∈ F.M.SAT ↔ F.M.red i x ∈ F.ladnerLang := by
    intro x
    obtain ⟨t, ht⟩ := F.redT_ex i x
    set n := max (max (max N (2 ^ Nat.size x)) t) (Nat.size (F.M.red i x)) with hn
    have hnN : N ≤ n :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
    have hnx : 2 ^ Nat.size x ≤ n :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
    have hnt : t ≤ n := le_trans (le_max_right _ _) (le_max_left _ _)
    have hny : Nat.size (F.M.red i x) ≤ n := le_max_right _ _
    have hxlog : Nat.size x ≤ Nat.log 2 n := by
      have h1 := Nat.log_mono_right (b := 2) hnx
      rwa [Nat.log_pow (by norm_num) (Nat.size x)] at h1
    have hconv : F.M.redT i x n = some (F.M.red i x) := F.redT_mono i x t n _ hnt ht
    have hb := hnb n hnN
    rw [Machines.bumpAt, hN n hnN, Machines.bump, if_neg hk] at hb
    push_neg at hb
    exact hb x hxlog (F.M.red i x) hny hconv
  have hLP : F.ladnerLang ∈ F.P := by
    refine F.P_finite_variant (∅ : Lang) F.ladnerLang (2 ^ N) F.empty_mem_P ?_
    intro x hx
    have hsz : N ≤ Nat.size x := size_ge_of_ge N x hx
    simp only [Set.mem_empty_iff_false, Framework.ladnerLang, Set.mem_setOf_eq,
      hN _ hsz, false_iff]
    exact fun hh => hk hh.2
  exact F.P_red_closed F.M.SAT F.ladnerLang ⟨i, hred⟩ hLP

/-- Assuming `P ≠ NP`, the stage function is unbounded. -/
lemma stage_unbounded (h : F.P ≠ F.NP) : ∀ k, ∃ n, k < F.M.stage n := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨k0, hk0⟩ := hcon
  have hex : ∃ k, ∀ n, F.M.stage n ≤ k := ⟨k0, hk0⟩
  set k := Nat.find hex with hkdef
  have hkb : ∀ n, F.M.stage n ≤ k := Nat.find_spec hex
  have hatt : ∃ N, F.M.stage N = k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exact ⟨0, by have := hkb 0; omega⟩
    · have hnot : ¬ (∀ n, F.M.stage n ≤ k - 1) := by
        intro hcc
        have : k ≤ k - 1 := Nat.find_le hcc
        omega
      push_neg at hnot
      obtain ⟨N, hN⟩ := hnot
      exact ⟨N, by have := hkb N; omega⟩
  obtain ⟨N, hN⟩ := hatt
  have hconst : ∀ n, N ≤ n → F.M.stage n = k := by
    intro n hn
    have h1 := Machines.stage_mono F.M hn
    have h2 := hkb n
    omega
  have hnb : ∀ n, N ≤ n → ¬ F.M.bumpAt n := by
    intro n hn hb
    have hs := Machines.stage_succ F.M n
    rw [if_pos hb] at hs
    have e1 := hconst n hn
    have e2 := hconst (n + 1) (by omega)
    omega
  have hSAT : F.M.SAT ∈ F.P := by
    by_cases hk : Even k
    · exact F.stage_stab_even N k hk hconst hnb
    · exact F.stage_stab_odd N k hk hconst hnb
  exact F.SAT_not_mem_P h hSAT

/-- Assuming `P ≠ NP`, every value `k` is taken by the stage function at a point
where the bump condition fires. -/
lemma stage_attains (h : F.P ≠ F.NP) (k : ℕ) :
    ∃ n, F.M.stage n = k ∧ F.M.bumpAt n := by
  obtain ⟨m, hm⟩ := F.stage_unbounded h k
  have hex : ∃ n, k < F.M.stage n := ⟨m, hm⟩
  set n0 := Nat.find hex with hn0
  have hspec : k < F.M.stage n0 := Nat.find_spec hex
  have hn0pos : n0 ≠ 0 := by
    intro h0
    rw [h0, Machines.stage_zero] at hspec
    omega
  obtain ⟨n, hn0eq⟩ : ∃ n, n0 = n + 1 := ⟨n0 - 1, by omega⟩
  rw [hn0eq] at hspec
  have hprev : ¬ (k < F.M.stage n) := Nat.find_min hex (by omega)
  have hle := Machines.stage_succ_le F.M n
  exact ⟨n, by omega, Machines.bumpAt_of_lt F.M (by omega)⟩

lemma ladnerLang_not_mem_P (h : F.P ≠ F.NP) : F.ladnerLang ∉ F.P := by
  intro hP
  rw [F.mem_P] at hP
  obtain ⟨i, hi⟩ := hP
  obtain ⟨n, hn, hb⟩ := F.stage_attains h (2 * i)
  rw [Machines.bumpAt, hn, Machines.bump, if_pos (even_two_mul i)] at hb
  simp only [Nat.mul_div_cancel_left i (by norm_num : 0 < 2)] at hb
  obtain ⟨x, _, hhalt, hne⟩ := hb
  rw [F.decT_sound i x n hhalt] at hne
  exact hne (hi x)

lemma SAT_not_reduces_ladnerLang (h : F.P ≠ F.NP) :
    ¬ F.Reduces F.M.SAT F.ladnerLang := by
  rintro ⟨i, hi⟩
  obtain ⟨n, hn, hb⟩ := F.stage_attains h (2 * i + 1)
  have hodd : ¬ Even (2 * i + 1) := by simp [parity_simps]
  rw [Machines.bumpAt, hn, Machines.bump, if_neg hodd] at hb
  have hdiv : (2 * i + 1) / 2 = i := by omega
  rw [hdiv] at hb
  obtain ⟨x, _, y, _, hconv, hne⟩ := hb
  have hyv : y = F.M.red i x := F.redT_sound i x n y hconv
  subst hyv
  exact hne (hi x)

lemma ladnerLang_not_NPComplete (h : F.P ≠ F.NP) : ¬ F.NPComplete F.ladnerLang := by
  rintro ⟨_, hhard⟩
  exact F.SAT_not_reduces_ladnerLang h (hhard F.M.SAT F.SAT_mem_NP)

end Framework

/-- **Ladner's theorem.**  In any framework satisfying the standard structural
facts about `P`, `NP` and polynomial-time many-one reductions, if `P ≠ NP` then
there is an `NP`-intermediate language: one that belongs to `NP`, does not
belong to `P`, and is not `NP`-complete. -/
theorem ladner (F : Framework) (h : F.P ≠ F.NP) : ∃ L : Lang, F.NPIntermediate L :=
  ⟨F.ladnerLang, F.ladnerLang_mem_NP, F.ladnerLang_not_mem_P h,
    F.ladnerLang_not_NPComplete h⟩

/-! ### Consistency of the framework axioms

The axioms bundled into `CS.Framework` are jointly satisfiable: we exhibit a
small model in which `P = NP` is the class of finite-or-cofinite languages.
This rules out the possibility that `CS.ladner` holds vacuously because its
hypotheses are contradictory.  (Of course Ladner's theorem says nothing about
*this* model, since `P = NP` there; the intended model is real complexity theory,
for which `P ≠ NP` is open.)
-/

namespace Model

/-- The finite-or-cofinite languages. -/
def FinCofin : Set Lang := {L | L.Finite ∨ Lᶜ.Finite}

/-- Decode a natural number as a finite set together with a sign. -/
def pairOf (i : ℕ) : Finset ℕ × Bool :=
  (Encodable.decode (α := Finset ℕ × Bool) i).getD (∅, true)

lemma pairOf_encode (p : Finset ℕ × Bool) : pairOf (Encodable.encode p) = p := by
  simp [pairOf]

/-- The `i`-th decider of the model. -/
def decFn (i x : ℕ) : Bool := decide (x ∈ (pairOf i).1) == (pairOf i).2

/-- The `i`-th reduction function of the model. -/
def redFn (i x : ℕ) : ℕ := if decFn i x then 0 else 1

/-- The machine data of the model. -/
def M : Machines where
  dec := decFn
  red := redFn
  decT := fun i x _ => decFn i x
  haltsDec := fun _ _ _ => true
  redT := fun i x _ => some (redFn i x)
  SAT := {0}

lemma decSet_mem (i : ℕ) : {x | decFn i x = true} ∈ FinCofin := by
  rcases hb : (pairOf i).2 with _ | _
  · right
    have : {x | decFn i x = true}ᶜ = ((pairOf i).1 : Set ℕ) := by
      ext x; simp [decFn, hb]
    rw [this]
    exact (pairOf i).1.finite_toSet
  · left
    have : {x | decFn i x = true} = ((pairOf i).1 : Set ℕ) := by
      ext x; simp [decFn, hb]
    rw [this]
    exact (pairOf i).1.finite_toSet

lemma mem_FinCofin_iff (L : Lang) :
    L ∈ FinCofin ↔ ∃ i, ∀ x, x ∈ L ↔ decFn i x = true := by
  constructor
  · rintro (hL | hL)
    · refine ⟨Encodable.encode (hL.toFinset, true), fun x => ?_⟩
      simp [decFn, pairOf_encode]
    · refine ⟨Encodable.encode (hL.toFinset, false), fun x => ?_⟩
      simp [decFn, pairOf_encode]
  · rintro ⟨i, hi⟩
    have : L = {x | decFn i x = true} := by ext x; simpa using hi x
    rw [this]; exact decSet_mem i

lemma FinCofin_compl {L : Lang} (h : L ∈ FinCofin) : Lᶜ ∈ FinCofin := by
  rcases h with h | h
  · exact Or.inr (by rwa [compl_compl])
  · exact Or.inl h

lemma FinCofin_variant (K L : Lang) (N : ℕ) (hK : K ∈ FinCofin)
    (h : ∀ x, N ≤ x → (x ∈ K ↔ x ∈ L)) : L ∈ FinCofin := by
  have hfin : (Set.Iio N).Finite := Set.finite_Iio N
  rcases hK with hK | hK
  · refine Or.inl (Set.Finite.subset (hK.union hfin) ?_)
    intro x hx
    rcases lt_or_ge x N with hlt | hge
    · exact Or.inr hlt
    · exact Or.inl ((h x hge).mpr hx)
  · refine Or.inr (Set.Finite.subset (hK.union hfin) ?_)
    intro x hx
    rcases lt_or_ge x N with hlt | hge
    · exact Or.inr hlt
    · exact Or.inl (fun hxK => hx ((h x hge).mp hxK))

lemma FinCofin_red (A B : Lang) (i : ℕ) (hA : ∀ x, x ∈ A ↔ redFn i x ∈ B)
    (hB : B ∈ FinCofin) : A ∈ FinCofin := by
  by_cases h0 : (0 : ℕ) ∈ B <;> by_cases h1 : (1 : ℕ) ∈ B
  · have : A = Set.univ := by
      ext x; simp only [Set.mem_univ, iff_true, hA x, redFn]
      split_ifs <;> assumption
    exact this ▸ Or.inr (by simp)
  · have : A = {x | decFn i x = true} := by
      ext x
      simp only [Set.mem_setOf_eq, hA x, redFn]
      by_cases hd : decFn i x = true <;> simp [hd, h0, h1]
    exact this ▸ decSet_mem i
  · have : A = {x | decFn i x = true}ᶜ := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, hA x, redFn]
      by_cases hd : decFn i x = true <;> simp [hd, h0, h1]
    exact this ▸ FinCofin_compl (decSet_mem i)
  · have : A = (∅ : Set ℕ) := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false, hA x, redFn]
      split_ifs <;> assumption
    exact this ▸ Or.inl (by simp)

lemma redFn_mem_SAT (i x : ℕ) : redFn i x ∈ ({0} : Lang) ↔ decFn i x = true := by
  simp only [redFn, Set.mem_singleton_iff]
  by_cases hd : decFn i x = true <;> simp [hd]

/-- A model of the framework axioms, showing they are consistent. -/
def framework : Framework where
  M := M
  P := FinCofin
  NP := FinCofin
  mem_P := mem_FinCofin_iff
  P_sub_NP := le_rfl
  empty_mem_P := Or.inl (by simp)
  P_finite_variant := FinCofin_variant
  P_red_closed := by
    rintro A B ⟨i, hi⟩ hB
    exact FinCofin_red A B i hi hB
  SAT_mem_NP := Or.inl (Set.finite_singleton 0)
  SAT_hard := by
    intro L hL
    obtain ⟨i, hi⟩ := (mem_FinCofin_iff L).mp hL
    exact ⟨i, fun x => (hi x).trans (redFn_mem_SAT i x).symm⟩
  decT_sound := by intro i x t _; rfl
  haltsDec_mono := by intro i x t t' _ _; rfl
  haltsDec_ex := fun i x => ⟨0, rfl⟩
  redT_sound := by
    intro i x t y hy
    exact (Option.some_inj.mp hy).symm
  redT_mono := by intro i x t t' y _ hy; exact hy
  redT_ex := fun i x => ⟨0, rfl⟩
  holes_mem_NP :=
    Or.inl (Set.Finite.subset (Set.finite_singleton 0) (fun x hx => hx.1))

end Model

/-- The axioms packaged in `CS.Framework` are consistent. -/
theorem framework_nonempty : Nonempty Framework := ⟨Model.framework⟩

end CS

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

