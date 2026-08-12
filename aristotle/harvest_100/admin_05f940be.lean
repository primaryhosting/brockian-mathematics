/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A `±1`-sequence: a function `f : ℕ → ℤ` all of whose values on positive integers
are `1` or `-1`. -/
def IsPlusMinusOne (f : ℕ → ℤ) : Prop := ∀ n : ℕ, 1 ≤ n → f n = 1 ∨ f n = -1

/-- The signed sum of a `±1`-sequence `f` along the homogeneous arithmetic progression
of common difference `d` and length `n`, i.e. `f d + f (2d) + ⋯ + f (nd)`. -/
def apSum (f : ℕ → ℤ) (d n : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, f (i * d)

/-- **The Erdős discrepancy problem** (theorem of Tao, 2016), as a `Prop`:
every `±1`-sequence has unbounded discrepancy along homogeneous arithmetic
progressions. -/
def ErdosDiscrepancyStatement : Prop :=
  ∀ f : ℕ → ℤ, IsPlusMinusOne f → ∀ C : ℕ,
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ (C : ℤ) < |apSum f d n|

/-- The **finitary form** of the Erdős discrepancy problem: for every `C` there is a
uniform bound `N` such that every `±1`-sequence already has discrepancy exceeding `C`
along a homogeneous arithmetic progression contained in `{1, …, N}`. -/
def FinitaryErdosDiscrepancyStatement : Prop :=
  ∀ C : ℕ, ∃ N : ℕ, ∀ f : ℕ → ℤ, IsPlusMinusOne f →
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ d * n ≤ N ∧ (C : ℤ) < |apSum f d n|

/-- If `a` and `b` are `±1` and `|a + b| ≤ 1`, then `b = -a`. -/
private lemma neg_of_abs_add_le_one {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (h : |a + b| ≤ 1) : b = -a := by
  rw [abs_le] at h
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> subst ha <;> subst hb <;> omega

/-- **Base case of the Erdős discrepancy problem (`C = 1`).**
For every `±1`-sequence `f` there are a common difference `d ≥ 1` and a length `n ≥ 1`
such that the discrepancy `|f d + f (2d) + ⋯ + f (nd)|` is at least `2`.

Moreover the progression can be taken inside `{1, …, 12}` (i.e. `d * n ≤ 12`), which is
optimal: see `Frontier.exists_discrepancy_le_one_up_to_eleven`. This is the `C = 1`
instance of `Frontier.ErdosDiscrepancyStatement`. -/
theorem erdos_discrepancy (f : ℕ → ℤ) (hf : IsPlusMinusOne f) :
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ d * n ≤ 12 ∧ 2 ≤ |apSum f d n| := by
  by_contra hcon
  push_neg at hcon
  -- `h d n` : the discrepancy along every homogeneous AP inside `{1, …, 12}` is at most `1`.
  have h : ∀ d n : ℕ, 0 < d → 0 < n → d * n ≤ 12 → |apSum f d n| ≤ 1 := by
    intro d n hd hn hdn
    have := hcon d n hd hn hdn
    omega
  have v : ∀ n : ℕ, 1 ≤ n → f n = 1 ∨ f n = -1 := hf
  -- expansions of the relevant progression sums
  have s12 : apSum f 1 2 = f 1 + f 2 := by
    simp [apSum, Finset.sum_Icc_succ_top]
  have s14 : apSum f 1 4 = f 1 + f 2 + f 3 + f 4 := by
    simp [apSum, Finset.sum_Icc_succ_top]
  have s16 : apSum f 1 6 = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
    simp [apSum, Finset.sum_Icc_succ_top]
  have s18 : apSum f 1 8 = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
    simp [apSum, Finset.sum_Icc_succ_top]
  have s110 : apSum f 1 10 = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by
    simp [apSum, Finset.sum_Icc_succ_top]
  have s112 : apSum f 1 12
      = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 := by
    simp [apSum, Finset.sum_Icc_succ_top]
  have s22 : apSum f 2 2 = f 2 + f 4 := by
    simp [apSum, Finset.sum_Icc_succ_top]
  have s24 : apSum f 2 4 = f 2 + f 4 + f 6 + f 8 := by
    simp [apSum, Finset.sum_Icc_succ_top]
  have s26 : apSum f 2 6 = f 2 + f 4 + f 6 + f 8 + f 10 + f 12 := by
    simp [apSum, Finset.sum_Icc_succ_top]
  have s42 : apSum f 4 2 = f 4 + f 8 := by
    simp [apSum, Finset.sum_Icc_succ_top]
  have s34 : apSum f 3 4 = f 3 + f 6 + f 9 + f 12 := by
    simp [apSum, Finset.sum_Icc_succ_top]
  -- step 1: `f 2 = -f 1`
  have e12 : |f 1 + f 2| ≤ 1 := by rw [← s12]; exact h 1 2 one_pos two_pos (by norm_num)
  have h2 : f 2 = -f 1 := neg_of_abs_add_le_one (v 1 (by norm_num)) (v 2 (by norm_num)) e12
  -- step 2: `f 4 = -f 3`
  have e14 : |f 1 + f 2 + f 3 + f 4| ≤ 1 := by
    rw [← s14]; exact h 1 4 one_pos (by norm_num) (by norm_num)
  have h4 : f 4 = -f 3 := by
    refine neg_of_abs_add_le_one (v 3 (by norm_num)) (v 4 (by norm_num)) ?_
    have e : f 1 + f 2 + f 3 + f 4 = f 3 + f 4 := by rw [h2]; ring
    rwa [e] at e14
  -- step 3: `f 4 = f 1` and hence `f 3 = -f 1`
  have e22 : |f 2 + f 4| ≤ 1 := by rw [← s22]; exact h 2 2 two_pos two_pos (by norm_num)
  have h4' : f 4 = f 1 := by
    have := neg_of_abs_add_le_one (v 2 (by norm_num)) (v 4 (by norm_num)) e22
    rw [this, h2, neg_neg]
  have h3 : f 3 = -f 1 := by rw [← h4', h4, neg_neg]
  -- step 4: `f 6 = -f 5` and `f 8 = -f 7`
  have e16 : |f 1 + f 2 + f 3 + f 4 + f 5 + f 6| ≤ 1 := by
    rw [← s16]; exact h 1 6 one_pos (by norm_num) (by norm_num)
  have h6 : f 6 = -f 5 := by
    refine neg_of_abs_add_le_one (v 5 (by norm_num)) (v 6 (by norm_num)) ?_
    have e : f 1 + f 2 + f 3 + f 4 + f 5 + f 6 = f 5 + f 6 := by rw [h2, h3, h4']; ring
    rwa [e] at e16
  have e18 : |f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8| ≤ 1 := by
    rw [← s18]; exact h 1 8 one_pos (by norm_num) (by norm_num)
  have h8 : f 8 = -f 7 := by
    refine neg_of_abs_add_le_one (v 7 (by norm_num)) (v 8 (by norm_num)) ?_
    have e : f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 = f 7 + f 8 := by
      rw [h2, h3, h4', h6]; ring
    rwa [e] at e18
  -- step 5: `f 8 = -f 1` and `f 6 = f 1`
  have e42 : |f 4 + f 8| ≤ 1 := by rw [← s42]; exact h 4 2 (by norm_num) two_pos (by norm_num)
  have h8' : f 8 = -f 1 := by
    have := neg_of_abs_add_le_one (v 4 (by norm_num)) (v 8 (by norm_num)) e42
    rw [this, h4']
  have e24 : |f 2 + f 4 + f 6 + f 8| ≤ 1 := by
    rw [← s24]; exact h 2 4 two_pos (by norm_num) (by norm_num)
  have h6' : f 6 = f 1 := by
    have hb : |f 6 + f 8| ≤ 1 := by
      have e : f 2 + f 4 + f 6 + f 8 = f 6 + f 8 := by rw [h2, h4']; ring
      rwa [e] at e24
    have := neg_of_abs_add_le_one (v 6 (by norm_num)) (v 8 (by norm_num)) hb
    rw [h8'] at this
    omega
  -- step 6: `f 10 = -f 9`, `f 12 = -f 11`, and finally `f 12 = f 9`
  have e110 : |f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10| ≤ 1 := by
    rw [← s110]; exact h 1 10 one_pos (by norm_num) (by norm_num)
  have h10 : f 10 = -f 9 := by
    refine neg_of_abs_add_le_one (v 9 (by norm_num)) (v 10 (by norm_num)) ?_
    have e : f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 = f 9 + f 10 := by
      rw [h2, h3, h4', h6, h8]; ring
    rwa [e] at e110
  have e112 : |f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12| ≤ 1 := by
    rw [← s112]; exact h 1 12 one_pos (by norm_num) (by norm_num)
  have h12 : f 12 = -f 11 := by
    refine neg_of_abs_add_le_one (v 11 (by norm_num)) (v 12 (by norm_num)) ?_
    have e : f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12
        = f 11 + f 12 := by rw [h2, h3, h4', h6, h8, h10]; ring
    rwa [e] at e112
  have e26 : |f 2 + f 4 + f 6 + f 8 + f 10 + f 12| ≤ 1 := by
    rw [← s26]; exact h 2 6 two_pos (by norm_num) (by norm_num)
  have h12' : f 12 = f 9 := by
    have hb : |f 10 + f 12| ≤ 1 := by
      have e : f 2 + f 4 + f 6 + f 8 + f 10 + f 12 = f 10 + f 12 := by
        rw [h2, h4', h6', h8']; ring
      rwa [e] at e26
    have := neg_of_abs_add_le_one (v 10 (by norm_num)) (v 12 (by norm_num)) hb
    rw [this, h10, neg_neg]
  -- the contradiction, coming from the progression `3, 6, 9, 12`
  have e34 : |f 3 + f 6 + f 9 + f 12| ≤ 1 := by
    rw [← s34]; exact h 3 4 (by norm_num) (by norm_num) (by norm_num)
  have e : f 3 + f 6 + f 9 + f 12 = 2 * f 9 := by rw [h3, h6', h12']; ring
  rw [e] at e34
  rcases v 9 (by norm_num) with h9 | h9 <;> rw [h9] at e34 <;> norm_num at e34

/-- An explicit `±1`-sequence witnessing that `12` terms are needed in
`Frontier.erdos_discrepancy`: it is given by `+,-,-,+,-,+,+,-,-,+,+` on `1, …, 11`
(and by `+` afterwards). -/
def extremalEleven : ℕ → ℤ := fun n => [0, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1].getD n 1

private lemma extremalEleven_bound_aux :
    ∀ d ∈ Finset.Icc 1 11, ∀ n ∈ Finset.Icc 1 11, d * n ≤ 11 →
      |apSum extremalEleven d n| ≤ 1 := by
  decide

/-- **Optimality of the base case.** There is a `±1`-sequence all of whose homogeneous
arithmetic progressions inside `{1, …, 11}` have sum of absolute value at most `1`.
Hence `Frontier.erdos_discrepancy` cannot be witnessed using fewer than `12` terms. -/
theorem exists_discrepancy_le_one_up_to_eleven :
    ∃ f : ℕ → ℤ, IsPlusMinusOne f ∧
      ∀ d n : ℕ, 0 < d → 0 < n → d * n ≤ 11 → |apSum f d n| ≤ 1 := by
  refine ⟨extremalEleven, ?_, ?_⟩
  · intro n hn
    by_cases h : n ≤ 11
    · interval_cases n <;> simp [extremalEleven]
    · exact Or.inl (by simp [extremalEleven, List.getD, show 12 ≤ n by omega])
  · intro d n hd hn hdn
    have hd11 : d ≤ 11 := le_trans (Nat.le_mul_of_pos_right d hn) hdn
    have hn11 : n ≤ 11 := le_trans (Nat.le_mul_of_pos_left n hd) hdn
    exact extremalEleven_bound_aux d (Finset.mem_Icc.mpr ⟨hd, hd11⟩) n
      (Finset.mem_Icc.mpr ⟨hn, hn11⟩) hdn

/-- The base case proved above is exactly the `C = 1` instance of the full Erdős
discrepancy statement `Frontier.ErdosDiscrepancyStatement`. -/
theorem erdos_discrepancy_C_one (f : ℕ → ℤ) (hf : IsPlusMinusOne f) :
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ ((1 : ℕ) : ℤ) < |apSum f d n| := by
  obtain ⟨d, n, hd, hn, -, hs⟩ := erdos_discrepancy f hf
  exact ⟨d, n, hd, hn, by push_cast; omega⟩

/-- The `C = 1` instance of the finitary statement holds with the (optimal) bound
`N = 12`. -/
theorem finitary_erdos_discrepancy_C_one (f : ℕ → ℤ) (hf : IsPlusMinusOne f) :
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ d * n ≤ 12 ∧ ((1 : ℕ) : ℤ) < |apSum f d n| := by
  obtain ⟨d, n, hd, hn, hdn, hs⟩ := erdos_discrepancy f hf
  exact ⟨d, n, hd, hn, hdn, by push_cast; omega⟩

open Filter in
/-- **A Lean-checked reduction: the Erdős discrepancy statement is equivalent to its
finitary form.** The nontrivial direction is a compactness argument: from a sequence of
counterexamples on longer and longer initial segments one extracts, along a nonprincipal
ultrafilter, a single `±1`-sequence of bounded discrepancy. -/
theorem erdosDiscrepancyStatement_iff_finitary :
    ErdosDiscrepancyStatement ↔ FinitaryErdosDiscrepancyStatement := by
  constructor
  · -- infinite ⟹ finitary, by compactness
    intro H
    by_contra hc
    unfold FinitaryErdosDiscrepancyStatement at hc
    push_neg at hc
    obtain ⟨C, hC⟩ := hc
    choose F hF1 hF2 using hC
    classical
    set U : Filter ℕ := (hyperfilter ℕ : Filter ℕ) with hU
    -- the ultrafilter limit of the counterexamples
    set g : ℕ → ℤ := fun i => if (∀ᶠ N in U, F N i = 1) then 1 else -1 with hg
    have hgpm : IsPlusMinusOne g := by
      intro n _
      by_cases h : (∀ᶠ N in U, F N n = 1) <;> simp [hg, h]
    have key : ∀ i, 1 ≤ i → ∀ᶠ N in U, F N i = g i := by
      intro i hi
      by_cases hcase : (∀ᶠ N in U, F N i = 1)
      · simp [hg, hcase]
      · have h1 : ∀ᶠ N in U, F N i ≠ 1 := Ultrafilter.eventually_not.mpr hcase
        have h2 : ∀ᶠ N in U, F N i = -1 := h1.mono fun N hN => ((hF1 N) i hi).resolve_left hN
        simpa [hg, hcase] using h2
    have hle : U ≤ atTop := by rw [hU, ← Nat.cofinite_eq_atTop]; exact hyperfilter_le_cofinite
    have bound : ∀ d n : ℕ, 0 < d → 0 < n → |apSum g d n| ≤ (C : ℤ) := by
      intro d n hd hn
      have hall : ∀ᶠ N in U, ∀ i ∈ Finset.Icc 1 n, F N (i * d) = g (i * d) :=
        (eventually_all_finset _).mpr (by
          intro i hi
          rw [Finset.mem_Icc] at hi
          exact key (i * d) (Nat.mul_pos hi.1 hd))
      have hbig : ∀ᶠ N in U, d * n ≤ N := hle (eventually_ge_atTop (d * n))
      have hev : ∀ᶠ N in U, |apSum g d n| ≤ (C : ℤ) := by
        filter_upwards [hall, hbig] with N h1 h2
        have he : apSum g d n = apSum (F N) d n :=
          Finset.sum_congr rfl fun i hi => (h1 i hi).symm
        rw [he]
        exact hF2 N d n hd hn h2
      obtain ⟨_, h⟩ := hev.exists
      exact h
    obtain ⟨d, n, hd, hn, hlt⟩ := H g hgpm C
    exact absurd (bound d n hd hn) (not_le.mpr hlt)
  · -- finitary ⟹ infinite
    intro H f hf C
    obtain ⟨N, hN⟩ := H C
    obtain ⟨d, n, hd, hn, -, hlt⟩ := hN f hf
    exact ⟨d, n, hd, hn, hlt⟩

end Frontier

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

