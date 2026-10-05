/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- The local (Euler) factor of the twin-prime singular series at `p`:
`1 - 1/(p-1)^2` at odd primes, and `1` at all other natural numbers. -/
noncomputable def singularFactor (p : ℕ) : ℝ :=
  if Nat.Prime p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1

/-- The `N`-th partial product of the twin-prime singular series,
`∏_{3 ≤ p ≤ N, p prime} (1 - 1/(p-1)^2)`. -/
noncomputable def singularPartial (N : ℕ) : ℝ :=
  ∏ p ∈ Finset.Ico 3 (N + 1), singularFactor p

/-- The size of the `p`-th correction term. -/
noncomputable def singularTerm (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1) ^ 2

lemma singularTerm_nonneg (p : ℕ) : 0 ≤ singularTerm p := by
  unfold singularTerm; positivity

lemma singularTerm_le_quarter {p : ℕ} (hp : 3 ≤ p) : singularTerm p ≤ 1 / 4 := by
  have h : (2 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  unfold singularTerm
  rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
  nlinarith

lemma one_sub_singularTerm_le_singularFactor {p : ℕ} (hp : 3 ≤ p) :
    1 - singularTerm p ≤ singularFactor p := by
  unfold singularFactor singularTerm
  split
  · exact le_rfl
  · have : (0:ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    linarith

lemma singularFactor_nonneg {p : ℕ} (hp : 3 ≤ p) : 0 ≤ singularFactor p := by
  have h1 := one_sub_singularTerm_le_singularFactor hp
  have h2 := singularTerm_le_quarter hp
  linarith

lemma singularFactor_le_one (p : ℕ) : singularFactor p ≤ 1 := by
  unfold singularFactor
  split
  · have : (0:ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    linarith
  · exact le_rfl

lemma singularPartial_nonneg (N : ℕ) : 0 ≤ singularPartial N := by
  unfold singularPartial
  refine Finset.prod_nonneg ?_
  intro p hp
  exact singularFactor_nonneg (Finset.mem_Ico.mp hp).1

lemma singularPartial_le_one (N : ℕ) : singularPartial N ≤ 1 := by
  unfold singularPartial
  refine Finset.prod_le_one ?_ ?_
  · intro p hp; exact singularFactor_nonneg (Finset.mem_Ico.mp hp).1
  · intro p _; exact singularFactor_le_one p

/-- Weierstrass-type inequality: `∏ (1 - f i) ≥ 1 - ∑ f i`. -/
lemma one_sub_sum_le_prod_one_sub (s : Finset ℕ) (f : ℕ → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      have hmem : ∀ i ∈ s, i ∈ Finset.cons a s ha := fun i hi => Finset.mem_cons_of_mem hi
      have h0' : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (hmem i hi)
      have h1' : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (hmem i hi)
      have ihs := ih h0' h1'
      have ha0 : 0 ≤ f a := h0 a (Finset.mem_cons_self a s)
      have ha1 : f a ≤ 1 := h1 a (Finset.mem_cons_self a s)
      have hsum0 : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg h0'
      rw [Finset.prod_cons, Finset.sum_cons]
      nlinarith [ihs, ha0, ha1, hsum0]

/-- Telescoping tail bound: `∑_{N < n ≤ M} 1/(n-1)^2 ≤ 1/(N-1) - 1/(M-1)`. -/
lemma sum_singularTerm_le {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    ∑ n ∈ Finset.Ico (N + 1) (M + 1), singularTerm n
      ≤ 1 / ((N : ℝ) - 1) - 1 / ((M : ℝ) - 1) := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
      have hM2 : (2 : ℝ) ≤ (M : ℝ) := by
        have : (2 : ℕ) ≤ M := le_trans hN hM
        exact_mod_cast this
      rw [Finset.sum_Ico_succ_top (by omega)]
      have hterm : singularTerm (M + 1) ≤ 1 / ((M : ℝ) - 1) - 1 / (((M : ℝ) + 1) - 1) := by
        unfold singularTerm
        have hcast : ((M + 1 : ℕ) : ℝ) - 1 = (M : ℝ) := by push_cast; ring
        rw [hcast]
        rw [div_sub_div _ _ (by linarith) (by linarith)]
        rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
        nlinarith
      have hcast2 : ((M + 1 : ℕ) : ℝ) - 1 = (M : ℝ) := by push_cast; ring
      rw [hcast2]
      have : (1 : ℝ) / (M : ℝ) = 1 / (((M : ℝ) + 1) - 1) := by ring_nf
      linarith [ih, hterm]

/-- Splitting the partial product at `N`. -/
lemma singularPartial_split {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    singularPartial M
      = singularPartial N * ∏ p ∈ Finset.Ico (N + 1) (M + 1), singularFactor p := by
  unfold singularPartial
  rw [Finset.prod_Ico_consecutive singularFactor (by omega : 3 ≤ N + 1) (by omega : N + 1 ≤ M + 1)]

lemma tailProd_nonneg (N M : ℕ) (hN : 2 ≤ N) :
    0 ≤ ∏ p ∈ Finset.Ico (N + 1) (M + 1), singularFactor p := by
  refine Finset.prod_nonneg ?_
  intro p hp
  exact singularFactor_nonneg (by have := (Finset.mem_Ico.mp hp).1; omega)

lemma tailProd_le_one (N M : ℕ) (hN : 2 ≤ N) :
    (∏ p ∈ Finset.Ico (N + 1) (M + 1), singularFactor p) ≤ 1 := by
  refine Finset.prod_le_one ?_ ?_
  · intro p hp
    exact singularFactor_nonneg (by have := (Finset.mem_Ico.mp hp).1; omega)
  · intro p _; exact singularFactor_le_one p

/-- The partial products are antitone. -/
lemma singularPartial_antitone : Antitone singularPartial := by
  intro N M hNM
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have : singularPartial N = 1 := by
      unfold singularPartial
      rw [Finset.Ico_eq_empty (by omega), Finset.prod_empty]
    rw [this]
    exact singularPartial_le_one M
  · rw [singularPartial_split hN hNM]
    nlinarith [singularPartial_nonneg N, singularPartial_le_one N,
      tailProd_nonneg N M hN, tailProd_le_one N M hN]

/-- Key effective estimate: later partial products cannot drop far below earlier ones. -/
lemma singularPartial_lower {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    singularPartial N - 1 / ((N : ℝ) - 1) ≤ singularPartial M := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hMr : (0 : ℝ) < (M : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (le_trans hN hNM)
    linarith
  set T : ℝ := ∏ p ∈ Finset.Ico (N + 1) (M + 1), singularFactor p with hT
  have hlow : 1 - ∑ n ∈ Finset.Ico (N + 1) (M + 1), singularTerm n ≤ T := by
    have hstep : (1 - ∑ n ∈ Finset.Ico (N + 1) (M + 1), singularTerm n)
        ≤ ∏ n ∈ Finset.Ico (N + 1) (M + 1), (1 - singularTerm n) := by
      refine one_sub_sum_le_prod_one_sub _ _ (fun i _ => singularTerm_nonneg i) ?_
      intro i hi
      have : 3 ≤ i := by have := (Finset.mem_Ico.mp hi).1; omega
      linarith [singularTerm_le_quarter this]
    refine le_trans hstep ?_
    refine Finset.prod_le_prod ?_ ?_
    · intro i hi
      have : 3 ≤ i := by have := (Finset.mem_Ico.mp hi).1; omega
      linarith [singularTerm_le_quarter this]
    · intro i hi
      exact one_sub_singularTerm_le_singularFactor (by have := (Finset.mem_Ico.mp hi).1; omega)
  have hsum : ∑ n ∈ Finset.Ico (N + 1) (M + 1), singularTerm n ≤ 1 / ((N : ℝ) - 1) := by
    have h := sum_singularTerm_le (by omega : 2 ≤ N) hNM
    have : (0:ℝ) ≤ 1 / ((M : ℝ) - 1) := by positivity
    linarith
  have hPN0 := singularPartial_nonneg N
  have hPN1 := singularPartial_le_one N
  have hsum0 : 0 ≤ ∑ n ∈ Finset.Ico (N + 1) (M + 1), singularTerm n :=
    Finset.sum_nonneg (fun i _ => singularTerm_nonneg i)
  rw [singularPartial_split (by omega : 2 ≤ N) hNM, ← hT]
  nlinarith [hlow, hsum, hPN0, hPN1, hsum0]

/-- **Singular series convergence rate.**  The partial products of the twin-prime
singular series converge to a positive limit `S`, with the effective rate
`|singularPartial N - S| ≤ 2 / N`. -/
theorem SingularSeriesConvergenceRate :
    ∃ S : ℝ, 0 < S ∧ Filter.Tendsto singularPartial Filter.atTop (nhds S) ∧
      ∀ N : ℕ, 3 ≤ N → |singularPartial N - S| ≤ 2 / (N : ℝ) := by
  have hbdd : BddBelow (Set.range singularPartial) := by
    refine ⟨0, ?_⟩
    rintro x ⟨N, rfl⟩
    exact singularPartial_nonneg N
  refine ⟨⨅ N, singularPartial N, ?_, ?_, ?_⟩
  · -- positivity of the limit
    have key : ∀ M : ℕ, (1 : ℝ) / 4 ≤ singularPartial M := by
      intro M
      rcases Nat.lt_or_ge M 3 with hM | hM
      · have : (1 : ℝ) / 4 ≤ singularPartial 3 := by
          unfold singularPartial singularFactor
          norm_num [Finset.prod_Ico_succ_top, Nat.prime_three]
        exact le_trans this (singularPartial_antitone (by omega : M ≤ 3))
      · have h := singularPartial_lower (le_refl 3) hM
        have h3 : singularPartial 3 = 3 / 4 := by
          unfold singularPartial singularFactor
          norm_num [Nat.prime_three]
        rw [h3] at h
        norm_num at h
        linarith
    have : (1 : ℝ) / 4 ≤ ⨅ N, singularPartial N := le_ciInf key
    linarith
  · exact tendsto_atTop_ciInf singularPartial_antitone hbdd
  · intro N hN
    have hNr : (2 : ℝ) ≤ (N : ℝ) - 1 := by
      have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hupper : (⨅ M, singularPartial M) ≤ singularPartial N := ciInf_le hbdd N
    have hlower : singularPartial N - 1 / ((N : ℝ) - 1) ≤ ⨅ M, singularPartial M := by
      refine le_ciInf ?_
      intro M
      rcases le_or_gt N M with h | h
      · exact singularPartial_lower hN h
      · have := singularPartial_antitone (le_of_lt h)
        have hpos : (0:ℝ) ≤ 1 / ((N : ℝ) - 1) := by positivity
        linarith
    rw [abs_le]
    have hN0 : (0:ℝ) < (N:ℝ) := by linarith
    have hrate : 1 / ((N : ℝ) - 1) ≤ 2 / (N : ℝ) := by
      rw [div_le_div_iff₀ (by linarith) hN0]
      linarith
    constructor <;> [linarith [hupper, hlower, hrate]; linarith [hupper, hlower, hrate]]

end Brockian

