import Brockian.Weyl.WeylLawTarget

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

/-
# Counting Diverges Of Candidate
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_candidate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Counting Diverges Of Candidate
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_candidate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set

namespace Brockian.Weyl.WeylLawTarget

/-- A *candidate spectrum* for a Weyl law: a nondecreasing sequence of real
"eigenvalues" which tends to `+∞`. -/
structure CandidateSpectrum where
  /-- The candidate eigenvalues, listed in nondecreasing order. -/
  lam : ℕ → ℝ
  /-- The eigenvalue list is nondecreasing. -/
  mono : Monotone lam
  /-- The eigenvalue list is unbounded above. -/
  tendsto_atTop : Filter.Tendsto lam Filter.atTop Filter.atTop

/-- The eigenvalue counting function `N(t) = #{n | λₙ ≤ t}`. -/
noncomputable def counting (c : CandidateSpectrum) (t : ℝ) : ℕ :=
  Nat.card {n : ℕ | c.lam n ≤ t}

/-- Since the candidate eigenvalues tend to `+∞`, only finitely many of them lie
below any given threshold. -/
theorem finite_setOf_lam_le (c : CandidateSpectrum) (t : ℝ) :
    {n : ℕ | c.lam n ≤ t}.Finite := by
  have h := Filter.tendsto_atTop.mp c.tendsto_atTop (t + 1)
  rw [Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  refine Set.Finite.subset (Set.finite_Iio N) ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_Iio]
  by_contra hcon
  have hle : N ≤ n := not_lt.mp hcon
  have := hN n hle
  linarith

/-- If the `k`-th candidate eigenvalue is at most `t`, then the counting function at
`t` is at least `k + 1`. -/
theorem succ_le_counting (c : CandidateSpectrum) (k : ℕ) {t : ℝ} (h : c.lam k ≤ t) :
    k + 1 ≤ counting c t := by
  have hsub : (↑(Finset.range (k + 1)) : Set ℕ) ⊆ {n : ℕ | c.lam n ≤ t} := by
    intro n hn
    simp only [Finset.coe_range, Set.mem_Iio] at hn
    exact le_trans (c.mono (Nat.lt_succ_iff.mp hn)) h
  have hcard := Set.ncard_le_ncard hsub (finite_setOf_lam_le c t)
  rwa [Set.ncard_coe_finset, Finset.card_range] at hcard

/-- **Weyl-law counting divergence.**  For any candidate spectrum (a nondecreasing,
unbounded list of eigenvalues) the counting function `N(t) = #{n | λₙ ≤ t}` tends to
`+∞` as `t → +∞`.  This discharges, unconditionally, the hypothesis that the counting
function of a candidate spectrum diverges. -/
theorem counting_diverges_of_candidate (c : CandidateSpectrum) :
    Filter.Tendsto (counting c) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨c.lam b, fun t ht => ?_⟩
  exact le_trans (Nat.le_succ b) (succ_le_counting c b ht)

end Brockian.Weyl.WeylLawTarget

