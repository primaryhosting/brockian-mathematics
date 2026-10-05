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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.Weyl.WeylLawTarget

open Filter Set

/-- A *candidate spectrum* for a Weyl law: a nondecreasing sequence of real
"eigenvalues" that tends to `+∞`. -/
structure Candidate where
  /-- The eigenvalue sequence. -/
  lam : ℕ → ℝ
  /-- The eigenvalues are listed in nondecreasing order. -/
  mono : Monotone lam
  /-- The eigenvalues tend to `+∞` (discreteness of the spectrum). -/
  tendsto_atTop : Filter.Tendsto lam Filter.atTop Filter.atTop

/-- The eigenvalue counting function `N(t) = #{n : λ n ≤ t}` of a candidate spectrum. -/
noncomputable def counting (C : Candidate) (t : ℝ) : ℕ := {n : ℕ | C.lam n ≤ t}.ncard

/-- For a candidate spectrum, each sublevel set of indices is finite. -/
theorem finite_sublevel (C : Candidate) (t : ℝ) : {n : ℕ | C.lam n ≤ t}.Finite := by
  obtain ⟨N, hN⟩ := (C.tendsto_atTop.eventually_gt_atTop t).exists_forall_of_atTop
  refine Set.Finite.subset (Set.finite_Iio N) ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_Iio]
  by_contra hcon
  exact absurd hn (not_le.mpr (hN n (not_lt.mp hcon)))

/-- The counting function is at least `m + 1` once `t` reaches `λ m`. -/
theorem le_counting (C : Candidate) (m : ℕ) {t : ℝ} (ht : C.lam m ≤ t) :
    m + 1 ≤ counting C t := by
  have hsub : (↑(Finset.range (m + 1)) : Set ℕ) ⊆ {n : ℕ | C.lam n ≤ t} := by
    intro n hn
    simp only [Finset.coe_range, Set.mem_Iio] at hn
    exact le_trans (C.mono (Nat.lt_succ_iff.mp hn)) ht
  have := Set.ncard_le_ncard hsub (finite_sublevel C t)
  simpa [Set.ncard_coe_Finset] using this

/-- **Weyl-law counting divergence.**  For any candidate spectrum (a nondecreasing
sequence of eigenvalues tending to `+∞`), the eigenvalue counting function
`N(t) = #{n : λ n ≤ t}` tends to `+∞` as `t → ∞`.  This discharges, unconditionally,
the hypothesis that the counting function diverges. -/
theorem counting_diverges_of_candidate (C : Candidate) :
    Filter.Tendsto (fun t : ℝ => counting C t) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun m => ?_
  filter_upwards [Filter.eventually_ge_atTop (C.lam m)] with t ht
  exact le_trans (Nat.le_succ m) (le_counting C m ht)

end Brockian.Weyl.WeylLawTarget

