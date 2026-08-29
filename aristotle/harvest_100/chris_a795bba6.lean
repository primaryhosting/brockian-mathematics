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

import Mathlib

/-!
# Counting Diverges Of Candidate
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_candidate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology

namespace Brockian.Weyl.WeylLawTarget

/-- A *spectral candidate* is a candidate eigenvalue list for a Weyl-law problem:
a nondecreasing sequence of real eigenvalues (listed with multiplicity) that
diverges to `+∞`. -/
structure SpectralCandidate where
  /-- The candidate eigenvalues, listed with multiplicity in nondecreasing order. -/
  lam : ℕ → ℝ
  /-- The eigenvalue list is nondecreasing. -/
  mono : Monotone lam
  /-- The eigenvalue list diverges to `+∞`. -/
  diverges : Filter.Tendsto lam Filter.atTop Filter.atTop

variable (C : SpectralCandidate)

/-- The set of indices whose candidate eigenvalue is at most `t`. -/
def countingSet (t : ℝ) : Set ℕ := {n : ℕ | C.lam n ≤ t}

/-- The Weyl counting function of a candidate: the number of eigenvalues
(with multiplicity) that are at most `t`. -/
noncomputable def counting (t : ℝ) : ℕ := (countingSet C t).ncard

/-- The counting set of a candidate is finite at every level `t`, since the
eigenvalues diverge. -/
theorem countingSet_finite (t : ℝ) : (countingSet C t).Finite := by
  obtain ⟨M, hM⟩ := (C.diverges.eventually_gt_atTop t).exists_forall_of_atTop
  refine Set.Finite.subset (Set.finite_Iio M) ?_
  intro n hn
  by_contra hlt
  exact absurd hn (not_le.mpr (hM n (not_lt.mp hlt)))

/-- If the `K`-th candidate eigenvalue is at most `t`, then the counting function
at `t` is at least `K + 1`. -/
theorem succ_le_counting (K : ℕ) (t : ℝ) (h : C.lam K ≤ t) :
    K + 1 ≤ counting C t := by
  have hsub : (↑(Finset.range (K + 1)) : Set ℕ) ⊆ countingSet C t := by
    intro n hn
    simp only [Finset.coe_range, Set.mem_Iio] at hn
    exact le_trans (C.mono (Nat.lt_succ_iff.mp hn)) h
  have := Set.ncard_le_ncard hsub (countingSet_finite C t)
  simpa [Set.ncard_coe_Finset, counting] using this

/-- **Discharged hypothesis.** For any spectral candidate, the Weyl counting
function diverges to `+∞`. -/
theorem counting_diverges_of_candidate :
    Filter.Tendsto (fun t : ℝ => (counting C t : ℝ)) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.mpr fun b => ?_
  set K : ℕ := ⌈b⌉₊ with hK
  filter_upwards [Filter.eventually_ge_atTop (C.lam K)] with t ht
  have h1 : K + 1 ≤ counting C t := succ_le_counting C K t ht
  have h2 : (b : ℝ) ≤ (K : ℝ) := Nat.le_ceil b
  have h3 : ((K : ℝ)) ≤ (counting C t : ℝ) := by
    exact_mod_cast le_trans (Nat.le_succ K) h1
  linarith

end Brockian.Weyl.WeylLawTarget

