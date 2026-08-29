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

theorem countingSet_finite (t : ℝ) : (countingSet C t).Finite := by
  obtain ⟨M, hM⟩ := (C.diverges.eventually_gt_atTop t).exists_forall_of_atTop
  refine Set.Finite.subset (Set.finite_Iio M) ?_
  intro n hn
  by_contra hlt
  exact absurd hn (not_le.mpr (hM n (not_lt.mp hlt)))

/-- If the `K`-th candidate eigenvalue is at most `t`, then the counting function
at `t` is at least `K + 1`. -/
