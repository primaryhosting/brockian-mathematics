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
