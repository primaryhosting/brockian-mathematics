/-
# Bolzano Weierstrass
Category: Pure Mathematics
Target: Math.bolzano_weierstrass
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Topology Metric Bornology

namespace Math

/-- **Bolzano–Weierstrass**: every bounded sequence in `ℝ^n` has a convergent subsequence. -/
theorem bolzano_weierstrass {n : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin n)) (C : ℝ)
    (hu : ∀ k, ‖u k‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (L : EuclideanSpace ℝ (Fin n)),
      StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 L) := by
  have hs : IsBounded (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) C) :=
    Metric.isBounded_closedBall
  have hmem : ∀ k, u k ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) C := by
    intro k
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu k
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hs hmem
  exact ⟨φ, a, hφ, hlim⟩

end Math

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

