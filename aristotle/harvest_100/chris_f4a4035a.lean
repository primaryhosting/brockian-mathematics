import Mathlib
/-!
# Bolzano Weierstrass
Category: Pure Mathematics
Target: Math.bolzano_weierstrass
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Bolzano–Weierstrass theorem.**  Every bounded sequence in `ℝ^n` has a convergent
subsequence: if `x : ℕ → EuclideanSpace ℝ (Fin n)` satisfies `‖x k‖ ≤ C` for all `k`, then
there is a strictly monotone index map `φ : ℕ → ℕ` and a point `a` such that the subsequence
`x ∘ φ` converges to `a`. -/
theorem bolzano_weierstrass {n : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin n)) (C : ℝ)
    (hC : ∀ k, ‖x k‖ ≤ C) :
    ∃ (a : EuclideanSpace ℝ (Fin n)) (φ : ℕ → ℕ),
      StrictMono φ ∧ Filter.Tendsto (x ∘ φ) Filter.atTop (nhds a) := by
  have hb : Bornology.IsBounded (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) C) :=
    Metric.isBounded_closedBall
  have hmem : ∀ k, x k ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) C := by
    intro k
    simpa [Metric.mem_closedBall, dist_eq_norm] using hC k
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hb hmem
  exact ⟨a, φ, hφ, hlim⟩

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

