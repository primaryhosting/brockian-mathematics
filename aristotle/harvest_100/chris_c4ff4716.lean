/-
# Bolzano Weierstrass
Category: Pure Mathematics
Target: Math.bolzano_weierstrass
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bolzano Weierstrass
Category: Pure Mathematics
Target: Math.bolzano_weierstrass
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Bolzano–Weierstrass** in `ℝ^n`: every bounded sequence in `EuclideanSpace ℝ (Fin n)`
admits a subsequence converging to some point.

The proof uses `tendsto_subseq_of_bounded` from Mathlib (Euclidean space is a proper
metric space, so bounded sets have compact closure). -/
theorem bolzano_weierstrass {n : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin n)) (C : ℝ)
    (hC : ∀ k, ‖u k‖ ≤ C) :
    ∃ a : EuclideanSpace ℝ (Fin n), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Filter.Tendsto (u ∘ φ) Filter.atTop (nhds a) := by
  have hb : Bornology.IsBounded (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) C) :=
    Metric.isBounded_closedBall
  have hmem : ∀ k, u k ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) C := by
    intro k
    simpa [Metric.mem_closedBall, dist_eq_norm] using hC k
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hb hmem
  exact ⟨a, φ, hφ, hlim⟩

end Math

#print axioms Math.bolzano_weierstrass

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

