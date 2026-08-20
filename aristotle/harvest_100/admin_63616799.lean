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

/-!
# Bolzano Weierstrass
Category: Pure Mathematics
Target: Math.bolzano_weierstrass
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Bolzano–Weierstrass** in `ℝ^n`: every bounded sequence in `EuclideanSpace ℝ (Fin n)`
has a subsequence converging to some point.  The proof is a direct application of Mathlib's
`tendsto_subseq_of_bounded`, which holds in any proper metric space. -/
theorem bolzano_weierstrass (n : ℕ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (C : ℝ)
    (hC : ∀ k, ‖x k‖ ≤ C) :
    ∃ a : EuclideanSpace ℝ (Fin n), ∃ g : ℕ → ℕ, StrictMono g ∧
      Filter.Tendsto (x ∘ g) Filter.atTop (nhds a) := by
  have hs : Bornology.IsBounded (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) C) :=
    Metric.isBounded_closedBall
  have hx : ∀ k, x k ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) C := by
    intro k
    simpa [Metric.mem_closedBall, dist_eq_norm] using hC k
  obtain ⟨a, -, g, hg, hlim⟩ := tendsto_subseq_of_bounded hs hx
  exact ⟨a, g, hg, hlim⟩

end Math

#print axioms Math.bolzano_weierstrass

