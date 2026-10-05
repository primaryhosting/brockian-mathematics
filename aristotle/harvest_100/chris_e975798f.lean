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

set_option grind.warning false

namespace Math

/-- **Bolzano–Weierstrass**: every bounded sequence in `ℝ^n` has a convergent subsequence.
Boundedness is expressed as a uniform norm bound `‖x k‖ ≤ C`; the conclusion provides a
limit point `a` and a strictly monotone index map `g` with `x ∘ g → a`. -/
theorem bolzano_weierstrass {n : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin n)) (C : ℝ)
    (hC : ∀ k, ‖x k‖ ≤ C) :
    ∃ (a : EuclideanSpace ℝ (Fin n)) (g : ℕ → ℕ),
      StrictMono g ∧ Filter.Tendsto (x ∘ g) Filter.atTop (nhds a) := by
  have hs : Bornology.IsBounded (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) C) :=
    Metric.isBounded_closedBall
  have hx : ∀ k, x k ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) C := by
    intro k
    simpa [Metric.mem_closedBall, dist_zero_right] using hC k
  obtain ⟨a, -, g, hg, hlim⟩ := tendsto_subseq_of_bounded hs hx
  exact ⟨a, g, hg, hlim⟩

end Math

