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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

open Filter Topology

namespace Math

/-- **Bolzano-Weierstrass theorem.** Every bounded sequence in `ℝ^n` has a convergent
subsequence: if `x : ℕ → EuclideanSpace ℝ (Fin n)` is bounded in norm, then there is a
strictly monotone index map `s` and a point `a` such that `x ∘ s` tends to `a`. -/
theorem bolzano_weierstrass (n : ℕ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hbdd : ∃ C : ℝ, ∀ k, ‖x k‖ ≤ C) :
    ∃ (s : ℕ → ℕ) (a : EuclideanSpace ℝ (Fin n)),
      StrictMono s ∧ Filter.Tendsto (x ∘ s) Filter.atTop (nhds a) := by
  obtain ⟨C, hC⟩ := hbdd
  obtain ⟨a, -, s, hs, hlim⟩ :=
    tendsto_subseq_of_bounded (s := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) C)
      Metric.isBounded_closedBall (fun k => by simpa [Metric.mem_closedBall] using hC k)
  exact ⟨s, a, hs, hlim⟩

end Math

