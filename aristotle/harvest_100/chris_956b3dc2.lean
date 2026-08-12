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

namespace Math

/-- **Bolzano–Weierstrass in `ℝⁿ`.** Every bounded sequence `u : ℕ → EuclideanSpace ℝ (Fin n)`
has a subsequence converging to some point of `ℝⁿ`. Boundedness is expressed as the existence
of a uniform bound `C` on the norms `‖u k‖`. -/
theorem bolzano_weierstrass {n : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin n))
    (hbdd : ∃ C : ℝ, ∀ k, ‖u k‖ ≤ C) :
    ∃ (L : EuclideanSpace ℝ (Fin n)) (phi : ℕ → ℕ),
      StrictMono phi ∧ Filter.Tendsto (u ∘ phi) Filter.atTop (nhds L) := by
  obtain ⟨C, hC⟩ := hbdd
  have hmem : ∀ k, u k ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) C := by
    intro k
    simpa [Metric.mem_closedBall, dist_eq_norm] using hC k
  obtain ⟨L, -, phi, hphi, hlim⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) C).tendsto_subseq hmem
  exact ⟨L, phi, hphi, hlim⟩

end Math

