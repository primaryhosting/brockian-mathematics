import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
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

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The real quadratic form `x ↦ re ⟪x, M x⟫` associated to a matrix `M`. -/

lemma inner_eq_zero_of_mem_span
    (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) (s : Finset (Fin d))
    {x : EuclideanSpace ℂ (Fin d)} (hx : x ∈ Submodule.span ℂ (b '' (s : Set (Fin d))))
    {i : Fin d} (hi : i ∉ s) : inner ℂ (b i) x = 0 := by
  have hle : Submodule.span ℂ (b '' (s : Set (Fin d)))
      ≤ LinearMap.ker ((innerSL ℂ (b i) : EuclideanSpace ℂ (Fin d) →L[ℂ] ℂ) : _ →ₗ[ℂ] ℂ) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    simp [LinearMap.mem_ker, b.orthonormal.2 hij]
  simpa using hle hx

/-- The span of a subfamily of an orthonormal basis has dimension equal to the number of vectors
in the subfamily. -/
