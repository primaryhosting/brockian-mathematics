/-
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ}

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/

lemma inner_eq_zero_of_mem_span {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ
    (EuclideanSpace ℂ (Fin d))) (s : Finset ι) {x : EuclideanSpace ℂ (Fin d)}
    (hx : x ∈ Submodule.span ℂ (b '' (s : Set ι))) {i : ι} (hi : i ∉ s) :
    inner ℂ (b i) x = 0 := by
  have hle : Submodule.span ℂ (b '' (s : Set ι)) ≤
      LinearMap.ker (innerSL ℂ (b i) : EuclideanSpace ℂ (Fin d) →L[ℂ] ℂ).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    have hne : i ≠ j := by rintro rfl; exact hi hj
    simpa using b.orthonormal.2 hne
  simpa using hle hx

/-- On the span of eigenvectors with eigenvalues above `θ`, the quadratic form dominates
`θ ‖x‖²` strictly. -/
