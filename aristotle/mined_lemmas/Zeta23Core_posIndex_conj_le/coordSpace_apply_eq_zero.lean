import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
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

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m]
  [Fintype d] [DecidableEq d]

/-- The real quadratic form associated with a matrix `Q`: `x ↦ Re (xᴴ Q x)`. -/

lemma coordSpace_apply_eq_zero {s : Finset m} {y : m → 𝕜} (hy : y ∈ coordSpace (𝕜 := 𝕜) s)
    {j : m} (hj : j ∉ s) : y j = 0 := by
  have hle : coordSpace (𝕜 := 𝕜) s ≤ LinearMap.ker (LinearMap.proj j : (m → 𝕜) →ₗ[𝕜] 𝕜) := by
    rw [coordSpace, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hij : (i : m) ≠ j := fun h => hj (h ▸ i.2)
    simp [LinearMap.mem_ker, hij]
  exact hle hy

/-- The quadratic form of a diagonal matrix. -/
