/-
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The real quadratic form `x ↦ xᴴ Q x` associated with a square matrix `Q`
(for Hermitian `Q` the value `xᴴ Q x` is real, and `qform` records its real part). -/

theorem finrank_le_of_injOn {m : Type*} [Fintype m] {N : Type*} [AddCommGroup N] [Module 𝕜 N]
    [Module.Finite 𝕜 N] (S : Submodule 𝕜 (m → 𝕜)) (f : (m → 𝕜) →ₗ[𝕜] N)
    (hf : ∀ y ∈ S, f y = 0 → y = 0) : Module.finrank 𝕜 S ≤ Module.finrank 𝕜 N := by
  refine LinearMap.finrank_le_finrank_of_injective (f := f.comp S.subtype) ?_
  intro a b hab
  have h0 : f (a - b : S) = 0 := by
    have : f (a : m → 𝕜) = f (b : m → 𝕜) := hab
    simp [map_sub, this]
  have := hf ((a : m → 𝕜) - b) (S.sub_mem a.2 b.2) (by simpa using h0)
  exact Subtype.ext (sub_eq_zero.mp this)

section Main

variable {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d] [DecidableEq d]

/-- **Direction B (hard direction of Sylvester's law), in compressed form.**
If the quadratic form of `Q` is positive on the (nonzero vectors of the) image of a subspace
`S` under `B`, then `dim S ≤ n₊(Q)`. -/
