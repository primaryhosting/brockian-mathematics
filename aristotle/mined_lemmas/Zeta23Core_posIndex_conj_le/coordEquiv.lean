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

open Matrix Module

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m]
  [Fintype d] [DecidableEq d]

/-- The (real) quadratic form associated with a matrix `Q`: `x ↦ Re (xᴴ Q x)`. -/

noncomputable def coordEquiv (s : Finset m) : (coordSub (𝕜 := 𝕜) s) ≃ₗ[𝕜] (s → 𝕜) where
  toFun x i := (x : m → 𝕜) i
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  invFun y := ⟨fun i => if h : i ∈ s then y ⟨i, h⟩ else 0, by intro i hi; simp [hi]⟩
  left_inv := by
    intro x
    ext i
    by_cases h : i ∈ s
    · simp [h]
    · simp [h, x.2 i h]
  right_inv := by
    intro y
    ext i
    simp

omit [Fintype m] in
