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

def coordSub (s : Finset m) : Submodule 𝕜 (m → 𝕜) where
  carrier := {x | ∀ i ∉ s, x i = 0}
  add_mem' := by
    intro a b ha hb i hi
    simp [ha i hi, hb i hi]
  zero_mem' := by intro i _; rfl
  smul_mem' := by
    intro c a ha i hi
    simp [ha i hi]

omit [Fintype m] [DecidableEq m] in
