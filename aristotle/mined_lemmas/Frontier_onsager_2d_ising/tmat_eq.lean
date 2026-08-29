import Mathlib
/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

namespace Frontier

noncomputable section

/-! ## The model -/

/-- The real value `±1` of a spin encoded as a `Bool`. -/

theorem tmat_eq (K : ℝ) (k : ℕ) (a b : Bool) :
    tmat K k a b =
      if a = b then ((2 * Real.cosh K) ^ k + (2 * Real.sinh K) ^ k) / 2
      else ((2 * Real.cosh K) ^ k - (2 * Real.sinh K) ^ k) / 2 := by
  induction k generalizing a b with
  | zero => cases a <;> cases b <;> norm_num [tmat]
  | succ k ih =>
      cases a <;> cases b <;>
        simp [tmat, ih, tw, spinVal, Real.cosh_eq, Real.sinh_eq, Real.exp_neg] <;> ring

/-- Key transfer-matrix identity: summing an open-chain weight against an arbitrary boundary
function `H` of the two endpoints reproduces the matrix power. -/
