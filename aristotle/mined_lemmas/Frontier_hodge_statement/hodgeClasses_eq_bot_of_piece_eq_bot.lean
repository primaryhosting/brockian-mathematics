import Mathlib
/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
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

open TensorProduct

/-- Complex conjugation acting on the complexification `ℂ ⊗[ℚ] V` of a rational vector
space `V` (conjugation on the left factor, identity on `V`).  It is only `ℚ`-linear
(it is conjugate-linear over `ℂ`). -/

theorem hodgeClasses_eq_bot_of_piece_eq_bot (X : HodgeVariety H) (p : ℕ)
    (hp : (X.hs p).piece p p = ⊥) : hodgeClasses X p = ⊥ := by
  refine le_antisymm (fun v hv => ?_) bot_le
  have hv' : (1 : ℂ) ⊗ₜ[ℚ] v ∈ (X.hs p).piece p p := hv
  rw [hp, Submodule.mem_bot] at hv'
  have hinj : Function.Injective ((TensorProduct.mk ℚ ℂ (H p)) 1) :=
    Module.FaithfullyFlat.tensorProduct_mk_injective (H p)
  have : v = 0 := by
    have h0 : ((TensorProduct.mk ℚ ℂ (H p)) 1) v = ((TensorProduct.mk ℚ ℂ (H p)) 1) 0 := by
      simpa using hv'
    exact hinj h0
  simp [this]

/-- Vanishing case of the Hodge conjecture: if `H^{p,p} = 0` then the conjecture holds in
codimension `p` (both sides are zero). -/
