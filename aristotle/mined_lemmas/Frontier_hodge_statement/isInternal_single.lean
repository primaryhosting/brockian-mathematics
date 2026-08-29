/-
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## Complex conjugation on a complexified rational vector space -/

/-- Complex conjugation, viewed as a `ℚ`-linear endomorphism of `ℂ`. -/

lemma isInternal_single {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (i₀ : ℤ) :
    DirectSum.IsInternal (fun k : ℤ => if k = i₀ then (⊤ : Submodule R M) else ⊥) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨fun i => ?_, le_antisymm le_top (le_iSup_of_le i₀ (by simp))⟩
  by_cases h : i = i₀
  · have hbot : (⨆ j, ⨆ (_ : j ≠ i), if j = i₀ then (⊤ : Submodule R M) else ⊥) = ⊥ := by
      refine iSup_eq_bot.2 fun j => iSup_eq_bot.2 fun hj => ?_
      have : j ≠ i₀ := by rw [← h] at *; exact hj
      simp [this]
    simp [hbot]
  · simp [h]

/-- The Hodge structure of *Tate type* `(p, p)` on a rational vector space `V`: the whole
complexification sits in the `(p,p)`-piece.  (For `V = ℚ` and `p = 0` this is the Hodge structure
on `H^0` of a connected variety; for `p = d` on `H^{2d}`.)  In particular Hodge structures, in
the above sense, exist. -/
