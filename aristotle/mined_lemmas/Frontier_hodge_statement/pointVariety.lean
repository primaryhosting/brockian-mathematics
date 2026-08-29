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

noncomputable def pointVariety : HodgeVarietyData 0 where
  coh := pointCoh
  hs p := tateHodgeStructure (pointCoh p) (p : ℤ)
  alg _ := ⊤
  alg_le_hodge p := by rw [hodgeClasses_tate]
  vanishing p hp := by
    obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
    refine le_antisymm (fun x _ => ?_) bot_le
    haveI : Subsingleton (pointCoh (n + 1)) := inferInstanceAs (Subsingleton PUnit)
    have : x = 0 := Subsingleton.elim x 0
    simp [this]

/-- The Hodge conjecture holds for a point.  In particular the hypotheses of `hodge_statement`
are satisfiable, so the statement is not vacuous. -/
