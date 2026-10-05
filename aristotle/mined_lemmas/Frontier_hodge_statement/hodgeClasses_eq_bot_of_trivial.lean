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

lemma hodgeClasses_eq_bot_of_trivial {w : ℤ} {V : Type} [AddCommGroup V] [Module ℚ V]
    (H : HodgeStructure w V) (p : ℤ) (hV : (⊤ : Submodule ℚ V) = ⊥) :
    hodgeClasses H p = ⊥ :=
  le_antisymm (hV ▸ le_top) bot_le

/-- A one-index family of submodules, equal to everything at `i₀` and zero elsewhere, gives an
internal direct sum decomposition. -/
