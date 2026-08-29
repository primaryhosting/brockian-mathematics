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

lemma hodgeClasses_eq_top_of_piece_eq_top {w : ℤ} {V : Type} [AddCommGroup V] [Module ℚ V]
    (H : HodgeStructure w V) (p : ℤ) (hp : H.piece p = ⊤) :
    hodgeClasses H p = ⊤ := by
  ext v
  simp [mem_hodgeClasses_iff, hp]

/-- If a rational vector space is trivial then it has no nonzero Hodge classes. -/
