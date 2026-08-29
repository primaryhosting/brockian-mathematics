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

def pointCoh : ℕ → Type
  | 0 => ℚ
  | _ + 1 => PUnit

instance instPointCohAddCommGroup : ∀ p, AddCommGroup (pointCoh p)
  | 0 => inferInstanceAs (AddCommGroup ℚ)
  | _ + 1 => inferInstanceAs (AddCommGroup PUnit)

instance instPointCohModule : ∀ p, Module ℚ (pointCoh p)
  | 0 => inferInstanceAs (Module ℚ ℚ)
  | _ + 1 => inferInstanceAs (Module ℚ PUnit)

instance instPointCohFinite : ∀ p, Module.Finite ℚ (pointCoh p)
  | 0 => inferInstanceAs (Module.Finite ℚ ℚ)
  | _ + 1 => inferInstanceAs (Module.Finite ℚ PUnit)

/-- The Hodge-theoretic data of a point: all cohomology is of Tate type and algebraic. -/
