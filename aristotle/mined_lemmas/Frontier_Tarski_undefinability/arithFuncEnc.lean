/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open FirstOrder Language

namespace Frontier

/-! ## The first-order language of arithmetic -/

/-- The function symbols of the language of arithmetic: `0`, `1`, `+`, `*`. -/
inductive arithFunc : ℕ → Type
  | zero : arithFunc 0
  | one : arithFunc 0
  | add : arithFunc 2
  | mul : arithFunc 2
  deriving DecidableEq

/-- The first-order language of arithmetic, with function symbols `0, 1, +, *`
and no relation symbols. -/

private def arithFuncEnc : (Σ l, arith.Functions l) → ℕ
  | ⟨_, .zero⟩ => 0
  | ⟨_, .one⟩ => 1
  | ⟨_, .add⟩ => 2
  | ⟨_, .mul⟩ => 3

