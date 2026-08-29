/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
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

/-- The radical of a natural number: the product of its distinct prime factors. -/

lemma exceptional_antitone {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    Exceptional ε₂ ⊆ Exceptional ε₁ := by
  rintro ⟨a, b⟩ ⟨ha, hb, hab, hlt⟩
  refine ⟨ha, hb, hab, lt_of_le_of_lt ?_ hlt⟩
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast one_le_rad (a * b * (a + b))) (by linarith)

