/-
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-- The translation operator `T_a` acting on wavefunctions: `(T_a ψ)(x) = ψ (x + a)`. -/

lemma iterate_translate_eq {a : ℝ} {ψ : ℝ → ℂ} {lam : ℂ}
    (hT : ∀ x : ℝ, ψ (x + a) = lam * ψ x) :
    ∀ (n : ℕ) (x : ℝ), ψ (x + n * a) = lam ^ n * ψ x := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
      intro x
      have hx : x + (↑(n + 1) : ℝ) * a = (x + n * a) + a := by push_cast; ring
      rw [hx, hT, ih, pow_succ]
      ring

/-- If `ψ` is bounded, not identically zero at `x₀`, and satisfies `ψ (x + a) = lam * ψ x`,
then `‖lam‖ ≤ 1`. -/
