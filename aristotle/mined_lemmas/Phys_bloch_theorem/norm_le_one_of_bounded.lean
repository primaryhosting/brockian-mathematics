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

lemma norm_le_one_of_bounded {a : ℝ} {ψ : ℝ → ℂ} {lam : ℂ} {C x₀ : ℝ}
    (hT : ∀ x : ℝ, ψ (x + a) = lam * ψ x)
    (hb : ∀ x : ℝ, ‖ψ x‖ ≤ C) (hx₀ : ψ x₀ ≠ 0) :
    ‖lam‖ ≤ 1 := by
  by_contra h
  push_neg at h
  have hpos : 0 < ‖ψ x₀‖ := norm_pos_iff.mpr hx₀
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / ‖ψ x₀‖) h
  have hle := hb (x₀ + n * a)
  rw [iterate_translate_eq hT n x₀, norm_mul, norm_pow] at hle
  rw [div_lt_iff₀ hpos] at hn
  linarith

/-- A bounded, nonzero quasi-periodic wavefunction forces the phase factor to have modulus one. -/
