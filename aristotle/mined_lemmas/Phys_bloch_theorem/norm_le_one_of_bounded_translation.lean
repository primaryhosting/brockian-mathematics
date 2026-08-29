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

/-- Iterating a translation-eigenvalue relation: `ψ (x₀ + n a) = c ^ n * ψ x₀`. -/

theorem norm_le_one_of_bounded_translation (a : ℝ) (ψ : ℝ → ℂ) (c : ℂ) (M : ℝ)
    (hb : ∀ x : ℝ, ‖ψ x‖ ≤ M) (x₀ : ℝ) (h0 : ψ x₀ ≠ 0)
    (hc : ∀ x : ℝ, ψ (x + a) = c * ψ x) : ‖c‖ ≤ 1 := by
  by_contra hgt
  push_neg at hgt
  have hpos : 0 < ‖ψ x₀‖ := norm_pos_iff.mpr h0
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / ‖ψ x₀‖) hgt
  have hkey : ‖c‖ ^ n * ‖ψ x₀‖ ≤ M := by
    have := hb (x₀ + (n : ℝ) * a)
    rwa [translate_iterate a ψ c hc x₀ n, norm_mul, norm_pow] at this
  have : M / ‖ψ x₀‖ * ‖ψ x₀‖ < ‖c‖ ^ n * ‖ψ x₀‖ := by
    exact (mul_lt_mul_of_pos_right hn hpos)
  rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at this
  linarith

/-- **Bloch's theorem.**  Let `H` be a Hamiltonian on wavefunctions `ℝ → ℂ` which is periodic
with period `a > 0` (it commutes with translation by `a`).  Let `ψ` be a bounded, nonzero
eigenstate of `H` with eigenvalue `E`, whose eigenspace is nondegenerate (one dimensional).
Then `ψ` is a Bloch wave: there are a crystal momentum `k : ℝ` and an `a`-periodic function
`u` with `ψ x = exp (i k x) * u x` for all `x`. -/
