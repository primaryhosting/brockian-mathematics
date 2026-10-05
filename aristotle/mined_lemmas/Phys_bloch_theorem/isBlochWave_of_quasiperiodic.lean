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

lemma isBlochWave_of_quasiperiodic {a θ : ℝ} (ha : a ≠ 0) {ψ : ℝ → ℂ}
    (hT : ∀ x : ℝ, ψ (x + a) = Complex.exp (θ * Complex.I) * ψ x) :
    IsBlochWave a (θ / a) ψ := by
  refine ⟨fun x => Complex.exp (-((θ / a : ℝ) * x * Complex.I)) * ψ x, ?_, ?_⟩
  · intro x
    show Complex.exp (-((θ / a : ℝ) * ((x + a : ℝ) : ℂ) * Complex.I)) * ψ (x + a)
      = Complex.exp (-((θ / a : ℝ) * (x : ℂ) * Complex.I)) * ψ x
    rw [hT x]
    have hka : ((θ / a : ℝ) : ℂ) * ((x + a : ℝ) : ℂ) = ((θ / a : ℝ) : ℂ) * (x : ℂ) + (θ : ℂ) := by
      have hac : ((a : ℂ)) ≠ 0 := by exact_mod_cast ha
      push_cast
      field_simp
    rw [hka]
    rw [show -((((θ / a : ℝ) : ℂ) * (x : ℂ) + (θ : ℂ)) * Complex.I)
        = -(((θ / a : ℝ) : ℂ) * (x : ℂ) * Complex.I) + (-(θ : ℂ) * Complex.I) by ring]
    rw [Complex.exp_add]
    rw [show (-(θ : ℂ) * Complex.I) = -((θ : ℂ) * Complex.I) by ring, Complex.exp_neg]
    field_simp
    rw [← Complex.exp_add]
    simp
  · intro x
    rw [← mul_assoc, ← Complex.exp_add]
    simp

/-- **Bloch's theorem.**  Let `H` be a Hamiltonian acting on wavefunctions on the line which
is invariant under translation by the lattice constant `a > 0`, i.e. it commutes with the
translation operator `T_a`.  Let `ψ` be a bounded eigenstate of `H` with a nondegenerate
eigenvalue `E` (every eigenfunction for `E` is a scalar multiple of `ψ`), and `ψ ≠ 0`.

Then `ψ` is a Bloch wave: there is a quasimomentum `k` and an `a`-periodic function `u`
with `ψ (x) = e^{i k x} u (x)` for all `x`. -/
