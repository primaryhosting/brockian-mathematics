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

set_option autoImplicit false

namespace Phys

open Complex

/-- Translation of a wavefunction by `a`: `(translate a ψ) x = ψ (x + a)`. -/

theorem bloch_theorem_of_bounded {a : ℝ} (ha : a ≠ 0) {ψ : ℝ → ℂ} {lam : ℂ} {M x₀ : ℝ}
    (hT : translate a ψ = fun x => lam * ψ x)
    (hM : ∀ x : ℝ, ‖ψ x‖ ≤ M) (hx₀ : ψ x₀ ≠ 0) :
    ∃ (k : ℝ) (u : ℝ → ℂ),
      (∀ x : ℝ, u (x + a) = u x) ∧
      (∀ x : ℝ, ψ x = Complex.exp (k * x * I) * u x) ∧
      lam = Complex.exp (k * a * I) := by
  have hlam : ‖lam‖ = 1 :=
    norm_translation_eigenvalue_eq_one (fun x => congrFun hT x) hM hx₀
  exact bloch_theorem a ha ψ lam hlam hT

end Phys

import Mathlib

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

