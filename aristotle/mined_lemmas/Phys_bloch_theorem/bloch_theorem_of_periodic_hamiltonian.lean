/-
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

open Complex

/-- The translation operator by `a` acting on wave functions. -/

theorem bloch_theorem_of_periodic_hamiltonian (a : ℝ) (ha : 0 < a) (V ψ : ℝ → ℂ) (E : ℂ)
    (M : ℝ) (hV : ∀ x, V (x + a) = V x)
    (hE : ∀ x, hamiltonian V ψ x = E * ψ x)
    (hnd : ∀ φ : ℝ → ℂ, (∀ x, hamiltonian V φ x = E * φ x) → ∃ c : ℂ, ∀ x, φ x = c * ψ x)
    (hbdd : ∀ x, ‖ψ x‖ ≤ M) (x₀ : ℝ) (hx₀ : ψ x₀ ≠ 0) :
    ∃ k : ℝ, ∃ u : ℝ → ℂ, (∀ x, u (x + a) = u x) ∧
      ∀ x, ψ x = Complex.exp (Complex.I * k * x) * u x := by
  have hcomm := hamiltonian_comm_translate a V hV ψ
  have hTE : ∀ x, hamiltonian V (translate a ψ) x = E * translate a ψ x := by
    intro x
    rw [hcomm]
    simpa [translate] using hE (x + a)
  obtain ⟨c, hc⟩ := hnd (translate a ψ) hTE
  exact bloch_theorem_of_bounded a ha ψ c M hbdd x₀ hx₀ hc

#print axioms bloch_theorem
#print axioms bloch_theorem_of_periodic_hamiltonian

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

