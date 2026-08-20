import Mathlib

/-!
# Grover Optimal
Category: Frontier Qi
Target: QI.grover_optimal
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

namespace QI

/-- The Hilbert space of a quantum query algorithm searching a database of `N` items:
the index register `Fin N` together with an arbitrary workspace register `K`. -/
abbrev HSpace (N : ℕ) (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  PiLp 2 (fun _ : Fin N => K)

variable {N : ℕ} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The (phase) query operator for the database whose unique marked item is `x`:
it flips the sign of the component of the index register at `x`. -/

lemma norm_phaseOracle_sub_self (x : Fin N) (psi : HSpace N K) :
    ‖phaseOracle x psi - psi‖ = 2 * ‖psi x‖ := by
  rw [PiLp.norm_eq_of_L2]
  have key : ∀ y : Fin N, ‖(phaseOracle x psi - psi).ofLp y‖ ^ 2
      = if y = x then (2 * ‖psi x‖) ^ 2 else 0 := by
    intro y
    show ‖(phaseOracle x psi) y - psi y‖ ^ 2 = _
    simp only [phaseOracle_apply]
    split <;> rename_i h
    · subst h
      rw [show -(psi y) - psi y = (-2 : ℝ) • psi y by module, norm_smul]
      simp [mul_pow]
    · simp
  rw [Finset.sum_congr rfl (fun y _ => key y), Finset.sum_ite_eq' Finset.univ x]
  simp [Real.sqrt_sq]

/-- Cauchy–Schwarz: the sum of the index-register component norms is at most `√N ‖ψ‖`. -/
