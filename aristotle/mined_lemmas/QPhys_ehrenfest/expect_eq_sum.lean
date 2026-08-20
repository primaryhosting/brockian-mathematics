/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

We formalise the Ehrenfest theorem for a finite-dimensional quantum system
(state space `Fin n → ℂ`, observables given by matrices).

If `ψ : ℝ → (Fin n → ℂ)` solves the Schrödinger equation `iℏ ψ'(t) = H ψ(t)`
with `H` Hermitian, and `A : ℝ → Matrix (Fin n) (Fin n) ℂ` is a (possibly time
dependent) observable, then the expectation value `⟪ψ, A ψ⟫` satisfies

  d⟨A⟩/dt = (i/ℏ) ⟨[H, A]⟩ + ⟨∂A/∂t⟩ .
-/

namespace QPhys

open Matrix

variable {n : ℕ}

/-- The expectation value `⟪v, A v⟫ = ∑ i, ∑ j, conj (v i) * A i j * v j`
of the observable `A` in the state `v`. -/

lemma expect_eq_sum (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    expect A v = ∑ i, ∑ j, (starRingEnd ℂ) (v i) * A i j * v j := by
  simp [expect, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/-- The commutator `[H, A] = H A - A H`. -/
