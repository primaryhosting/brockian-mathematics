/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open ComplexConjugate Finset

variable {n : ℕ}

/-- The expectation value `⟨A⟩ = ⟪ψ, A ψ⟫` of an observable `A` (given as a matrix)
in the state `ψ` (a vector of `ℂ^n`). -/

lemma hasDerivAt_expect
    (ψ dψ : ℝ → Fin n → ℂ) (A dA : ℝ → Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (hψ : ∀ i, HasDerivAt (fun s => ψ s i) (dψ t i) t)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (dA t i j) t) :
    HasDerivAt (fun s => expect (ψ s) (A s))
      (∑ i, ∑ j, (conj (dψ t i) * (A t i j * ψ t j)
        + conj (ψ t i) * (dA t i j * ψ t j)
        + conj (ψ t i) * (A t i j * dψ t j))) t := by
  have hfun : (fun s => expect (ψ s) (A s))
      = fun s => ∑ i, ∑ j, conj (ψ s i) * (A s i j * ψ s j) := rfl
  rw [hfun]
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  have h1 : HasDerivAt (fun s => conj (ψ s i)) (conj (dψ t i)) t := by
    simpa using HasDerivAt.star (𝕜 := ℝ) (F := ℂ) (hψ i)
  have h2 : HasDerivAt (fun s => A s i j * ψ s j)
      (dA t i j * ψ t j + A t i j * dψ t j) t := (hA i j).fun_mul (hψ j)
  exact (h1.fun_mul h2).congr_deriv (by ring)

/-- **Ehrenfest's theorem** (finite-dimensional form).

If the state `ψ : ℝ → ℂ^n` solves the Schrödinger equation `i ℏ ψ' = H ψ` with hermitian
Hamiltonian `H`, and `A : ℝ → Matrix` is a (possibly time-dependent) observable with time
derivative `dA`, then the expectation value `⟨A⟩` satisfies

`d⟨A⟩/dt = (i/ℏ) ⟨[H, A]⟩ + ⟨∂A/∂t⟩`. -/
