/-
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset Complex

variable {n : ℕ}

/-- Auxiliary: the derivative of the (constant) squared norm of a normalized state vanishes. -/

lemma norm_deriv_zero {n : ℕ} (psi : ℝ → Fin n → ℂ) (dpsi : Fin n → ℂ) (l : ℝ)
    (hpsid : ∀ i, HasDerivAt (fun t => psi t i) (dpsi i) l)
    (hnorm : ∀ t : ℝ, ∑ i, (starRingEnd ℂ) (psi t i) * psi t i = 1) :
    ∑ i, ((starRingEnd ℂ) (dpsi i) * psi l i + (starRingEnd ℂ) (psi l i) * dpsi i) = 0 := by
  have hd : HasDerivAt (fun t => ∑ i, (starRingEnd ℂ) (psi t i) * psi t i)
      (∑ i, ((starRingEnd ℂ) (dpsi i) * psi l i + (starRingEnd ℂ) (psi l i) * dpsi i)) l := by
    apply HasDerivAt.fun_sum
    intro i _
    exact ((hpsid i).star).mul (hpsid i)
  have hc : HasDerivAt (fun t => ∑ i, (starRingEnd ℂ) (psi t i) * psi t i) 0 l := by
    have : (fun t => ∑ i, (starRingEnd ℂ) (psi t i) * psi t i) = fun _ : ℝ => (1 : ℂ) :=
      funext hnorm
    rw [this]
    exact hasDerivAt_const l 1
  exact hd.unique hc

/-- **Hellmann–Feynman theorem** (finite-dimensional form).

Let `H i j t` be the entries of a family of Hermitian matrices depending on a real parameter `t`,
let `psi t` be a normalized eigenvector of `H · · t` with real eigenvalue `E t`, and suppose all
data are differentiable at `l`, with `dH i j` the derivative of the entries, `dpsi` the derivative
of the state and `dE` the derivative of the eigenvalue.  Then

`dE/dλ = ⟪ψ, (dH/dλ) ψ⟫`. -/
