import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Scope and contents

States are density matrices `ρ : Matrix d d ℂ`, measurements are POVMs (`QI.IsPOVM`), the von
Neumann entropy `QI.vonNeumannEntropy` is the sum of `-λ log λ` over the eigenvalues, and
`QI.holevoChi` is `S(∑ pₓ ρₓ) - ∑ pₓ S(ρₓ)`.

The main theorem `QI.holevo_bound` proves the Holevo bound
`I(X;Y) ≤ χ` for ensembles of *commuting* states, i.e. states that are simultaneously
diagonalizable by one unitary `U`, and for an arbitrary POVM measurement; the supremum form
`QI.accessibleInfo_le_holevoChi` then bounds the accessible information by `χ`.
The general (non-commuting) case rests on the monotonicity of quantum relative entropy, which
is not available in Mathlib and is not developed here.

The mathematical core is classical: the log-sum inequality (`QI.log_sum_inequality`) and the
resulting data-processing inequality for the Kullback-Leibler divergence
(`QI.kl_data_processing`); the Holevo quantity of a commuting ensemble is
`∑ₓ pₓ D(rₓ ‖ r̄)`, and measuring with a POVM applies the stochastic map
`W y i = (E y) i i` to each `rₓ`.
-/

namespace QI

open Matrix Real Finset ComplexOrder

/-! ## Classical information-theoretic core -/

/-- The log-sum inequality:
`(∑ aᵢ) log ((∑ aᵢ)/(∑ bᵢ)) ≤ ∑ aᵢ log (aᵢ/bᵢ)` for nonnegative `a`, `b` with `a ≪ b`. -/

theorem vonNeumannEntropy_unitary_conj [Fintype d] [DecidableEq d] {U : Matrix d d ℂ}
    (hU : U ∈ Matrix.unitaryGroup d ℂ) (ρ : Matrix d d ℂ) :
    vonNeumannEntropy (U * ρ * star U) = vonNeumannEntropy ρ := by
  have h1 : star U * U = 1 := hU.1
  have h2 : U * star U = 1 := hU.2
  have hback : star U * (U * ρ * star U) * U = ρ := by
    calc star U * (U * ρ * star U) * U = (star U * U) * ρ * (star U * U) := by
          simp [Matrix.mul_assoc]
      _ = ρ := by rw [h1]; simp
  by_cases h : ρ.IsHermitian
  · have h' : (U * ρ * star U).IsHermitian := isHermitian_conj U h
    rw [vonNeumannEntropy_of_isHermitian h', vonNeumannEntropy_of_isHermitian h]
    have hchar : (U * ρ * star U).charpoly = ρ.charpoly := by
      let u : (Matrix d d ℂ)ˣ := ⟨U, star U, h2, h1⟩
      have h3 : ((u : (Matrix d d ℂ)ˣ) : Matrix d d ℂ) * ρ *
          ((u⁻¹ : (Matrix d d ℂ)ˣ) : Matrix d d ℂ) = U * ρ * star U := by
        simp [u, Units.inv_mk]
      have := Matrix.charpoly_units_conj u ρ
      rwa [h3] at this
    rw [(Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff h' h).2 hchar]
  · have h' : ¬ (U * ρ * star U).IsHermitian := by
      intro hc
      have := isHermitian_conj (star U) hc
      rw [star_star, hback] at this
      exact h this
    simp only [vonNeumannEntropy, dif_neg h, dif_neg h']

/-- Born probabilities for a diagonal state. -/
