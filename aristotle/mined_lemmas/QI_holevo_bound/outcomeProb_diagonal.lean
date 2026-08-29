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

theorem outcomeProb_diagonal [Fintype d] [DecidableEq d] (E : Matrix d d ℂ) (v : d → ℝ) :
    outcomeProb E (Matrix.diagonal fun i => (v i : ℂ)) = ∑ i, (E i i).re * v i := by
  have : (E * Matrix.diagonal fun i => (v i : ℂ)).trace = ∑ i, E i i * (v i : ℂ) := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.diag]
  rw [outcomeProb, this]
  simp [Complex.re_sum, Complex.mul_re]

/-! ## The Holevo bound -/

/-- The Holevo bound for an ensemble of commuting states, in the special case where the states
are already diagonal.  (The normalization hypotheses `hp1` and `hr1` are part of the data of a
quantum ensemble, but the proof only uses nonnegativity.) -/
