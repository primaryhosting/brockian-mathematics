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

theorem accessibleInfo_le_holevoChi [Fintype d] [DecidableEq d] [Fintype X]
    {O : Type*} [Fintype O] [DecidableEq O] [Nonempty O]
    (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (r : X → d → ℝ) (hr0 : ∀ x i, 0 ≤ r x i) (hr1 : ∀ x, ∑ i, r x i = 1)
    (U : Matrix d d ℂ) (hU : U ∈ Matrix.unitaryGroup d ℂ)
    (ρ : X → Matrix d d ℂ) (hρ : ∀ x, ρ x = U * (Matrix.diagonal fun i => (r x i : ℂ)) * star U) :
    accessibleInfo O p ρ ≤ holevoChi p ρ := by
  classical
  have hpovm : IsPOVM (fun o : O => if o = Classical.arbitrary O then (1 : Matrix d d ℂ) else 0) := by
    refine ⟨fun o => ?_, by simp⟩
    by_cases h : o = Classical.arbitrary O <;>
      simp [h, Matrix.PosSemidef.one, Matrix.PosSemidef.zero]
  refine csSup_le ⟨_, ⟨_, hpovm, rfl⟩⟩ ?_
  rintro I ⟨E, hE, rfl⟩
  exact holevo_bound p hp0 hp1 r hr0 hr1 U hU ρ hρ E hE

/-! ## Tightness -/

/-- The bound is attained (and the statement is not vacuous): for the uniform ensemble of the two
orthogonal states `|0⟩⟨0|`, `|1⟩⟨1|` measured in the distinguishing basis, both the measured
information and the Holevo quantity equal `log 2`. -/
