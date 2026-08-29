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

theorem measuredInfo_eq_holevoChi_of_orthogonal_pair :
    measuredInfo (fun _ : Fin 2 => (1/2 : ℝ))
        (fun x : Fin 2 => Matrix.diagonal fun i : Fin 2 => ((if x = i then (1:ℝ) else 0 : ℝ) : ℂ))
        (fun y : Fin 2 => Matrix.diagonal fun i : Fin 2 => ((if i = y then (1:ℝ) else 0 : ℝ) : ℂ))
      = Real.log 2 ∧
    holevoChi (fun _ : Fin 2 => (1/2 : ℝ))
        (fun x : Fin 2 => Matrix.diagonal fun i : Fin 2 => ((if x = i then (1:ℝ) else 0 : ℝ) : ℂ))
      = Real.log 2 := by
  constructor
  · rw [measuredInfo]
    simp only [outcomeProb_diagonal, Matrix.diagonal_apply_eq, Complex.ofReal_re]
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [Fin.sum_univ_two]
    ring
  · have havg : (∑ x : Fin 2, (1/2 : ℝ) •
        (Matrix.diagonal fun i : Fin 2 => ((if x = i then (1:ℝ) else 0 : ℝ) : ℂ)))
        = Matrix.diagonal (fun _ : Fin 2 => (((1/2 : ℝ)) : ℂ)) := by
      ext i j
      by_cases h : i = j
      · subst h
        simp only [Matrix.sum_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply,
          Fin.sum_univ_two, Complex.real_smul]
        fin_cases i <;> norm_num
      · simp [Matrix.sum_apply, h]
    rw [holevoChi, havg, vonNeumannEntropy_diagonal]
    simp only [vonNeumannEntropy_diagonal]
    have h0 : ∀ x : Fin 2, ∑ i : Fin 2, Real.negMulLog (if x = i then (1:ℝ) else 0) = 0 := by
      intro x; fin_cases x <;> simp [Real.negMulLog]
    simp only [h0]
    simp [Real.negMulLog]

end QI

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

