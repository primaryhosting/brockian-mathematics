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

theorem kl_data_processing {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W : κ → ι → ℝ) (hW0 : ∀ y i, 0 ≤ W y i) (hW1 : ∀ i, ∑ y, W y i = 1)
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hab : ∀ i, b i = 0 → a i = 0) :
    ∑ y, (∑ i, W y i * a i) * Real.log ((∑ i, W y i * a i) / (∑ i, W y i * b i))
      ≤ ∑ i, a i * Real.log (a i / b i) := by
  have step : ∀ y ∈ (univ : Finset κ),
      (∑ i, W y i * a i) * Real.log ((∑ i, W y i * a i) / (∑ i, W y i * b i))
        ≤ ∑ i, W y i * (a i * Real.log (a i / b i)) := by
    intro y _
    have h := log_sum_inequality (fun i => W y i * a i) (fun i => W y i * b i)
      (fun i => mul_nonneg (hW0 y i) (ha i)) (fun i => mul_nonneg (hW0 y i) (hb i))
      (by
        intro i hi
        rcases mul_eq_zero.1 hi with h | h
        · simp [h]
        · simp [hab i h])
    refine h.trans_eq (Finset.sum_congr rfl fun i _ => ?_)
    by_cases hw : W y i = 0
    · simp [hw]
    · rw [mul_div_mul_left _ _ hw, mul_assoc]
  calc ∑ y, (∑ i, W y i * a i) * Real.log ((∑ i, W y i * a i) / (∑ i, W y i * b i))
      ≤ ∑ y, ∑ i, W y i * (a i * Real.log (a i / b i)) := Finset.sum_le_sum step
    _ = ∑ i, (∑ y, W y i) * (a i * Real.log (a i / b i)) := by
        rw [Finset.sum_comm]; simp [Finset.sum_mul]
    _ = ∑ i, a i * Real.log (a i / b i) := by simp [hW1]

/-! ## Quantum definitions -/

variable {d X Y : Type*}

open Classical in
/-- The von Neumann entropy `S(ρ) = -Tr ρ log ρ` of a Hermitian matrix, computed from its
eigenvalues. (It is set to `0` on non-Hermitian matrices.) -/
