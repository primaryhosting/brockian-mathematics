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

theorem log_sum_inequality {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hab : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) ≤ ∑ i, a i * Real.log (a i / b i) := by
  set A := ∑ i, a i with hA
  set B := ∑ i, b i with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => ha i
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => hb i
  rcases eq_or_lt_of_le hB0 with hB' | hB'
  · have hbz : ∀ i, b i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hb i)).1 hB'.symm i (mem_univ i)
    have haz : ∀ i, a i = 0 := fun i => hab i (hbz i)
    have hAz : A = 0 := by simp [hA, haz]
    simp [hAz, haz]
  · rcases eq_or_lt_of_le hA0 with hA' | hA'
    · have haz : ∀ i, a i = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha i)).1 hA'.symm i (mem_univ i)
      simp [← hA', haz]
    · have key : ∀ i ∈ (univ : Finset ι),
          a i * Real.log (A / B) + (a i - b i * (A / B)) ≤ a i * Real.log (a i / b i) := by
        intro i _
        rcases eq_or_lt_of_le (ha i) with hai | hai
        · have h0 : a i = 0 := hai.symm
          simp only [h0, zero_mul, zero_sub, zero_add]
          have : 0 ≤ b i * (A / B) := mul_nonneg (hb i) (by positivity)
          linarith
        · have hbi : 0 < b i := by
            rcases eq_or_lt_of_le (hb i) with h | h
            · exact absurd (hab i h.symm) (by linarith)
            · exact h
          have htpos : 0 < (a i / b i) / (A / B) := by positivity
          set t := (a i / b i) / (A / B) with ht
          have hlogt : Real.log t = Real.log (a i / b i) - Real.log (A / B) := by
            rw [ht, Real.log_div (by positivity) (by positivity)]
          have h1 : 1 - t⁻¹ ≤ Real.log t := by
            have := Real.log_le_sub_one_of_pos (show (0:ℝ) < t⁻¹ by positivity)
            rw [Real.log_inv] at this
            linarith
          have h2 : a i * t⁻¹ = b i * (A / B) := by rw [ht]; field_simp
          have h3 := mul_le_mul_of_nonneg_left h1 hai.le
          have h4 : a i * (1 - t⁻¹) = a i - b i * (A / B) := by rw [mul_sub, mul_one, h2]
          have h5 : a i * Real.log t = a i * Real.log (a i / b i) - a i * Real.log (A / B) := by
            rw [hlogt]; ring
          linarith
      have hsum := Finset.sum_le_sum key
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
        ← Finset.sum_mul] at hsum
      rw [← hA, ← hB] at hsum
      have hBA : B * (A / B) = A := by field_simp
      rw [hBA] at hsum
      simpa using hsum

/-- Data processing inequality for the Kullback-Leibler divergence:
applying a stochastic map `W` to two distributions cannot increase their divergence. -/
