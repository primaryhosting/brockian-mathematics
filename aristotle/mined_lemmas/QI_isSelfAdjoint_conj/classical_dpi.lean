import Mathlib

/-!
# Quantum relative entropy and data processing

This file develops, for finite-dimensional systems (complex matrices), the basic theory of the
Umegaki quantum relative entropy

`D(ρ‖σ) = Tr(ρ log ρ) - Tr(ρ log σ)`

for faithful (positive definite) density matrices, together with

* Klein's inequality `QI.relEntropy_nonneg` : `0 ≤ D(ρ‖σ)`;
* invariance under unitary channels `QI.relEntropy_unitary_conj`;
* the data-processing inequality `QI.data_processing_condExp` for trace-self-adjoint maps fixing `σ`
  (conditional expectations), and its concrete instance for the completely dephasing channel
  `QI.data_processing_dephasing`.
-/

open Matrix
open scoped ComplexOrder

namespace QI

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The logarithm of a (Hermitian) matrix, defined through the continuous functional calculus. -/

theorem classical_dpi {m : Type u} [Fintype m] {T : m → n → ℝ} (hT : ∀ j i, 0 ≤ T j i)
    (hTcol : ∀ i, ∑ j, T j i = 1)
    {p q : n → ℝ} (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hTp : ∀ j, 0 < ∑ i, T j i * p i) (hTq : ∀ j, 0 < ∑ i, T j i * q i) :
    ∑ j, (∑ i, T j i * p i) * (Real.log (∑ i, T j i * p i) - Real.log (∑ i, T j i * q i))
      ≤ ∑ i, p i * (Real.log (p i) - Real.log (q i)) := by
  have key : ∀ j : m, (∑ i, T j i * p i) *
      (Real.log (∑ i, T j i * p i) - Real.log (∑ i, T j i * q i))
      ≤ ∑ i, T j i * p i * (Real.log (p i) - Real.log (q i)) := by
    intro j
    set A := ∑ i, T j i * p i with hA
    set B := ∑ i, T j i * q i with hB
    have hApos := hTp j
    have hBpos := hTq j
    have step : ∀ i ∈ Finset.univ, T j i * p i - T j i * q i * (A / B)
        ≤ T j i * p i * (Real.log (p i) - Real.log (q i))
          - T j i * p i * (Real.log A - Real.log B) := by
      intro i _
      rcases eq_or_lt_of_le (hT j i) with h0 | hpos
      · simp [← h0]
      · set a := T j i * p i with ha
        set b := T j i * q i with hb
        have hapos : 0 < a := mul_pos hpos (hp i)
        have hbpos : 0 < b := mul_pos hpos (hq i)
        have hx : 0 < a * B / (b * A) := by positivity
        have hlog := one_sub_inv_le_log hx
        have hexp : Real.log (a * B / (b * A))
            = (Real.log (p i) - Real.log (q i)) - (Real.log A - Real.log B) := by
          rw [Real.log_div (by positivity) (by positivity), Real.log_mul hapos.ne' hBpos.ne',
            Real.log_mul hbpos.ne' hApos.ne', ha, hb,
            Real.log_mul hpos.ne' (hp i).ne', Real.log_mul hpos.ne' (hq i).ne']
          ring
        rw [hexp] at hlog
        have h2 : a * (1 - 1 / (a * B / (b * A))) = a - b * (A / B) := by
          field_simp
        nlinarith [mul_le_mul_of_nonneg_left hlog hapos.le]
    have hsum := Finset.sum_le_sum step
    have hL : ∑ i, (T j i * p i - T j i * q i * (A / B)) = A - B * (A / B) := by
      rw [Finset.sum_sub_distrib, ← hA, ← Finset.sum_mul, ← hB]
    have hR : ∑ i, (T j i * p i * (Real.log (p i) - Real.log (q i))
        - T j i * p i * (Real.log A - Real.log B))
        = (∑ i, T j i * p i * (Real.log (p i) - Real.log (q i)))
          - A * (Real.log A - Real.log B) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← hA]
    rw [hL, hR] at hsum
    have hBA : B * (A / B) = A := by
      rw [mul_comm, div_mul_cancel₀ _ hBpos.ne']
    rw [hBA, sub_self] at hsum
    linarith
  calc ∑ j, (∑ i, T j i * p i) * (Real.log (∑ i, T j i * p i) - Real.log (∑ i, T j i * q i))
      ≤ ∑ j, ∑ i, T j i * p i * (Real.log (p i) - Real.log (q i)) :=
        Finset.sum_le_sum fun j _ => key j
    _ = ∑ i, p i * (Real.log (p i) - Real.log (q i)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hcongr : ∀ j : m, T j i * p i * (Real.log (p i) - Real.log (q i))
            = T j i * (p i * (Real.log (p i) - Real.log (q i))) := fun j => by ring
        rw [Finset.sum_congr rfl (fun j _ => hcongr j), ← Finset.sum_mul, hTcol i, one_mul]

omit [Fintype n] in
