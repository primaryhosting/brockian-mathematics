/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix Finset ComplexOrder

/-! ## Classical information quantities -/

variable {ι X I Y : Type*}

/-- Shannon entropy of a finite (sub)probability vector, `H(p) = -∑ p i log (p i)`. -/

lemma log_sum_le [Fintype I] (a b : I → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hac : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) ≤ ∑ i, a i * Real.log (a i / b i) := by
  set A := ∑ i, a i with hAdef
  set B := ∑ i, b i with hBdef
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => ha i
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => hb i
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have h2 : ∑ i, a i = 0 := by rw [← hAdef]; exact hA0.symm
    have hall : ∀ i, a i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha i)).1 h2 i (Finset.mem_univ i)
    simp [hall, ← hA0]
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · exfalso
    have h2 : ∑ i, b i = 0 := by rw [← hBdef]; exact hB0.symm
    have hall : ∀ i, b i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hb i)).1 h2 i (Finset.mem_univ i)
    have : A = 0 := by
      rw [hAdef]; exact Finset.sum_eq_zero fun i _ => hac i (hall i)
    exact absurd this (ne_of_gt hApos)
  · set c := A / B with hc
    have hcpos : 0 < c := div_pos hApos hBpos
    have hcB : c * B = A := div_mul_cancel₀ A (ne_of_gt hBpos)
    have key : ∀ i ∈ (univ : Finset I),
        a i * Real.log c + (a i - c * b i) ≤ a i * Real.log (a i / b i) := by
      intro i _
      rcases eq_or_lt_of_le (ha i) with h0 | hpos
      · simp [← h0]
        exact mul_nonneg hcpos.le (hb i)
      · have hbi : 0 < b i := by
          rcases eq_or_lt_of_le (hb i) with h | h
          · exact absurd (hac i h.symm) (ne_of_gt hpos)
          · exact h
        set t := a i / (b i * c) with ht
        have htpos : 0 < t := div_pos hpos (mul_pos hbi hcpos)
        have hlog : 1 - 1 / t ≤ Real.log t := by
          have h := Real.log_le_sub_one_of_pos (x := 1 / t) (by positivity)
          rw [Real.log_div one_ne_zero (ne_of_gt htpos), Real.log_one] at h
          rw [one_div] at h ⊢
          linarith
        have hlt : Real.log t = Real.log (a i) - Real.log (b i) - Real.log c := by
          rw [ht, Real.log_div (ne_of_gt hpos) (by positivity),
            Real.log_mul (ne_of_gt hbi) (ne_of_gt hcpos)]
          ring
        have hsplit : Real.log (a i / b i) = Real.log t + Real.log c := by
          rw [hlt, Real.log_div (ne_of_gt hpos) (ne_of_gt hbi)]; ring
        rw [hsplit]
        have h1t : a i * (1 / t) = c * b i := by rw [ht]; field_simp
        have hkey : a i - c * b i ≤ a i * Real.log t := by
          have h := mul_le_mul_of_nonneg_left hlog hpos.le
          rw [mul_sub, mul_one, h1t] at h
          linarith
        nlinarith [hkey]
    calc A * Real.log c = ∑ i, (a i * Real.log c + (a i - c * b i)) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
            ← hAdef, ← hBdef, hcB]
          ring
      _ ≤ ∑ i, a i * Real.log (a i / b i) := Finset.sum_le_sum key

/-- Data-processing for the relative entropy of two nonnegative vectors under a stochastic
kernel `M`. -/
