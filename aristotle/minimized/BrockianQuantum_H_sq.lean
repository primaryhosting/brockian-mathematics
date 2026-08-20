import Mathlib
/-!
# Batch 2 — Hadamard gate & basis change. All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

noncomputable def hc : ℂ := (Real.sqrt 2 : ℂ)⁻¹
/-- Hadamard. -/ noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ := !![hc, hc; hc, -hc]

private lemma hc_mul_hc : hc * hc = 1 / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [hc, ← mul_inv, h2]
  norm_num

private lemma hc_sq : hc ^ 2 = 1 / 2 := by rw [pow_two, hc_mul_hc]

/-- `hc` is real, hence fixed by complex conjugation. -/
