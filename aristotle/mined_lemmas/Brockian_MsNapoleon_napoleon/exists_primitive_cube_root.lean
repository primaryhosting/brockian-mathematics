import Mathlib

namespace Brockian.MsNapoleon

/-!
# Napoleon's theorem (complex form)

The original statement in this file was

```

theorem exists_primitive_cube_root : ∃ ω : ℂ, ω ^ 2 + ω + 1 = 0 := by
  refine ⟨⟨-1 / 2, Real.sqrt 3 / 2⟩, ?_⟩
  apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_nonneg 3]

/-- The originally stated identity is false. -/
