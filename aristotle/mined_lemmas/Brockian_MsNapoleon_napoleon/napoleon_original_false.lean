import Mathlib

namespace Brockian.MsNapoleon

/-!
# Napoleon's theorem (complex form)

The original statement in this file was

```

theorem napoleon_original_false :
    ¬ ∀ (a b c ω : ℂ), ω ^ 2 + ω + 1 = 0 →
      (b + c + (c - b) * (-ω)) / 3 + ω * ((c + a + (a - c) * (-ω)) / 3)
        + ω ^ 2 * ((a + b + (b - a) * (-ω)) / 3) = 0 := by
  intro h
  obtain ⟨ω, hω⟩ := exists_primitive_cube_root
  have h1 := h 1 0 0 ω hω
  have hsq : ω ^ 2 = 0 := by linear_combination -3 * h1 + ω * hω
  have hω0 : ω = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  rw [hω0] at hω
  norm_num at hω

end Brockian.MsNapoleon

