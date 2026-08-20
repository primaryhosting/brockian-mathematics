import Mathlib

namespace Brockian.MsNapoleon

/-!
# Napoleon's theorem (complex form)

The original statement in this file was

```

theorem napoleon (a b c : ℂ) (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    let g₁ := (b + c + apex ω b c) / 3
    let g₂ := (c + a + apex ω c a) / 3
    let g₃ := (a + b + apex ω a b) / 3
    g₁ + ω * g₂ + ω ^ 2 * g₃ = 0 := by
  simp only [apex]
  linear_combination ((a * ω - b * ω + 2 * b + c) / 3) * hω

/-- A primitive cube root of unity exists in `ℂ`. -/
