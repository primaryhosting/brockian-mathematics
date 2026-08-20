import Mathlib

namespace Brockian.MsNapoleon

/-!
# Napoleon's theorem (complex form)

The original statement in this file was

```

def apex (ω p q : ℂ) : ℂ := p + (q - p) * (-ω)

/-- Napoleon's theorem (complex form): the centroids of the outward equilateral triangles
erected on the sides of any triangle `a, b, c ∈ ℂ` themselves form an equilateral triangle.
With `ω` a primitive cube root of unity (`ω ^ 2 + ω + 1 = 0`), the three centroids
`g₁, g₂, g₃` satisfy the standard equilaterality criterion `g₁ + ω * g₂ + ω ^ 2 * g₃ = 0`. -/
