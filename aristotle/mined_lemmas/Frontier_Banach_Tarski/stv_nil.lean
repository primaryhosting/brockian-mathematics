import Mathlib

/-!
# Arithmetic core for the freeness of two rotations of `SO(3)`

We consider the two rotations of `ℝ³`

```
σ = 1/3 * ![![1, -2√2, 0], ![2√2, 1, 0], ![0,0,3]]      (rotation about the z-axis)
τ = 1/3 * ![![3, 0, 0], ![0, 1, -2√2], ![0, 2√2, 1]]    (rotation about the x-axis)
```

both by the angle `arccos (1/3)`.  Applying a word of length `n` in `σ^{±1}, τ^{±1}` to the
vector `(1, 0, 1)` produces a vector of the form `3⁻ⁿ • (a, b√2, c)` with `a b c : ℤ`.
This file contains the purely arithmetic heart of the matter: for a nonempty *reduced* word,
the middle coordinate `b` is not divisible by `3`; in particular it is nonzero.
-/

namespace BanachTarski

/-- A letter: the first component selects the generator (`false` = `σ`, `true` = `τ`),
the second component is the sign of the exponent (`true` = `+1`). -/
abbrev Ltr := Bool × Bool

/-- The action of a letter on the integer triple `(a, b, c)` representing the vector
`3⁻ⁿ • (a, b√2, c)`; the factor `3⁻¹` is not recorded here. -/

@[simp] theorem stv_nil : stv [] = (1, 0, 1) := rfl

