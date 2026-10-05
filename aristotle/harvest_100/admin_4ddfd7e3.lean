/-!
# Pell 10
Category: Pure Mathematics
Target: Math.pell_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The witness pair `(19, 6)` satisfies the Pell equation for `d = 10`:
`19² - 10 · 6² = 361 - 360 = 1`. -/
theorem pell_10_witness : (19 : Int) ^ 2 - 10 * (6 : Int) ^ 2 = 1 := by decide

/-- **Pell's equation for `d = 10`.**
`x² - 10·y² = 1` has a nontrivial integer solution, i.e. a solution with `y ≠ 0`
(so it is different from the trivial solutions `(±1, 0)`).
The fundamental solution is `(x, y) = (19, 6)`. -/
theorem pell_10 : ∃ x y : Int, x ^ 2 - 10 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨19, 6, pell_10_witness, by decide⟩

end Math

import Mathlib
import RequestProject.Main

/-!
# Pell 10 — Mathlib restatement

`RequestProject/Main.lean` must begin with a fixed header comment, which in Lean 4 forces
that file to be import-free (a module docstring may not precede an `import`). The core
theorem `Math.pell_10` needs nothing beyond the Lean core `Int` API, so this is harmless;
this file records the same statement in a Mathlib context, over `ℤ`.
-/

namespace Math

/-- **Pell's equation for `d = 10`**, stated over `ℤ` in a Mathlib environment:
`x² - 10·y² = 1` has a solution with `y ≠ 0`, namely `(x, y) = (19, 6)`. -/
theorem pell_10_int : ∃ x y : ℤ, x ^ 2 - 10 * y ^ 2 = 1 ∧ y ≠ 0 := pell_10

end Math

