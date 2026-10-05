-- (Lean 4 requires `import` lines to precede any module docstring, so the required
-- header comment appears immediately below the import.)
import Mathlib

/-!
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-- Fermat's Last Theorem for a fixed exponent `n`, stated with *positive* integers:
there are no `x, y, z > 0` with `x ^ n + y ^ n = z ^ n`. -/

theorem FLTFor_of_dvd {m n : ℕ} (hmn : m ∣ n) (hm : FLTFor m) : FLTFor n :=
  (FLTFor_iff_fermatLastTheoremFor n).2 <|
    FermatLastTheoremFor.mono hmn ((FLTFor_iff_fermatLastTheoremFor m).1 hm)

/-- Base case `n = 3`: `x ^ 3 + y ^ 3 = z ^ 3` has no positive solution. -/
