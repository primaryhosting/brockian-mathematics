/-
# Catalan Closed
Category: Pure Mathematics
Target: Math.catalan_closed
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` before any module docstring `/-! ... -/`, so the
-- header above is repeated below in module-docstring form.)
import Mathlib

/-!
# Catalan Closed
Category: Pure Mathematics
Target: Math.catalan_closed
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Key Mathlib identity (`succ_mul_catalan_eq_centralBinom`), restated with
`Nat.choose (2 * n) n` in place of `Nat.centralBinom n`:
`(n + 1) * catalan n = C(2n, n)`. -/

theorem succ_mul_catalan_eq_choose (n : ℕ) :
    (n + 1) * catalan n = Nat.choose (2 * n) n :=
  succ_mul_catalan_eq_centralBinom n

/-- **Closed form for the Catalan numbers.**
The `n`-th Catalan number equals `C(2n, n) / (n + 1)`, stated over `ℚ` so that
the division is genuine division. -/
