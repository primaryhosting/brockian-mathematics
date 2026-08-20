import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The full Catalan–Mihăilescu theorem, as a statement (it is *not* proved in this file):
the only pair of consecutive perfect powers is `8 = 2 ^ 3` and `9 = 3 ^ 2`. -/

def CatalanMihailescuStatement : Prop :=
  ∀ x y p q : ℕ, 1 < x → 1 < y → 1 < p → 1 < q → x ^ p - y ^ q = 1 →
    x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3

/-! ### Elementary auxiliary estimates and identities -/

/-- A crude but sufficient strict growth estimate: `(b+1) ^ n` exceeds `b ^ n` by at least
`2 * b + 1` as soon as `n ≥ 2`. -/
