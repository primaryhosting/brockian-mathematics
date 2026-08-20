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

theorem catalan_check :
    ∀ x ∈ Finset.range 101, ∀ p ∈ Finset.range 14, 1 < x → 1 < p → x ^ p ≤ 10000 →
      ∀ y ∈ Finset.range 101, ∀ q ∈ Finset.range 14, 1 < y → 1 < q → x ^ p = y ^ q + 1 →
        x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3 := by decide +kernel

/-- Catalan–Mihăilescu, verified for all perfect powers up to `10000`. -/
