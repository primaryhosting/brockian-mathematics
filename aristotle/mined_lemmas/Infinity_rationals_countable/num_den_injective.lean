import Mathlib
/-!
# Rationals Countable
Category: Frontier — Set Theory
Target: Infinity.rationals_countable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

/-- A rational number is determined by its numerator and denominator, so the map
`q ↦ (q.num, q.den)` from `ℚ` to `ℤ × ℕ` is injective. -/

theorem num_den_injective :
    Function.Injective (fun q : ℚ => (q.num, q.den)) := by
  intro p q h
  simp only [Prod.mk.injEq] at h
  exact Rat.ext h.1 h.2

/-- The rationals form a countable type.

Proved directly: `ℤ × ℕ` is countable and `q ↦ (q.num, q.den)` is an injection of `ℚ`
into it. (Mathlib also provides this instance directly.) -/
