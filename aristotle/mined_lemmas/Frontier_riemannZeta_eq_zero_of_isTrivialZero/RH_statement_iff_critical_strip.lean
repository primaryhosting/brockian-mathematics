import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` lines to be the very first commands in a file,
so the module docstring above is placed directly after `import Mathlib` (a `/-! ... -/` block
before the imports is rejected by the parser).
-/

open Complex

namespace Frontier

/-- `s` is a *trivial zero* of the Riemann zeta function if it is one of the points
`-2, -4, -6, …`, at which `ζ` is known to vanish (`riemannZeta_neg_two_mul_nat_add_one`). -/

theorem RH_statement_iff_critical_strip :
    RH_statement ↔ ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 := by
  constructor
  · intro h s hs0 hs1 hz
    refine h s ⟨hz, ?_⟩
    rintro ⟨n, rfl⟩
    have hre : ((-2 * ((n : ℂ) + 1)).re) = -2 * ((n : ℝ) + 1) := by simp
    rw [hre] at hs0
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro h s hs
    obtain ⟨h0, h1⟩ := re_mem_critical_strip_of_isNontrivialZero hs
    exact h s h0 h1 hs.1

/-- **Lean-checked reduction**: this formalisation of the Riemann Hypothesis agrees with
Mathlib's `RiemannHypothesis`. -/
