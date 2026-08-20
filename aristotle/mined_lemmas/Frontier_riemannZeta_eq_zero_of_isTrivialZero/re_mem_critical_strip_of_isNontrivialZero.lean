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

theorem re_mem_critical_strip_of_isNontrivialZero {s : ℂ} (hs : IsNontrivialZero s) :
    0 < s.re ∧ s.re < 1 := by
  obtain ⟨hz, hnt⟩ := hs
  constructor
  · by_contra h
    exact hnt (isTrivialZero_of_re_nonpos (not_lt.mp h) hz)
  · by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz

/-- **Lean-checked reduction**: the Riemann Hypothesis is equivalent to the statement that all
zeros of `ζ` in the open critical strip `0 < Re s < 1` lie on the line `Re s = 1/2`. -/
