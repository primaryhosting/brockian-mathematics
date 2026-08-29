import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex
open scoped Real

namespace Frontier

/-- `s` is a *trivial* zero of the Riemann zeta function, i.e. `s = -2, -4, -6, …`. -/

theorem isNontrivialZero_mem_criticalStrip {s : ℂ} (h : IsNontrivialZero s) :
    0 < s.re ∧ s.re < 1 := by
  obtain ⟨hz, hnt⟩ := h
  refine ⟨?_, ?_⟩
  · by_contra hle
    exact hnt (isTrivialZero_of_zeta_eq_zero_of_re_nonpos (not_lt.mp hle) hz)
  · by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hz

/-- **Lean-checked reduction of the Riemann hypothesis to the critical strip.**

The full statement — all nontrivial zeros of `ζ` have real part `1/2` — is equivalent to its
restriction to the critical strip `0 < Re s < 1`.  The nontrivial content is that outside the
strip the zeros of `ζ` are completely understood: `ζ` does not vanish on `Re s ≥ 1`, and on
`Re s ≤ 0` its only zeros are the trivial ones `-2, -4, -6, …`. -/
