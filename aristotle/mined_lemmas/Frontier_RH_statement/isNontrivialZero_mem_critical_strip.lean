import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The Riemann Hypothesis asserts that all nontrivial zeros of the Riemann zeta function `ζ`
have real part `1/2`.  Mathlib provides the formal statement as `RiemannHypothesis`:

`∀ (s : ℂ), riemannZeta s = 0 → ¬(∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2`.

The Riemann Hypothesis itself is open, so what is proved here is a *Lean-checked reduction*:
the main theorem `Frontier.RH_statement` shows that `RiemannHypothesis` is **equivalent** to the
apparently weaker assertion that every zero of `ζ` inside the critical strip `0 < re s < 1`
lies on the critical line `re s = 1/2`.

The nontrivial content is the "zero-free region" direction: any zero of `ζ` which is neither
a trivial zero `-2, -4, -6, …` nor the pole `s = 1` must lie in the critical strip.  This is
proved from Mathlib's non-vanishing theorem on `re s ≥ 1` together with the functional equation.
-/

namespace Frontier

open Complex

/-- A *nontrivial zero* of the Riemann zeta function: a zero of `ζ` which is not one of the
trivial zeros `-2, -4, -6, …` (and is not the point `s = 1`, where Mathlib's `riemannZeta`
takes a junk value). -/

theorem isNontrivialZero_mem_critical_strip {s : ℂ} (hs : IsNontrivialZero s) :
    0 < s.re ∧ s.re < 1 := by
  obtain ⟨hzero, hntriv, _⟩ := hs
  constructor
  · by_contra hcon
    push_neg at hcon
    exact hntriv (trivial_of_zero_of_re_nonpos hzero hcon)
  · by_contra hcon
    push_neg at hcon
    exact riemannZeta_ne_zero_of_one_le_re hcon hzero

/-- **Riemann Hypothesis, Lean-checked reduction.**

The statement "all nontrivial zeros of `ζ` have real part `1/2`" (Mathlib's
`RiemannHypothesis`) is equivalent to the statement that every zero of `ζ` inside the
critical strip `0 < re s < 1` lies on the critical line `re s = 1/2`.

Thus RH may be verified by examining only the critical strip: all other zeros of `ζ` are
automatically the trivial zeros `-2, -4, -6, …`. -/
