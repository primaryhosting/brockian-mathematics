/-
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 requires `import` commands to
-- precede any module docstring; the docstring form is repeated immediately after the import.)

import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real

namespace Frontier

/-
The Riemann Hypothesis itself is an open problem, so `RH_statement` is *stated* here (and shown
to agree with Mathlib's `RiemannHypothesis`) rather than proved. What is proved below,
unconditionally and axiom-cleanly, is:

* the zero-free regions `Re s ≤ 0` (only trivial zeros) and `Re s ≥ 1` (no zeros), i.e. every
  nontrivial zero lies in the critical strip `0 < Re s < 1`;
* the symmetry `s ↦ 1 - s` of the set of nontrivial zeros, coming from the functional equation;
* the resulting reduction: RH is equivalent to the one-sided statement that no nontrivial zero
  has `Re s > 1/2` (and, symmetrically, to `Re s < 1/2` being excluded).
-/

/-- A complex number `s` is a *nontrivial zero* of the Riemann zeta function if `ζ s = 0`,
`s` is not one of the trivial zeros `-2, -4, -6, …`, and `s ≠ 1` (the point `s = 1` is a pole,
where Mathlib's `riemannZeta` takes a junk value). -/

theorem RH_statement_iff_half_le :
    RH_statement ↔ ∀ s : ℂ, IsNontrivialZero s → 1 / 2 ≤ s.re := by
  constructor
  · intro h s hs
    exact le_of_eq (h s hs).symm
  · intro h s hs
    have h1 := h s hs
    have h2 := h (1 - s) (isNontrivialZero_one_sub hs)
    have hre : (1 - s).re = 1 - s.re := by simp
    rw [hre] at h2
    linarith

end Frontier

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

