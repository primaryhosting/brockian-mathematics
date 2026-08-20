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

(The header block is placed immediately after the single `import Mathlib` line, since Lean 4
requires `import` commands to precede any module docstring.)
-/

open Complex

namespace Frontier

/-- `s` is a *nontrivial zero* of the Riemann zeta function: a zero of `ζ` which is neither
the pole `s = 1` (where Mathlib's `riemannZeta` takes a junk value) nor one of the trivial
zeros `s = -2, -4, -6, …`. -/

theorem RH_statement :
    [ RiemannHypothesis
    , ∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2
    , ∀ s : ℂ, IsNontrivialZero s → s.re ≤ 1 / 2
    , ∀ s : ℂ, IsNontrivialZero s → 1 / 2 ≤ s.re ].TFAE := by
  tfae_have 1 ↔ 2 := RH_iff_RiemannHypothesis.symm
  tfae_have 2 → 3 := fun h s hs => (h s hs).le
  tfae_have 2 → 4 := fun h s hs => (h s hs).ge
  tfae_have 3 → 2 := by
    intro h s hs
    have h1 := h s hs
    have h2 := h (1 - s) (isNontrivialZero_one_sub hs)
    simp only [Complex.sub_re, Complex.one_re] at h2
    linarith
  tfae_have 4 → 2 := by
    intro h s hs
    have h1 := h s hs
    have h2 := h (1 - s) (isNontrivialZero_one_sub hs)
    simp only [Complex.sub_re, Complex.one_re] at h2
    linarith
  tfae_finish

end Frontier

-- Axiom check for the target theorem.
#print axioms Frontier.RH_statement

