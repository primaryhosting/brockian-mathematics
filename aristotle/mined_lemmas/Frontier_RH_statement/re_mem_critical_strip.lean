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

theorem re_mem_critical_strip {s : ℂ} (hs : IsNontrivialZero s) : 0 < s.re ∧ s.re < 1 := by
  obtain ⟨hz, -, htriv⟩ := hs
  constructor
  · by_contra h
    push_neg at h
    have h0 : s ≠ 0 := by
      rintro rfl
      rw [riemannZeta_zero] at hz
      norm_num at hz
    exact zeta_ne_zero_of_re_nonpos h h0 htriv hz
  · by_contra h
    push_neg at h
    exact riemannZeta_ne_zero_of_one_le_re h hz

/-- The nontrivial zeros are symmetric about the critical line: `s ↦ 1 - s`. -/
