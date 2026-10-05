/-
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

/-- A real Möbius transformation `x ↦ (a x + b) / (c x + d)`.  These are exactly the
boundary values on `ℝ = ∂ℍ` of the conformal automorphisms of the upper half-plane. -/

noncomputable def cardyFunction (C : ℝ → ℝ → ℝ → ℝ → ℝ) (l : ℝ) : ℝ :=
  if h : ∃ p : ℝ × ℝ × ℝ × ℝ,
      Distinct4 p.1 p.2.1 p.2.2.1 p.2.2.2 ∧ modulus p.1 p.2.1 p.2.2.1 p.2.2.2 = l then
    C h.choose.1 h.choose.2.1 h.choose.2.2.1 h.choose.2.2.2
  else 0

/-- **Cardy–Smirnov conformal invariance.**

A crossing-probability function on conformal quadrilaterals of the half-plane (four marked
boundary points) is conformally invariant precisely when it is a function of the conformal
modulus (cross-ratio) alone.  This is the exact content of the Cardy–Smirnov theorem's
conclusion, reduced to an algebraic statement about the Möbius group: the "shape" of a quad
is captured by a single real parameter, and Cardy's formula is the resulting function `F`. -/
