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

/-
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A Hilbert–Pólya style scaffold: a *Brockian system* is a complex inner product space equipped
with a symmetric operator whose point spectrum contains the spectral parameter
`-i (ρ - 1/2)` of every nontrivial zero `ρ` of the Riemann zeta function.  The main theorem
`Brockian.RiemannScaffold.RH_of_BrockianSystem` shows that the existence of such a system
implies the Riemann hypothesis, with no further hypotheses.
-/

open scoped BigOperators
open scoped Real
open scoped Classical
open scoped InnerProductSpace

set_option maxHeartbeats 1000000

namespace Brockian.RiemannScaffold

open Complex

/-- The *Brockian spectral parameter* attached to a complex number `s`, namely `-i (s - 1/2)`.
It is real exactly when `s` lies on the critical line. -/

theorem mulOp_apply (f : ℝ →₀ ℂ) (x : ℝ) : (mulOp f) x = (x : ℂ) * f x := by
  have h1 : mulOp f = f.sum (fun t a => Finsupp.single t ((t : ℂ) * a)) := by
    simp [mulOp, Finsupp.lsum_apply, Finsupp.sum]
  rw [h1, Finsupp.sum, Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  by_cases hx : x ∈ f.support
  · rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd hx h
  · have hf : f x = 0 := Finsupp.notMem_support_iff.mp hx
    rw [hf, mul_zero]
    refine Finset.sum_eq_zero ?_
    intro b hb
    have hbx : b ≠ x := by rintro rfl; exact hx hb
    simp [hbx]

