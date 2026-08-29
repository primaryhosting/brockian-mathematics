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

noncomputable def brockianCore : InnerProductSpace.Core ℂ BrockianSpace where
  conj_inner_symm x y := fsInner_conj_symm x y
  re_inner_nonneg x := fsInner_self_nonneg x
  add_left x y z := fsInner_add_left x y z
  smul_left x y r := fsInner_smul_left x y r
  definite x h := fsInner_definite x h

noncomputable instance : NormedAddCommGroup BrockianSpace := brockianCore.toNormedAddCommGroup
noncomputable instance : InnerProductSpace ℂ BrockianSpace := .ofCore brockianCore.1

/-- On the critical line the spectral parameter is the (real) imaginary part. -/
