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

theorem re_eq_half_iff_spectralParameter_im_eq_zero (s : ℂ) :
    s.re = 1 / 2 ↔ (spectralParameter s).im = 0 := by
  have h : (spectralParameter s).im = 1 / 2 - s.re := by
    simp [spectralParameter, Complex.mul_im]
  rw [h]
  constructor <;> intro h' <;> linarith

/-- A **Brockian system** is a Hilbert–Pólya style datum: a complex inner product space
together with a symmetric (formally self-adjoint) linear operator on it whose point spectrum
contains the spectral parameter `-i (ρ - 1/2)` of every nontrivial zero `ρ` of the Riemann
zeta function. -/
structure BrockianSystem where
  /-- The underlying complex inner product space. -/
  carrier : Type
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [innerProductSpace : InnerProductSpace ℂ carrier]
  /-- The Brockian operator. -/
  op : carrier →ₗ[ℂ] carrier
  /-- The Brockian operator is symmetric. -/
  op_symm : ∀ x y : carrier, ⟪op x, y⟫_ℂ = ⟪x, op y⟫_ℂ
  /-- Every nontrivial zero of `ζ` contributes an eigenvector whose eigenvalue is the
  corresponding spectral parameter. -/
  hasEigenvector : ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
    ∃ v : carrier, v ≠ 0 ∧ op v = spectralParameter s • v

attribute [instance] BrockianSystem.normedAddCommGroup BrockianSystem.innerProductSpace

/-- Eigenvalues of a symmetric operator on a complex inner product space are real. -/
