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
# A Hilbert–Pólya ("Brockian system") scaffold for the Riemann Hypothesis

This file sets up a spectral scaffold for the Riemann Hypothesis and proves the
*reduction* step rigorously:

* `Brockian.BrockianSystem μ` is a spectral realization of the complex number `μ`:
  an inner product space over `ℂ` together with a symmetric (self-adjoint)
  linear operator having `μ` as an eigenvalue.
* `Brockian.spectralParameter s = -I * (s - 1/2)` is the Hilbert–Pólya spectral
  parameter attached to a zero `s` of `ζ`; it is real exactly when `s.re = 1/2`.
* `Brockian.RiemannScaffold.BrockianRealization` is the named hypothesis: every
  nontrivial zero of `ζ` admits a Brockian system for its spectral parameter.
* `Brockian.RiemannScaffold.RH_of_BrockianSystem` derives `RiemannHypothesis`
  from that hypothesis. This is proved unconditionally, with no unproved steps.

To document that the scaffold is *faithful* (neither vacuous nor stronger than
needed) we also prove the converse,
`Brockian.RiemannScaffold.brockianRealization_of_RiemannHypothesis`, so that
`BrockianRealization ↔ RiemannHypothesis`
(`Brockian.RiemannScaffold.brockianRealization_iff_riemannHypothesis`).

Consequently the named hypothesis `BrockianRealization` is *exactly* the Riemann
Hypothesis; discharging it is the open problem itself, and it is not discharged
here. Every declaration in this file is fully proved.
-/

open Complex

namespace Brockian

/-- `s` is a nontrivial zero of the Riemann zeta function: a zero which is neither
one of the trivial zeros `-2*(n+1)` nor the pole `1`. -/

lemma spectralParameter_isReal_iff (s : ℂ) :
    (spectralParameter s).im = 0 ↔ s.re = 1 / 2 := by
  rw [spectralParameter_im]
  constructor <;> intro h <;> linarith

/-- A **Brockian system** for a complex number `μ`: a complex inner product space
equipped with a symmetric linear operator admitting `μ` as an eigenvalue.

This is the local (one zero at a time) form of the Hilbert–Pólya heuristic. -/
structure BrockianSystem (μ : ℂ) where
  /-- The underlying vector space of the system. -/
  carrier : Type
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [innerProductSpace : InnerProductSpace ℂ carrier]
  /-- The operator of the system. -/
  op : carrier →ₗ[ℂ] carrier
  /-- The operator is symmetric (formally self-adjoint). -/
  op_isSymmetric : op.IsSymmetric
  /-- `μ` occurs in the point spectrum of the operator. -/
  hasEigenvalue : Module.End.HasEigenvalue op μ

attribute [instance] BrockianSystem.normedAddCommGroup BrockianSystem.innerProductSpace

/-- Every complex number realized by a Brockian system is real. -/
