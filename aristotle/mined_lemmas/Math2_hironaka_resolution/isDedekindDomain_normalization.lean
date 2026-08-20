/-
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
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
set_option synthInstance.maxHeartbeats 400000
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

namespace Math2

open Polynomial

attribute [local instance] FractionRing.liftAlgebra

section Curve

/-- The normalization of `A`: the integral closure of `A` inside its field of fractions. -/
noncomputable abbrev normalization (A : Type*) [CommRing A] [IsDomain A] :
    Subalgebra A (FractionRing A) :=
  integralClosure A (FractionRing A)

/-- `HasResolutionOfSingularities A` says that the affine variety `Spec A` admits a resolution of
its singularities inside its function field `K = Frac A`: there is a ring `B` with `A ⊆ B ⊆ K`
which is a finite `A`-module (so that `Spec B → Spec A` is a finite, hence proper, morphism), has
`K` as its fraction field (so that `Spec B → Spec A` is birational), and is regular, in the sense
that `B` is a Dedekind domain all of whose localizations at nonzero primes are discrete valuation
rings. -/

theorem isDedekindDomain_normalization : IsDedekindDomain ↥(normalization A) := by
  haveI := isIntegralClosure_normalization k A
  exact IsIntegralClosure.isDedekindDomain k[X] (FractionRing k[X]) (FractionRing A) _

include k in
/-- **Resolution of singularities in characteristic zero** (Hironaka), in the case of curves.

Let `k` be a field of characteristic zero and let `A` be an affine curve over `k`, presented (as
Noether normalization always allows) as a domain that is a finite module over the coordinate ring
`k[X]` of the affine line, with `k[X] → A` injective.  Write `K = Frac A` for its function field.

Then there is a ring `B` with `A ⊆ B ⊆ K` — the normalization of `A` — such that

* `B` is exactly the set of elements of `K` integral over `A`;
* `B` is finite as an `A`-module, so `Spec B → Spec A` is a finite (hence proper) morphism;
* `B` has the same fraction field `K` as `A`, so `Spec B → Spec A` is birational;
* `B` is a Dedekind domain and all of its local rings at nonzero primes are discrete valuation
  rings, i.e. `Spec B` is regular (nonsingular).

In other words, every affine curve in characteristic zero admits a resolution of its
singularities by a proper birational morphism from a regular variety. -/
