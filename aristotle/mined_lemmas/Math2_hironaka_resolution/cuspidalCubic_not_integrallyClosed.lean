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

theorem cuspidalCubic_not_integrallyClosed :
    ∃ x : k[X], IsIntegral (cuspidalCubic k) x ∧ x ∉ cuspidalCubic k := by
  refine ⟨X, ⟨Polynomial.X ^ 2 - Polynomial.C (⟨X ^ 2, sq_mem_cuspidalCubic k⟩ : cuspidalCubic k),
    monic_X_pow_sub_C _ (by norm_num), by simp⟩, ?_⟩
  intro h
  have hle : cuspidalCubic k ≤ noLinearCoeff k := by
    apply Algebra.adjoin_le
    rintro y (rfl | rfl) <;> simp [noLinearCoeff, Polynomial.coeff_X_pow]
  have := hle h
  simp [noLinearCoeff] at this

variable [CharZero k]

/-- The resolution of singularities applies to the (singular) cuspidal cubic. -/
