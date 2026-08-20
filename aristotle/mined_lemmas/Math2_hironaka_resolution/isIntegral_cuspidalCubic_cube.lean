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

lemma isIntegral_cuspidalCubic_cube :
    IsIntegral k[X] (⟨X ^ 3, cube_mem_cuspidalCubic k⟩ : cuspidalCubic k) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (X ^ 3 : k[X]),
    monic_X_pow_sub_C _ (by norm_num), ?_⟩
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C]
  apply Subtype.ext
  push_cast
  simp [cuspidalCubic_algebraMap_coe, ← pow_mul]

instance : Algebra.IsIntegral k[X] (cuspidalCubic k) := by
  constructor
  intro x
  have htop : Algebra.adjoin k ((cuspidalCubic k).val ⁻¹' {X ^ 2, X ^ 3}) = ⊤ :=
    Algebra.adjoin_adjoin_coe_preimage
  have hx : x ∈ Algebra.adjoin k ((cuspidalCubic k).val ⁻¹' {X ^ 2, X ^ 3}) :=
    htop ▸ Algebra.mem_top
  have hle : Algebra.adjoin k ((cuspidalCubic k).val ⁻¹' {X ^ 2, X ^ 3}) ≤
      Subalgebra.restrictScalars k (integralClosure k[X] (cuspidalCubic k)) := by
    apply Algebra.adjoin_le
    rintro y hy
    have hy' : (y : k[X]) = X ^ 2 ∨ (y : k[X]) = X ^ 3 := by simpa using hy
    have : y = (⟨X ^ 2, sq_mem_cuspidalCubic k⟩ : cuspidalCubic k) ∨
        y = (⟨X ^ 3, cube_mem_cuspidalCubic k⟩ : cuspidalCubic k) := by
      rcases hy' with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    rcases this with rfl | rfl
    · exact isIntegral_cuspidalCubic_sq k
    · exact isIntegral_cuspidalCubic_cube k
  exact hle hx

instance : Algebra.FiniteType k[X] (cuspidalCubic k) := by
  have : Algebra.FiniteType k (cuspidalCubic k) :=
    Algebra.FiniteType.adjoin_of_finite (Set.toFinite _)
  exact Algebra.FiniteType.of_restrictScalars_finiteType k k[X] (cuspidalCubic k)

instance : Module.Finite k[X] (cuspidalCubic k) := Algebra.IsIntegral.finite

instance : FaithfulSMul k[X] (cuspidalCubic k) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  have h2 : Transcendental k ((X : k[X]) ^ 2) := (transcendental_X k).pow (by norm_num)
  have h3 : Function.Injective (Polynomial.aeval ((X : k[X]) ^ 2) : k[X] →ₐ[k] k[X]) :=
    transcendental_iff_injective.mp h2
  intro a b hab
  apply h3
  have := congrArg (fun y : cuspidalCubic k => (y : k[X])) hab
  simpa [cuspidalCubic_algebraMap_coe] using this

/-- The polynomials with vanishing linear coefficient form a subalgebra of `k[t]`. -/
