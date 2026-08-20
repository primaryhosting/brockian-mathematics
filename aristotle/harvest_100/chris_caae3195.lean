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
def HasResolutionOfSingularities (A : Type*) [CommRing A] [IsDomain A] : Prop :=
  ∃ B : Subalgebra A (FractionRing A),
    (∀ x : FractionRing A, x ∈ B ↔ IsIntegral A x) ∧
    Module.Finite A ↥B ∧
    IsFractionRing ↥B (FractionRing A) ∧
    IsDedekindDomain ↥B ∧
    ∀ (P : Ideal ↥B) [P.IsPrime], P ≠ ⊥ →
      IsDiscreteValuationRing (Localization.AtPrime P)

variable (k : Type*) [Field k] [CharZero k]
variable (A : Type*) [CommRing A] [IsDomain A] [Algebra k[X] A] [Module.Finite k[X] A]
  [FaithfulSMul k[X] A]

instance : IsScalarTower k[X] ↥(normalization A) (FractionRing A) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

omit [CharZero k] [FaithfulSMul k[X] A] in
/-- **Key intermediate lemma.** Since the affine curve `A` is finite (hence integral) over the
coordinate ring `k[X]` of the affine line, the integral closure of `A` in the function field
`Frac A` is also the integral closure of `k[X]` in `Frac A`.  This is what lets us deduce
regularity of the normalization from the fact that `k[X]` is a Dedekind domain. -/
theorem isIntegralClosure_normalization :
    IsIntegralClosure (↥(normalization A)) k[X] (FractionRing A) where
  algebraMap_injective := Subtype.coe_injective
  isIntegral_iff := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx.tower_top⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact isIntegral_trans (R := k[X]) (y : FractionRing A) y.2

include k in
/-- The normalization is module-finite over `A`: the resolution map is a finite morphism. -/
theorem finite_normalization : Module.Finite A ↥(normalization A) := by
  haveI := isIntegralClosure_normalization k A
  haveI : Module.Finite k[X] ↥(normalization A) :=
    IsIntegralClosure.finite k[X] (FractionRing k[X]) (FractionRing A) _
  exact Module.Finite.of_restrictScalars_finite k[X] A _

include k in
omit [CharZero k] in
/-- The normalization has the same field of fractions as `A`: the resolution is birational. -/
theorem isFractionRing_normalization :
    IsFractionRing ↥(normalization A) (FractionRing A) := by
  haveI := isIntegralClosure_normalization k A
  exact IsIntegralClosure.isFractionRing_of_finite_extension k[X] (FractionRing k[X])
    (FractionRing A) _

include k in
/-- The normalization of an affine curve is a Dedekind domain, i.e. it is regular. -/
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
theorem hironaka_resolution : HasResolutionOfSingularities A := by
  refine ⟨normalization A, fun _ => Iff.rfl, finite_normalization k A,
    isFractionRing_normalization k A, isDedekindDomain_normalization k A, ?_⟩
  intro P _ hP0
  haveI := isDedekindDomain_normalization k A
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (↥(normalization A)) hP0 (Localization.AtPrime P)

end Curve

section CuspidalCubic

/-!
### A worked singular example: the cuspidal cubic

The hypotheses of `Math2.hironaka_resolution` are satisfied by genuinely singular curves.  We
check this for the cuspidal cubic `y² = x³`, whose coordinate ring is `k[t², t³] ⊆ k[t]`.
-/

variable (k : Type*) [Field k]

/-- The coordinate ring `k[t², t³]` of the cuspidal cubic `y² = x³`, realised as a subalgebra of
`k[t]`. -/
noncomputable def cuspidalCubic : Subalgebra k k[X] := Algebra.adjoin k {X ^ 2, X ^ 3}

lemma sq_mem_cuspidalCubic : (X ^ 2 : k[X]) ∈ cuspidalCubic k := Algebra.subset_adjoin (by simp)

lemma cube_mem_cuspidalCubic : (X ^ 3 : k[X]) ∈ cuspidalCubic k := Algebra.subset_adjoin (by simp)

/-- The cuspidal cubic is a curve over the affine line, via `x ↦ t²`. -/
noncomputable instance cuspidalCubicAlgebra : Algebra k[X] (cuspidalCubic k) :=
  (Polynomial.aeval (⟨X ^ 2, sq_mem_cuspidalCubic k⟩ : cuspidalCubic k)).toRingHom.toAlgebra

instance : IsScalarTower k k[X] (cuspidalCubic k) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    apply Subtype.ext
    simp [cuspidalCubicAlgebra, RingHom.algebraMap_toAlgebra, Algebra.algebraMap_eq_smul_one]

lemma cuspidalCubic_algebraMap_coe (p : k[X]) :
    ((algebraMap k[X] (cuspidalCubic k) p : cuspidalCubic k) : k[X]) =
      Polynomial.aeval ((X : k[X]) ^ 2) p := by
  have h : (cuspidalCubic k).val.comp
      (Polynomial.aeval (⟨X ^ 2, sq_mem_cuspidalCubic k⟩ : cuspidalCubic k)) =
      Polynomial.aeval ((X : k[X]) ^ 2) := by
    apply Polynomial.algHom_ext; simp
  exact congrArg (fun f => f p) h

lemma isIntegral_cuspidalCubic_sq :
    IsIntegral k[X] (⟨X ^ 2, sq_mem_cuspidalCubic k⟩ : cuspidalCubic k) := by
  have h : (⟨X ^ 2, sq_mem_cuspidalCubic k⟩ : cuspidalCubic k) =
      algebraMap k[X] (cuspidalCubic k) X := by
    apply Subtype.ext; simp [cuspidalCubic_algebraMap_coe]
  rw [h]; exact isIntegral_algebraMap

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
noncomputable def noLinearCoeff : Subalgebra k k[X] where
  carrier := {p | p.coeff 1 = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [Polynomial.coeff_mul]
    simp [Finset.Nat.antidiagonal_succ, ha, hb]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    simp [ha, hb]
  algebraMap_mem' := by intro c; simp [Set.mem_setOf_eq]

/-- The cuspidal cubic is singular: the element `t` of its function field is integral over
`k[t², t³]` but does not lie in it, so `k[t², t³]` is not integrally closed. -/
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
theorem hironaka_resolution_cuspidalCubic :
    HasResolutionOfSingularities ↥(cuspidalCubic k) :=
  hironaka_resolution k (cuspidalCubic k)

end CuspidalCubic

end Math2

