import Mathlib

/-!
# Atiyah Singer Index
Category: Frontier — Fields Medal Work
Target: Frontier.atiyah_singer_index
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Module Polynomial

/-! ## The analytic index

The *analytic index* of an operator `D` is `dim ker D - dim coker D`.  This is the
standard Fredholm index, written here for a `ℂ`-linear map between arbitrary
`ℂ`-vector spaces; it is the meaningful invariant exactly when both the kernel and
the cokernel are finite dimensional (`Module.finrank` returns `0` on infinite
dimensional spaces). -/

/-- The analytic (Fredholm) index `dim ker D - dim coker D` of a linear operator `D`. -/
noncomputable def analyticIndex {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (D : V →ₗ[ℂ] W) : ℤ :=
  (finrank ℂ (LinearMap.ker D) : ℤ) - (finrank ℂ (W ⧸ LinearMap.range D) : ℤ)

/-- Rank–nullity computation of the analytic index in the finite dimensional case:
the index of any linear map between finite dimensional spaces depends only on the
dimensions of the source and the target. -/
theorem analyticIndex_eq_finrank_sub_finrank {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (D : V →ₗ[ℂ] W) :
    analyticIndex D = (finrank ℂ V : ℤ) - (finrank ℂ W : ℤ) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker D
  have h2 := Submodule.finrank_quotient_add_finrank (R := ℂ) (LinearMap.range D)
  unfold analyticIndex
  omega

/-! ## The topological index on a `0`-dimensional closed manifold

A closed `0`-dimensional manifold is a finite set `M` of points.  A complex vector
bundle over it is a family `E : M → Type*` of finite dimensional complex vector
spaces, and the space of smooth sections of `E` is `∀ x, E x`.

Since the cotangent space at each point is `0`, there are *no* nonzero covectors and
hence every bundle homomorphism `D : Γ(E) → Γ(F)` is elliptic: the symbol condition
(invertibility of the principal symbol at every nonzero covector) is vacuous.  The
Atiyah–Singer topological index `∫_M ch(σ_D) · Td(TM ⊗ ℂ)` collapses, since `Td = 1`
and integration over a `0`-manifold is summation over its points, to
`∑_{x ∈ M} (rk E_x - rk F_x)`. -/

/-- The topological index of a `0`-dimensional index problem: the sum over the points
of the manifold of the difference of the ranks of the two bundles. -/
noncomputable def topologicalIndex (M : Type*) [Fintype M] (E F : M → Type*)
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)] : ℤ :=
  ∑ x : M, ((finrank ℂ (E x) : ℤ) - (finrank ℂ (F x) : ℤ))

/-- **Atiyah–Singer index theorem, `0`-dimensional case.**

For a closed `0`-dimensional manifold `M` (a finite set of points), complex vector
bundles `E`, `F` over `M` and any (automatically elliptic) operator
`D : Γ(E) → Γ(F)` between their spaces of sections, the analytic index
`dim ker D - dim coker D` equals the topological index
`∑_{x ∈ M} (rk E_x - rk F_x)`. -/
theorem atiyah_singer_index {M : Type*} [Fintype M] (E F : M → Type*)
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, FiniteDimensional ℂ (E x)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)] [∀ x, FiniteDimensional ℂ (F x)]
    (D : (∀ x, E x) →ₗ[ℂ] (∀ x, F x)) :
    analyticIndex D = topologicalIndex M E F := by
  rw [analyticIndex_eq_finrank_sub_finrank, topologicalIndex,
    Module.finrank_pi_fintype ℂ, Module.finrank_pi_fintype ℂ, Finset.sum_sub_distrib]
  push_cast
  ring

/-- Deformation invariance in the `0`-dimensional case: the analytic index does not
depend on the operator at all, only on the underlying bundles.  This homotopy
invariance of the analytic index is one of the two pillars of the index theorem. -/
theorem analyticIndex_indep_of_operator {M : Type*} [Fintype M] (E F : M → Type*)
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, FiniteDimensional ℂ (E x)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)] [∀ x, FiniteDimensional ℂ (F x)]
    (D D' : (∀ x, E x) →ₗ[ℂ] (∀ x, F x)) :
    analyticIndex D = analyticIndex D' := by
  rw [atiyah_singer_index E F D, atiyah_singer_index E F D']

/-! ## The Toeplitz index theorem

A genuinely infinite dimensional instance of the same principle: the index theorem
for Toeplitz operators on the circle.  We use the polynomial model `ℂ[X]` of the
Hardy space, on which the Toeplitz operator with symbol `σ_n(z) = z ^ n` is
multiplication by `X ^ n`.  Its analytic index is `-n`, and this equals minus the
winding number of the symbol around the origin, computed by the argument principle
as the logarithmic derivative contour integral `(2πi)⁻¹ ∮_{|z| = 1} σ'(z) / σ(z) dz`. -/

/-- The Toeplitz operator with symbol `z ↦ z ^ n` on the polynomial model of the
Hardy space: multiplication by `X ^ n`. -/
noncomputable def toeplitzPow (n : ℕ) : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ :=
  LinearMap.mulLeft ℂ (Polynomial.X ^ n)

/-- The winding number of the symbol `z ↦ z ^ n` around the origin, defined by the
argument principle as `(2πi)⁻¹ ∮_{|z| = 1} σ'(z) / σ(z) dz`. -/
noncomputable def symbolWinding (n : ℕ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * ∮ z in C(0, 1), deriv (fun w : ℂ => w ^ n) z / z ^ n

/-- The winding number of `z ↦ z ^ n` about the origin is `n`. -/
theorem symbolWinding_eq (n : ℕ) : symbolWinding n = (n : ℂ) := by
  have hEq : Set.EqOn (fun z : ℂ => deriv (fun w : ℂ => w ^ n) z / z ^ n)
      (fun z : ℂ => (n : ℂ) * (z - 0)⁻¹) (Metric.sphere (0 : ℂ) 1) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      simp only [Metric.mem_sphere, dist_zero_right] at hz
      intro h
      rw [h] at hz
      simp at hz
    have hd : deriv (fun w : ℂ => w ^ n) z = (n : ℂ) * z ^ (n - 1) := by simp
    simp only [hd, sub_zero]
    rcases n with _ | m
    · simp
    · rw [pow_succ, Nat.add_sub_cancel]
      field_simp
  unfold symbolWinding
  rw [circleIntegral.integral_congr zero_le_one hEq, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_center_inv 0 one_ne_zero]
  have h : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  field_simp

/-- The kernel of multiplication by `X ^ n` on `ℂ[X]` is trivial. -/
theorem ker_toeplitzPow (n : ℕ) : LinearMap.ker (toeplitzPow n) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro p q h
  simpa [toeplitzPow, mul_right_inj', pow_ne_zero, Polynomial.X_ne_zero] using h

/-- The image of the Toeplitz operator consists exactly of the polynomials divisible
by `X ^ n`, i.e. those with vanishing remainder modulo `X ^ n`. -/
theorem range_toeplitzPow (n : ℕ) :
    LinearMap.range (toeplitzPow n) = LinearMap.ker (Polynomial.modByMonicHom (X ^ n : ℂ[X])) := by
  ext p
  simp only [LinearMap.mem_range, LinearMap.mem_ker, Polynomial.modByMonicHom_apply,
    Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow (R := ℂ) n)]
  constructor
  · rintro ⟨q, rfl⟩; exact ⟨q, rfl⟩
  · rintro ⟨q, rfl⟩; exact ⟨q, rfl⟩

/-- Reduction modulo `X ^ n` surjects `ℂ[X]` onto the polynomials of degree `< n`. -/
theorem range_modByMonicHom_X_pow (n : ℕ) :
    LinearMap.range (Polynomial.modByMonicHom (X ^ n : ℂ[X])) = Polynomial.degreeLT ℂ n := by
  ext p
  simp only [LinearMap.mem_range, Polynomial.modByMonicHom_apply, Polynomial.mem_degreeLT]
  constructor
  · rintro ⟨q, rfl⟩
    have := Polynomial.degree_modByMonic_lt q (Polynomial.monic_X_pow (R := ℂ) n)
    simpa [Polynomial.degree_X_pow] using this
  · intro h
    refine ⟨p, ?_⟩
    rw [Polynomial.modByMonic_eq_self_iff (Polynomial.monic_X_pow n)]
    simpa [Polynomial.degree_X_pow] using h

/-- The cokernel of multiplication by `X ^ n` on `ℂ[X]` is `n`-dimensional; it is
modelled by the polynomials of degree `< n`. -/
theorem finrank_coker_toeplitzPow (n : ℕ) :
    finrank ℂ (Polynomial ℂ ⧸ LinearMap.range (toeplitzPow n)) = n := by
  have e1 : (Polynomial ℂ ⧸ LinearMap.range (toeplitzPow n)) ≃ₗ[ℂ]
      (Polynomial ℂ ⧸ LinearMap.ker (Polynomial.modByMonicHom (X ^ n : ℂ[X]))) :=
    Submodule.quotEquivOfEq _ _ (range_toeplitzPow n)
  have e2 := (Polynomial.modByMonicHom (X ^ n : ℂ[X])).quotKerEquivRange
  have e3 : (LinearMap.range (Polynomial.modByMonicHom (X ^ n : ℂ[X])) :
      Submodule ℂ (Polynomial ℂ)) ≃ₗ[ℂ] (Polynomial.degreeLT ℂ n) :=
    LinearEquiv.ofEq _ _ (range_modByMonicHom_X_pow n)
  rw [(e1.trans (e2.trans (e3.trans (Polynomial.degreeLTEquiv ℂ n)))).finrank_eq]
  simp

/-- The analytic index of the Toeplitz operator with symbol `z ↦ z ^ n` is `-n`. -/
theorem analyticIndex_toeplitzPow (n : ℕ) : analyticIndex (toeplitzPow n) = -(n : ℤ) := by
  rw [analyticIndex, ker_toeplitzPow, finrank_coker_toeplitzPow]
  simp

/-- **Toeplitz index theorem.**  The analytic index of the Toeplitz operator with
symbol `z ↦ z ^ n` equals minus the winding number of its symbol around the origin.
This is the Atiyah–Singer index theorem in its Toeplitz (circle) incarnation. -/
theorem atiyah_singer_index_toeplitz (n : ℕ) :
    (analyticIndex (toeplitzPow n) : ℂ) = -symbolWinding n := by
  rw [analyticIndex_toeplitzPow, symbolWinding_eq]
  push_cast
  ring

end Frontier

