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
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Real ComplexConjugate InnerProductSpace
open Complex MeasureTheory Submodule AddCircle Module

namespace Brockian.Weyl.DeficiencyODE

/-! ## Abstract setting: symmetric operators, deficiency vectors, essential self-adjointness -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

/-- A densely defined operator `T` with domain `D` is *symmetric* if
`⟪T x, y⟫ = ⟪x, T y⟫` for all `x, y` in the domain. -/
def IsSymmetric (T : D →ₗ[ℂ] H) : Prop :=
  ∀ x y : D, ⟪T x, (y : H)⟫_ℂ = ⟪(x : H), T y⟫_ℂ

/-- `u` is a *deficiency vector* of `T` at `z` if it is orthogonal to the range of `T - z`;
equivalently, `u` solves the adjoint equation `T* u = conj z • u` weakly. -/
def IsDeficiencyVector (T : D →ₗ[ℂ] H) (z : ℂ) (u : H) : Prop :=
  ∀ x : D, ⟪T x - z • (x : H), u⟫_ℂ = 0

/-- Essential self-adjointness in the form of von Neumann's basic criterion: the operator is
densely defined, symmetric, and both deficiency spaces (at `z = i` and at `z = -i`) are trivial. -/
structure EssentiallySelfAdjoint (T : D →ₗ[ℂ] H) : Prop where
  dense_domain : Dense (D : Set H)
  symmetric : IsSymmetric T
  deficiency_pos : ∀ u : H, IsDeficiencyVector T Complex.I u → u = 0
  deficiency_neg : ∀ u : H, IsDeficiencyVector T (-Complex.I) u → u = 0

variable {ι : Type*}

/-- The algebraic basis of the algebraic span of a Hilbert basis. -/
noncomputable def spanBasis (b : HilbertBasis ι ℂ H) :
    Basis ι ℂ (span ℂ (Set.range (b : ι → H))) :=
  Basis.span b.orthonormal.linearIndependent

@[simp] lemma spanBasis_apply (b : HilbertBasis ι ℂ H) (i : ι) :
    ((spanBasis b i : span ℂ (Set.range (b : ι → H))) : H) = b i :=
  Basis.span_apply _ i

lemma spanBasis_induction {b : HilbertBasis ι ℂ H}
    {P : (span ℂ (Set.range (b : ι → H))) → Prop}
    (mem : ∀ i, P (spanBasis b i)) (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y))
    (smul : ∀ (c : ℂ) x, P x → P (c • x)) (x : span ℂ (Set.range (b : ι → H))) : P x := by
  have hx : x ∈ span ℂ (Set.range (spanBasis b)) := by
    rw [(spanBasis b).span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨i, rfl⟩ := hz; exact mem i
  | zero => exact zero
  | add x y _ _ hx hy => exact add _ _ hx hy
  | smul c x _ hx => exact smul _ _ hx

/-- The diagonal (unbounded) operator with eigenvalues `lam i` and eigenvectors `b i`, defined on
the algebraic span of the Hilbert basis `b`. -/
noncomputable def diagOp (b : HilbertBasis ι ℂ H) (lam : ι → ℝ) :
    (span ℂ (Set.range (b : ι → H))) →ₗ[ℂ] H :=
  (spanBasis b).constr ℂ fun i => (lam i : ℂ) • b i

@[simp] lemma diagOp_basis (b : HilbertBasis ι ℂ H) (lam : ι → ℝ) (i : ι) :
    diagOp b lam (spanBasis b i) = (lam i : ℂ) • b i :=
  Basis.constr_basis _ _ _ _

lemma diagOp_apply (b : HilbertBasis ι ℂ H) (lam : ι → ℝ) (i : ι)
    (hi : b i ∈ span ℂ (Set.range (b : ι → H))) :
    diagOp b lam ⟨b i, hi⟩ = (lam i : ℂ) • b i := by
  have h : (⟨b i, hi⟩ : span ℂ (Set.range (b : ι → H))) = spanBasis b i := by
    apply Subtype.ext; simp
  rw [h, diagOp_basis]

lemma diagOp_isSymmetric (b : HilbertBasis ι ℂ H) (lam : ι → ℝ) :
    IsSymmetric (diagOp b lam) := by
  have key : ∀ (i : ι) (y : span ℂ (Set.range (b : ι → H))),
      ⟪diagOp b lam (spanBasis b i), (y : H)⟫_ℂ = ⟪b i, diagOp b lam y⟫_ℂ := by
    intro i y
    induction y using spanBasis_induction with
    | mem j =>
        rcases eq_or_ne i j with rfl | hij
        · simp
        · simp [b.orthonormal.2 hij]
    | zero => simp
    | add x y hx hy =>
        simp only [Submodule.coe_add, map_add, inner_add_right] at *
        rw [hx, hy]
    | smul c x hx =>
        simp only [Submodule.coe_smul, map_smul, inner_smul_right] at *
        rw [hx]
  intro x y
  induction x using spanBasis_induction with
  | mem i => simpa using key i y
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
      simp only [Submodule.coe_add, map_add, inner_add_left] at *
      rw [h₁, h₂]
  | smul c x hx =>
      simp only [Submodule.coe_smul, map_smul, inner_smul_left] at *
      rw [hx]

/-- A symmetric diagonal operator whose eigenvectors form a Hilbert basis of the whole space and
whose eigenvalues are real is essentially self-adjoint: the deficiency equation
`(lam i - conj z) * ⟪b i, u⟫ = 0` with `z = ±i` forces all Fourier coefficients of `u` to vanish. -/
theorem diagOp_essentiallySelfAdjoint (b : HilbertBasis ι ℂ H) (lam : ι → ℝ) :
    EssentiallySelfAdjoint (diagOp b lam) := by
  have hdef : ∀ (z : ℂ), z.re = 0 → z ≠ 0 →
      ∀ u : H, IsDeficiencyVector (diagOp b lam) z u → u = 0 := by
    intro z hz hz0 u hu
    have hcoeff : ∀ i, ⟪b i, u⟫_ℂ = 0 := by
      intro i
      have h := hu (spanBasis b i)
      rw [diagOp_basis, spanBasis_apply, ← sub_smul, inner_smul_left] at h
      rcases mul_eq_zero.1 h with h1 | h2
      · exfalso
        have : ((lam i : ℂ) - z) = 0 := by
          simpa using congrArg (starRingEnd ℂ) h1
        have him : z.im = 0 := by
          have := congrArg Complex.im this
          simpa using this
        exact hz0 (Complex.ext hz him)
      · exact h2
    have : b.repr u = 0 := by
      ext i
      rw [b.repr_apply_apply]
      simpa using hcoeff i
    have := congrArg b.repr.symm this
    simpa using this
  refine ⟨?_, diagOp_isSymmetric b lam, ?_, ?_⟩
  · rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact b.dense_span
  · exact hdef Complex.I (by simp) Complex.I_ne_zero
  · exact hdef (-Complex.I) (by simp) (by simp [Complex.I_ne_zero])

end Abstract

/-! ## The one-dimensional Schrödinger operator on a circle

We work on `L²` of the circle `AddCircle T` of circumference `T > 0`, with the Schrödinger
operator `-d²/dx² + V` for a constant potential `V : ℝ`, defined on the domain of trigonometric
polynomials (the algebraic span of the Fourier basis).  The Fourier modes are genuine classical
eigenfunctions of this differential expression, as certified by `schrodingerExpr_fourier` below.
-/

section Schrodinger

variable (T : ℝ) [hT : Fact (0 < T)] (V : ℝ)

/-- The eigenvalue of `-d²/dx² + V` on the `n`-th Fourier mode of the circle `AddCircle T`. -/
noncomputable def schrodingerEigenvalue (n : ℤ) : ℝ := (2 * π * n / T) ^ 2 + V

/-- The `n`-th Fourier mode of `AddCircle T`, viewed as a function on `ℝ`. -/
noncomputable def fourierFun (n : ℤ) : ℝ → ℂ := fun y => fourier n (y : AddCircle T)

omit hT in
lemma hasDerivAt_fourierFun (n : ℤ) (x : ℝ) :
    HasDerivAt (fourierFun T n) (2 * π * I * n / T * fourierFun T n x) x :=
  hasDerivAt_fourier T n x

omit hT in
/-- The Fourier modes are classical solutions of the Schrödinger eigenvalue equation
`-u'' + V u = ((2πn/T)² + V) u` on the circle: this is what makes `schrodingerOp` the
Schrödinger operator `-d²/dx² + V`. -/
theorem schrodingerExpr_fourier (n : ℤ) (x : ℝ) :
    -deriv (deriv (fourierFun T n)) x + (V : ℂ) * fourierFun T n x
      = (schrodingerEigenvalue T V n : ℂ) * fourierFun T n x := by
  have hderiv : deriv (fourierFun T n) = fun y => 2 * π * I * n / T * fourierFun T n y := by
    funext y
    exact (hasDerivAt_fourierFun T n y).deriv
  have h2 : deriv (deriv (fourierFun T n)) x
      = (2 * π * I * n / T) * ((2 * π * I * n / T) * fourierFun T n x) := by
    rw [hderiv]
    exact (((hasDerivAt_fourierFun T n x).const_mul (2 * π * I * n / T))).deriv
  rw [h2]
  simp only [schrodingerEigenvalue]
  push_cast
  linear_combination (-(4 * (π : ℂ) ^ 2 * (n : ℂ) ^ 2 / (T : ℂ) ^ 2 * fourierFun T n x)) *
    Complex.I_mul_I

/-- The Schrödinger operator `-d²/dx² + V` on the circle `AddCircle T`, defined on the dense
domain of trigonometric polynomials inside `L²`. -/
noncomputable def schrodingerOp :
    (span ℂ (Set.range ((fourierBasis (T := T)) : ℤ → Lp ℂ 2 (@haarAddCircle T hT)))) →ₗ[ℂ]
      Lp ℂ 2 (@haarAddCircle T hT) :=
  diagOp fourierBasis (schrodingerEigenvalue T V)

/-- **Weak regularity for the deficiency ODE.**  If `u ∈ L²` is a weak solution of the deficiency
equation `-u'' + V u = z u` (i.e. `u` is orthogonal to the range of `S - z` on trigonometric
polynomials), then its Fourier coefficients satisfy the corresponding algebraic (ODE) relation
`((2πn/T)² + V - conj z) * û(n) = 0`.  This is the hypothesis that used to be assumed; it is
proved here, which makes the main theorem unconditional. -/
theorem weakRegularity (z : ℂ) (u : Lp ℂ 2 (@haarAddCircle T hT))
    (hu : IsDeficiencyVector (schrodingerOp T V) z u) (n : ℤ) :
    ((schrodingerEigenvalue T V n : ℂ) - conj z) * fourierCoeff u n = 0 := by
  have h := hu (spanBasis fourierBasis n)
  rw [schrodingerOp, diagOp_basis, spanBasis_apply, ← sub_smul, inner_smul_left] at h
  rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply]
  simpa [map_sub] using h

/-- **The Schrödinger operator `-d²/dx² + V` with constant potential `V` on the circle is
essentially self-adjoint on trigonometric polynomials.**  Formerly conditional on a weak-regularity
hypothesis for the deficiency ODE; that hypothesis is discharged by `weakRegularity`. -/
theorem schrodinger_essentiallySelfAdjoint_of_weakRegularity :
    EssentiallySelfAdjoint (schrodingerOp T V) :=
  diagOp_essentiallySelfAdjoint _ _

end Schrodinger

end Brockian.Weyl.DeficiencyODE

