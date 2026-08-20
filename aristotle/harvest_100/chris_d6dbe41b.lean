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
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate Real
open LinearPMap Submodule

namespace Brockian.Weyl.SchrodingerMinimal

/-! ## Essential self-adjointness -/

section Abstract

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A densely defined operator `A` is *essentially self-adjoint* when it is symmetric and its
adjoint is self-adjoint (equivalently, its closure is self-adjoint; equivalently, it has a
unique self-adjoint extension, see `unique_selfAdjoint_extension`). -/
def IsEssentiallySelfAdjoint (A : E →ₗ.[ℂ] E) : Prop :=
  Dense (A.domain : Set E) ∧ A.IsFormalAdjoint A ∧ IsSelfAdjoint A.adjoint

/-- Taking adjoints is antitone. -/
theorem adjoint_le_adjoint_of_le {A B : E →ₗ.[ℂ] E} (hA : Dense (A.domain : Set E))
    (hAB : A ≤ B) : B.adjoint ≤ A.adjoint := by
  have hsub : (A.domain : Set E) ⊆ (B.domain : Set E) := fun x hx => hAB.1 hx
  have hB : Dense (B.domain : Set E) := hA.mono hsub
  refine LinearPMap.IsFormalAdjoint.le_adjoint hA ?_
  intro x y
  have hx : (x : E) ∈ B.domain := hAB.1 x.2
  have hAx : A x = B ⟨(x : E), hx⟩ := hAB.2 rfl
  rw [hAx]
  exact (LinearPMap.adjoint_isFormalAdjoint hB).symm ⟨(x : E), hx⟩ y

/-- An essentially self-adjoint operator has exactly one self-adjoint extension. -/
theorem unique_selfAdjoint_extension {A : E →ₗ.[ℂ] E} (hA : IsEssentiallySelfAdjoint A) :
    ∃! B : E →ₗ.[ℂ] E, IsSelfAdjoint B ∧ A ≤ B := by
  obtain ⟨hdense, hsym, hsa⟩ := hA
  refine ⟨A.adjoint, ⟨hsa, hsym.le_adjoint hdense⟩, ?_⟩
  rintro B ⟨hB, hAB⟩
  have hBd : Dense (B.domain : Set E) := hB.dense_domain
  have h1 : B ≤ A.adjoint := by
    have := adjoint_le_adjoint_of_le hdense hAB
    rwa [LinearPMap.isSelfAdjoint_def.mp hB] at this
  have h2 : A.adjoint ≤ B := by
    have := adjoint_le_adjoint_of_le hBd h1
    rwa [LinearPMap.isSelfAdjoint_def.mp hB, LinearPMap.isSelfAdjoint_def.mp hsa] at this
  exact le_antisymm h1 h2

/-! ## The minimal diagonal operator attached to a Hilbert basis -/

variable (b : HilbertBasis ι ℂ E) (lam : ι → ℝ)

/-- The minimal operator with eigenbasis `b` and (real) eigenvalues `lam`: it is defined on the
algebraic span of the basis vectors, where it acts by `b i ↦ lam i • b i`. -/
noncomputable def diagMin : E →ₗ.[ℂ] E where
  domain := span ℂ (Set.range b)
  toFun := (Finsupp.linearCombination ℂ fun i => (lam i : ℂ) • b i).comp
      (b.orthonormal.linearIndependent).repr

omit [CompleteSpace E] in
theorem diagMin_domain : (diagMin b lam).domain = span ℂ (Set.range b) := rfl

omit [CompleteSpace E] in
theorem basis_mem_domain (i : ι) : b i ∈ (diagMin b lam).domain :=
  subset_span ⟨i, rfl⟩

omit [CompleteSpace E] in
theorem diagMin_dense : Dense ((diagMin b lam).domain : Set E) := by
  rw [diagMin_domain, Submodule.dense_iff_topologicalClosure_eq_top]
  exact b.dense_span

omit [CompleteSpace E] in
/-- Coefficients of a finite linear combination of the (rescaled) basis vectors. -/
theorem repr_linearCombination (f : ι → ℂ) (c : ι →₀ ℂ) (i : ι) :
    b.repr (Finsupp.linearCombination ℂ (fun j => f j • b j) c) i = f i * c i := by
  classical
  rw [b.repr_apply_apply, Finsupp.linearCombination_apply, Finsupp.sum, inner_sum]
  have h : ∀ j ∈ c.support, (inner ℂ (b i) (c j • (f j • b j)) : ℂ)
      = if i = j then f i * c i else 0 := by
    intro j _
    rw [inner_smul_right, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal i j]
    by_cases hij : i = j
    · subst hij; simp; ring
    · simp [hij]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq c.support i (fun _ => f i * c i)]
  by_cases hi : i ∈ c.support
  · simp [hi]
  · have hci : c i = 0 := by simpa using hi
    simp [hi, hci]

omit [CompleteSpace E] in
theorem repr_coe (u : (diagMin b lam).domain) (i : ι) :
    b.repr (u : E) i = (b.orthonormal.linearIndependent.repr u) i := by
  conv_lhs => rw [← b.orthonormal.linearIndependent.linearCombination_repr u]
  have h : (Finsupp.linearCombination ℂ (⇑b)) (b.orthonormal.linearIndependent.repr u)
      = Finsupp.linearCombination ℂ (fun j => (1 : ℂ) • b j)
        (b.orthonormal.linearIndependent.repr u) := by simp
  rw [h, repr_linearCombination, one_mul]

omit [CompleteSpace E] in
/-- The defining action of the minimal operator on the eigenbasis. -/
theorem diagMin_apply_basis (i : ι) :
    diagMin b lam ⟨b i, basis_mem_domain b lam i⟩ = (lam i : ℂ) • b i := by
  have h : b.orthonormal.linearIndependent.repr ⟨b i, basis_mem_domain b lam i⟩
      = Finsupp.single i 1 := LinearIndependent.repr_eq _ (by simp)
  show Finsupp.linearCombination ℂ (fun j => (lam j : ℂ) • b j)
      (b.orthonormal.linearIndependent.repr ⟨b i, basis_mem_domain b lam i⟩) = _
  rw [h]
  simp

omit [CompleteSpace E] in
theorem repr_diagMin (u : (diagMin b lam).domain) (i : ι) :
    b.repr (diagMin b lam u) i = (lam i : ℂ) * b.repr u i := by
  have h : diagMin b lam u = Finsupp.linearCombination ℂ (fun j => (lam j : ℂ) • b j)
      (b.orthonormal.linearIndependent.repr u) := rfl
  rw [h, repr_linearCombination, repr_coe]

theorem repr_adjoint (u : (diagMin b lam).adjoint.domain) (i : ι) :
    b.repr ((diagMin b lam).adjoint u) i = (lam i : ℂ) * b.repr u i := by
  have h := LinearPMap.adjoint_isFormalAdjoint (T := diagMin b lam) (diagMin_dense b lam)
      u ⟨b i, basis_mem_domain b lam i⟩
  rw [diagMin_apply_basis, inner_smul_right] at h
  have h' := congrArg (starRingEnd ℂ) h
  simp only [map_mul, Complex.conj_ofReal, inner_conj_symm] at h'
  rw [b.repr_apply_apply, b.repr_apply_apply, h']

omit [CompleteSpace E] in
/-- Two vectors whose Fourier coefficients are multiplied by the *real* sequence `lam` can be
swapped inside an inner product. -/
theorem inner_swap_of_repr {x y x' y' : E} (hx : ∀ i, b.repr x' i = (lam i : ℂ) * b.repr x i)
    (hy : ∀ i, b.repr y' i = (lam i : ℂ) * b.repr y i) :
    inner ℂ x' y = inner ℂ x y' := by
  rw [← b.repr.inner_map_map x' y, ← b.repr.inner_map_map x y', lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  rw [RCLike.inner_apply, RCLike.inner_apply, hx i, hy i, map_mul, Complex.conj_ofReal]
  ring

omit [CompleteSpace E] in
theorem diagMin_symmetric : (diagMin b lam).IsFormalAdjoint (diagMin b lam) := fun x y =>
  inner_swap_of_repr b lam (repr_diagMin b lam x) (repr_diagMin b lam y)

theorem adjoint_symmetric :
    (diagMin b lam).adjoint.IsFormalAdjoint (diagMin b lam).adjoint := fun x y =>
  inner_swap_of_repr b lam (repr_adjoint b lam x) (repr_adjoint b lam y)

theorem diagMin_le_adjoint : diagMin b lam ≤ (diagMin b lam).adjoint :=
  (diagMin_symmetric b lam).le_adjoint (diagMin_dense b lam)

/-- **The minimal diagonal operator attached to a Hilbert basis with real eigenvalues is
essentially self-adjoint.** -/
theorem diagMin_essentiallySelfAdjoint : IsEssentiallySelfAdjoint (diagMin b lam) := by
  refine ⟨diagMin_dense b lam, diagMin_symmetric b lam, ?_⟩
  have hle := diagMin_le_adjoint b lam
  have hdense' : Dense (((diagMin b lam).adjoint).domain : Set E) :=
    (diagMin_dense b lam).mono fun x hx => hle.1 hx
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm (adjoint_le_adjoint_of_le (diagMin_dense b lam) hle)
    ((adjoint_symmetric b lam).le_adjoint hdense')

end Abstract

/-! ## The minimal Schrödinger operator on the circle -/

section Circle

open AddCircle MeasureTheory

variable (T : ℝ) [hT : Fact (0 < T)]

/-- The eigenvalue of the `n`-th Fourier mode for the Schrödinger operator `-d²/dx² + V₀`. -/
noncomputable def eig (V₀ : ℝ) (n : ℤ) : ℝ := (2 * π * n / T) ^ 2 + V₀

omit hT in
/-- **The ODE.** The `n`-th Fourier mode solves the Schrödinger eigenvalue equation
`-u'' + V₀ u = eig n * u` on the line. -/
theorem fourier_ode (V₀ : ℝ) (n : ℤ) (x : ℝ) :
    -(deriv (deriv fun y : ℝ => fourier n (y : AddCircle T)) x)
        + (V₀ : ℂ) * fourier n (x : AddCircle T)
      = (eig T V₀ n : ℂ) * fourier n (x : AddCircle T) := by
  have h1 : ∀ y : ℝ, HasDerivAt (fun z : ℝ => fourier n (z : AddCircle T))
      (2 * π * Complex.I * n / T * fourier n (y : AddCircle T)) y := hasDerivAt_fourier T n
  have hd1 : (deriv fun z : ℝ => fourier n (z : AddCircle T))
      = fun y : ℝ => 2 * π * Complex.I * n / T * fourier n (y : AddCircle T) :=
    funext fun y => (h1 y).deriv
  have hd2 : deriv (fun y : ℝ => 2 * π * Complex.I * n / T * fourier n (y : AddCircle T)) x
      = 2 * π * Complex.I * n / T * (2 * π * Complex.I * n / T * fourier n (x : AddCircle T)) :=
    ((h1 x).const_mul _).deriv
  rw [hd1, hd2, eig]
  push_cast
  linear_combination (-((2 * π * (n : ℂ) / T) ^ 2) * fourier n (x : AddCircle T)) * Complex.I_sq

/-- The minimal Schrödinger operator `-d²/dx² + V₀` on the circle `ℝ / Tℤ`: it is defined on the
span of the Fourier modes (the trigonometric polynomials), where it acts on each mode by the
eigenvalue produced by the ODE `fourier_ode`. -/
noncomputable def schrodingerMin (V₀ : ℝ) :
    (Lp ℂ 2 (@haarAddCircle T hT)) →ₗ.[ℂ] (Lp ℂ 2 (@haarAddCircle T hT)) :=
  diagMin fourierBasis (eig T V₀)

theorem schrodingerMin_apply_fourier (V₀ : ℝ) (n : ℤ) :
    schrodingerMin T V₀ ⟨fourierLp 2 n, by
      simpa [schrodingerMin, diagMin, coe_fourierBasis] using
        basis_mem_domain (fourierBasis (T := T)) (eig T V₀) n⟩
      = (eig T V₀ n : ℂ) • fourierLp 2 n := by
  have h := diagMin_apply_basis (fourierBasis (T := T)) (eig T V₀) n
  simpa only [coe_fourierBasis] using h

/-! ### The minimal operator really is the differential expression `-d²/dx² + V₀`

Its domain consists exactly of the trigonometric polynomials, and on such a function the operator
is computed by the classical differential expression applied to the (smooth) representative. -/

/-- A trigonometric polynomial, as a continuous function on the circle. -/
noncomputable def trigPolyC (g : ℤ → ℂ) (s : Finset ℤ) : C(AddCircle T, ℂ) :=
  ∑ n ∈ s, g n • fourier n

/-- The same trigonometric polynomial, as an element of `L²`. -/
noncomputable def trigPolyL (g : ℤ → ℂ) (s : Finset ℤ) : Lp ℂ 2 (@haarAddCircle T hT) :=
  ∑ n ∈ s, g n • fourierLp 2 n

theorem trigPolyL_eq_toLp (g : ℤ → ℂ) (s : Finset ℤ) :
    trigPolyL T g s = ContinuousMap.toLp 2 haarAddCircle ℂ (trigPolyC T g s) := by
  simp only [trigPolyL, trigPolyC, map_sum, _root_.map_smul, fourierLp]

/-- A trigonometric polynomial in `L²` is represented by the corresponding continuous function. -/
theorem coeFn_trigPolyL (g : ℤ → ℂ) (s : Finset ℤ) :
    ⇑(trigPolyL T g s) =ᵐ[haarAddCircle] ⇑(trigPolyC T g s) := by
  rw [trigPolyL_eq_toLp]
  exact ContinuousMap.coeFn_toLp haarAddCircle (trigPolyC T g s)

theorem fourierLp_mem_domain (V₀ : ℝ) (n : ℤ) :
    fourierLp 2 n ∈ (schrodingerMin T V₀).domain := by
  simpa [schrodingerMin, coe_fourierBasis] using
    basis_mem_domain (fourierBasis (T := T)) (eig T V₀) n

theorem trigPolyL_mem_domain (V₀ : ℝ) (g : ℤ → ℂ) (s : Finset ℤ) :
    trigPolyL T g s ∈ (schrodingerMin T V₀).domain :=
  Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ (fourierLp_mem_domain T V₀ n)

/-- The domain of the minimal operator consists exactly of the trigonometric polynomials. -/
theorem mem_schrodingerMin_domain_iff (V₀ : ℝ) (u : Lp ℂ 2 (@haarAddCircle T hT)) :
    u ∈ (schrodingerMin T V₀).domain ↔ ∃ (g : ℤ → ℂ) (s : Finset ℤ), u = trigPolyL T g s := by
  constructor
  · intro hu
    rw [schrodingerMin, diagMin_domain, coe_fourierBasis] at hu
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hu
    exact ⟨c, c.support, by rw [← hc, trigPolyL, Finsupp.sum]⟩
  · rintro ⟨g, s, rfl⟩
    exact trigPolyL_mem_domain T V₀ g s

/-- The minimal operator multiplies the `n`-th Fourier coefficient by the ODE eigenvalue. -/
theorem schrodingerMin_trigPolyL (V₀ : ℝ) (g : ℤ → ℂ) (s : Finset ℤ) :
    schrodingerMin T V₀ ⟨trigPolyL T g s, trigPolyL_mem_domain T V₀ g s⟩
      = trigPolyL T (fun n => (eig T V₀ n : ℂ) * g n) s := by
  have hsub : (⟨trigPolyL T g s, trigPolyL_mem_domain T V₀ g s⟩ :
        (schrodingerMin T V₀).domain)
      = ∑ n ∈ s, g n • (⟨fourierLp 2 n, fourierLp_mem_domain T V₀ n⟩ :
        (schrodingerMin T V₀).domain) := by
    apply Subtype.ext
    simp [trigPolyL]
  rw [hsub]
  show (schrodingerMin T V₀).toFun _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [_root_.map_smul]
  show g n • (schrodingerMin T V₀) ⟨fourierLp 2 n, fourierLp_mem_domain T V₀ n⟩ = _
  rw [schrodingerMin_apply_fourier, smul_smul, mul_comm]

omit hT in
/-- **The ODE, for a trigonometric polynomial.** The classical differential expression
`-u'' + V₀ u` applied to a trigonometric polynomial multiplies its `n`-th coefficient by the
eigenvalue `eig T V₀ n`. -/
theorem trigPolyC_ode (V₀ : ℝ) (g : ℤ → ℂ) (s : Finset ℤ) (x : ℝ) :
    -(deriv (deriv fun y : ℝ => trigPolyC T g s (y : AddCircle T)) x)
        + (V₀ : ℂ) * trigPolyC T g s (x : AddCircle T)
      = trigPolyC T (fun n => (eig T V₀ n : ℂ) * g n) s (x : AddCircle T) := by
  have hfun : (fun y : ℝ => trigPolyC T g s (y : AddCircle T))
      = fun y : ℝ => ∑ n ∈ s, g n * fourier n (y : AddCircle T) := by
    funext y; simp [trigPolyC]
  have hfn : ∀ (c : ℤ → ℂ), (∑ n ∈ s, fun z : ℝ => c n * fourier n (z : AddCircle T))
      = fun z : ℝ => ∑ n ∈ s, c n * fourier n (z : AddCircle T) := by
    intro c; funext z; simp
  have D1 : ∀ y : ℝ, HasDerivAt (fun z : ℝ => ∑ n ∈ s, g n * fourier n (z : AddCircle T))
      (∑ n ∈ s, g n * (2 * π * Complex.I * n / T * fourier n (y : AddCircle T))) y := by
    intro y
    have h := HasDerivAt.sum (u := s) (A := fun n (z : ℝ) => g n * fourier n (z : AddCircle T))
      (A' := fun n => g n * (2 * π * Complex.I * n / T * fourier n (y : AddCircle T)))
      (fun n _ => (hasDerivAt_fourier T n y).const_mul (g n))
    rwa [hfn g] at h
  have hd1 : (deriv fun z : ℝ => ∑ n ∈ s, g n * fourier n (z : AddCircle T))
      = fun y : ℝ => ∑ n ∈ s, g n * (2 * π * Complex.I * n / T * fourier n (y : AddCircle T)) :=
    funext fun y => (D1 y).deriv
  have D2 : HasDerivAt
      (fun z : ℝ => ∑ n ∈ s, g n * (2 * π * Complex.I * n / T * fourier n (z : AddCircle T)))
      (∑ n ∈ s, g n * (2 * π * Complex.I * n / T *
        (2 * π * Complex.I * n / T * fourier n (x : AddCircle T)))) x := by
    have h := HasDerivAt.sum (u := s)
      (A := fun n (z : ℝ) => g n * (2 * π * Complex.I * n / T * fourier n (z : AddCircle T)))
      (A' := fun n => g n * (2 * π * Complex.I * n / T *
        (2 * π * Complex.I * n / T * fourier n (x : AddCircle T))))
      (fun n _ => ((hasDerivAt_fourier T n x).const_mul
        (2 * π * Complex.I * n / T)).const_mul (g n))
    have hfn2 : (∑ n ∈ s, fun z : ℝ =>
        g n * (2 * π * Complex.I * n / T * fourier n (z : AddCircle T)))
        = fun z : ℝ => ∑ n ∈ s, g n * (2 * π * Complex.I * n / T * fourier n (z : AddCircle T)) := by
      funext z; simp
    rwa [hfn2] at h
  rw [hfun, hd1, D2.deriv]
  simp only [trigPolyC, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [eig]
  push_cast
  linear_combination (-(g n) * ((2 * π * (n : ℂ) / T) ^ 2) * fourier n (x : AddCircle T)) *
    Complex.I_sq

/-- **The minimal Schrödinger operator acts as the differential expression `-d²/dx² + V₀`.**
For a trigonometric polynomial `u` in the domain, with continuous (indeed smooth) representative
`F`, the image `schrodingerMin T V₀ u` is represented by the continuous function `G` obtained from
`F` by the classical Schrödinger differential expression. -/
theorem schrodingerMin_apply_eq_ode (V₀ : ℝ) (g : ℤ → ℂ) (s : Finset ℤ) :
    ⇑(trigPolyL T g s) =ᵐ[haarAddCircle] ⇑(trigPolyC T g s) ∧
      ⇑(schrodingerMin T V₀ ⟨trigPolyL T g s, trigPolyL_mem_domain T V₀ g s⟩) =ᵐ[haarAddCircle]
        ⇑(trigPolyC T (fun n => (eig T V₀ n : ℂ) * g n) s) ∧
      ∀ x : ℝ, -(deriv (deriv fun y : ℝ => trigPolyC T g s (y : AddCircle T)) x)
          + (V₀ : ℂ) * trigPolyC T g s (x : AddCircle T)
        = trigPolyC T (fun n => (eig T V₀ n : ℂ) * g n) s (x : AddCircle T) :=
  ⟨coeFn_trigPolyL T g s, by
    rw [schrodingerMin_trigPolyL]; exact coeFn_trigPolyL T _ s,
   trigPolyC_ode T V₀ g s⟩

/-- **The minimal Schrödinger operator on the circle is essentially self-adjoint.** -/
theorem schrodinger_essentiallySelfAdjoint_of_ode (V₀ : ℝ) :
    IsEssentiallySelfAdjoint (schrodingerMin T V₀) :=
  diagMin_essentiallySelfAdjoint _ _

end Circle

end Brockian.Weyl.SchrodingerMinimal

