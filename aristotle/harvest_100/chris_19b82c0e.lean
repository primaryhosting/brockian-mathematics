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
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The required header comment is placed immediately after `import Mathlib`, since Lean 4 does not
-- allow a module doc comment to precede the `import` commands.)

open scoped LinearPMap ComplexConjugate

noncomputable section

namespace Brockian.Weyl.DeficiencyODE

/-- The Hilbert space `ℓ²(ℤ, ℂ)` of square-summable two-sided sequences. -/
abbrev L2Z : Type := lp (fun _ : ℤ => ℂ) 2

/-- A densely defined operator is *essentially self-adjoint* when its adjoint is self-adjoint;
equivalently, when its closure is its unique self-adjoint extension. -/
def EssentiallySelfAdjoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (T : E →ₗ.[ℂ] E) : Prop :=
  IsSelfAdjoint T†

/-! ### Restrictions of bounded self-adjoint operators -/

/-- The restriction of a bounded self-adjoint operator to any dense subspace is essentially
self-adjoint. -/
theorem essentiallySelfAdjoint_toPMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) {D : Submodule ℂ E}
    (hD : Dense (D : Set E)) : EssentiallySelfAdjoint ((A : E →ₗ[ℂ] E).toPMap D) := by
  have hA' : ContinuousLinearMap.adjoint A = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hA
  have htop : Dense ((⊤ : Submodule ℂ E) : Set E) := by
    simp only [Submodule.top_coe]; exact dense_univ
  unfold EssentiallySelfAdjoint
  rw [A.toPMap_adjoint_eq_adjoint_toPMap_of_dense hD, hA', LinearPMap.isSelfAdjoint_def,
    A.toPMap_adjoint_eq_adjoint_toPMap_of_dense htop, hA']

/-! ### The finitely supported sequences -/

/-- The subspace of finitely supported elements of `ℓ²(ℤ, ℂ)`. -/
def finSupp : Submodule ℂ L2Z where
  carrier := {f | (Function.support (f : ℤ → ℂ)).Finite}
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq, lp.coeFn_add] at *
    exact (hf.union hg).subset (Function.support_add _ _)
  zero_mem' := by simp [Set.mem_setOf_eq]
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_setOf_eq, lp.coeFn_smul] at *
    exact hf.subset (Function.support_smul_subset_right _ _)

/-- The finitely supported sequences are dense in `ℓ²(ℤ, ℂ)`. -/
theorem dense_finSupp : Dense ((finSupp : Submodule ℂ L2Z) : Set L2Z) := by
  set b : HilbertBasis ℤ ℂ (lp (fun _ : ℤ => ℂ) 2) := default with hbdef
  have hb := b.dense_span
  have hsub : Submodule.span ℂ (Set.range ⇑b) ≤ finSupp := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    have hbn : b n = lp.single 2 n (1 : ℂ) := by
      simp [hbdef, ← HilbertBasis.repr_symm_single]
      rfl
    rw [hbn]
    show (Function.support ((lp.single 2 n (1 : ℂ) : L2Z) : ℤ → ℂ)).Finite
    refine (Set.finite_singleton n).subset (fun m hm => ?_)
    simp only [Function.mem_support, lp.single_apply, Pi.single_apply] at hm
    by_contra h
    exact hm (if_neg (by simpa using h))
  have hdense : Dense ((Submodule.span ℂ (Set.range ⇑b) : Submodule ℂ L2Z) : Set L2Z) := by
    rw [← Submodule.dense_iff_topologicalClosure_eq_top] at hb
    exact hb
  exact hdense.mono hsub

/-! ### The discrete Schrödinger operator -/

/-- Composition with a permutation of the index set preserves square-summability. -/
theorem memℓp_comp_equiv (f : L2Z) (e : ℤ ≃ ℤ) : Memℓp (fun n => f (e n)) 2 := by
  refine memℓp_gen ?_
  have hf : Summable fun n : ℤ => ‖f n‖ ^ (2 : ENNReal).toReal :=
    (lp.memℓp f).summable (by norm_num)
  exact (e.summable_iff (f := fun n : ℤ => ‖f n‖ ^ (2 : ENNReal).toReal)).2 hf

/-- Reindexing `ℓ²(ℤ, ℂ)` along a permutation of `ℤ`, as a linear map. -/
def shiftLM (e : ℤ ≃ ℤ) : L2Z →ₗ[ℂ] L2Z where
  toFun f := ⟨fun n => f (e n), memℓp_comp_equiv f e⟩
  map_add' f g := by ext n; simp
  map_smul' c f := by ext n; simp

@[simp] theorem shiftLM_apply (e : ℤ ≃ ℤ) (f : L2Z) (n : ℤ) : shiftLM e f n = f (e n) := rfl

/-- Reindexing `ℓ²(ℤ, ℂ)` along a permutation of `ℤ`, as a bounded operator. -/
def shiftCLM (e : ℤ ≃ ℤ) : L2Z →L[ℂ] L2Z :=
  (shiftLM e).mkContinuous 1 (by
    intro f
    rw [one_mul]
    refine lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg f) ?_
    rw [lp.norm_rpow_eq_tsum (by norm_num) f]
    exact le_of_eq (Equiv.tsum_eq e (fun n : ℤ => ‖f n‖ ^ (2 : ENNReal).toReal)))

@[simp] theorem shiftCLM_apply (e : ℤ ≃ ℤ) (f : L2Z) (n : ℤ) : shiftCLM e f n = f (e n) := rfl

/-- Multiplication by a bounded real potential preserves square-summability. -/
theorem memℓp_mul_potential (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) (f : L2Z) :
    Memℓp (fun n => (V n : ℂ) * f n) 2 := by
  refine memℓp_gen ?_
  have hf : Summable fun n : ℤ => ‖f n‖ ^ (2 : ENNReal).toReal :=
    (lp.memℓp f).summable (by norm_num)
  refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (norm_nonneg _) _)
    (fun n => ?_) (hf.mul_left (C ^ (2 : ENNReal).toReal))
  have h1 : ‖(V n : ℂ) * f n‖ = |V n| * ‖f n‖ := by simp [Complex.norm_real]
  rw [h1, Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
  gcongr
  exact hV n

/-- Multiplication by a bounded real potential, as a linear map on `ℓ²(ℤ, ℂ)`. -/
def multLM (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) : L2Z →ₗ[ℂ] L2Z where
  toFun f := ⟨fun n => (V n : ℂ) * f n, memℓp_mul_potential V C hV f⟩
  map_add' f g := by ext n; simp [mul_add]
  map_smul' c f := by ext n; simp [mul_left_comm]

@[simp] theorem multLM_apply (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) (f : L2Z) (n : ℤ) :
    multLM V C hV f n = (V n : ℂ) * f n := rfl

/-- Multiplication by a bounded real potential, as a bounded operator on `ℓ²(ℤ, ℂ)`. -/
def multCLM (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) : L2Z →L[ℂ] L2Z :=
  (multLM V C hV).mkContinuous C (by
    intro f
    have hC : 0 ≤ C := le_trans (abs_nonneg _) (hV 0)
    have hf : Summable fun n : ℤ => ‖f n‖ ^ (2 : ENNReal).toReal :=
      (lp.memℓp f).summable (by norm_num)
    refine lp.norm_le_of_tsum_le (by norm_num) (mul_nonneg hC (norm_nonneg f)) ?_
    have hle : ∀ n : ℤ, ‖(multLM V C hV f) n‖ ^ (2 : ENNReal).toReal
        ≤ C ^ (2 : ENNReal).toReal * ‖f n‖ ^ (2 : ENNReal).toReal := by
      intro n
      have h1 : ‖(multLM V C hV f) n‖ = |V n| * ‖f n‖ := by
        show ‖(V n : ℂ) * f n‖ = _
        simp [Complex.norm_real]
      rw [h1, Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
      gcongr
      exact hV n
    calc ∑' n, ‖(multLM V C hV f) n‖ ^ (2 : ENNReal).toReal
        ≤ ∑' n, C ^ (2 : ENNReal).toReal * ‖f n‖ ^ (2 : ENNReal).toReal :=
          Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le
            (fun n => Real.rpow_nonneg (norm_nonneg _) _) hle (hf.mul_left _)) (hf.mul_left _)
      _ = C ^ (2 : ENNReal).toReal * ∑' n, ‖f n‖ ^ (2 : ENNReal).toReal := tsum_mul_left
      _ = (C * ‖f‖) ^ (2 : ENNReal).toReal := by
          rw [Real.mul_rpow hC (norm_nonneg f), ← lp.norm_rpow_eq_tsum (by norm_num) f])

@[simp] theorem multCLM_apply (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) (f : L2Z) (n : ℤ) :
    multCLM V C hV f n = (V n : ℂ) * f n := rfl

/-- The right shift `n ↦ n + 1` of the index set. -/
abbrev shiftEquiv : ℤ ≃ ℤ := Equiv.addRight (1 : ℤ)

/-- The discrete Schrödinger operator `(H f) n = 2 f n - f (n+1) - f (n-1) + V n * f n`
on `ℓ²(ℤ, ℂ)`, for a bounded real potential `V`. -/
def schrodingerCLM (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) : L2Z →L[ℂ] L2Z :=
  (2 : ℂ) • ContinuousLinearMap.id ℂ L2Z - shiftCLM shiftEquiv - shiftCLM shiftEquiv.symm
    + multCLM V C hV

theorem schrodingerCLM_apply (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) (f : L2Z) (n : ℤ) :
    schrodingerCLM V C hV f n = 2 * f n - f (n + 1) - f (n - 1) + (V n : ℂ) * f n := by
  simp [schrodingerCLM, sub_eq_add_neg]

/-- The two shifts are formally adjoint to each other. -/
theorem inner_shiftCLM_left (e : ℤ ≃ ℤ) (f g : L2Z) :
    inner ℂ (shiftCLM e f) g = inner ℂ f (shiftCLM e.symm g) := by
  simp only [lp.inner_eq_tsum, shiftCLM_apply]
  rw [← Equiv.tsum_eq e (fun m : ℤ => (inner ℂ (f m) (g (e.symm m)) : ℂ))]
  simp

/-- Multiplication by a real potential is symmetric. -/
theorem inner_multCLM_left (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) (f g : L2Z) :
    inner ℂ (multCLM V C hV f) g = inner ℂ f (multCLM V C hV g) := by
  simp only [lp.inner_eq_tsum]
  congr 1
  funext n
  simp [RCLike.inner_apply, mul_assoc, mul_left_comm]

theorem schrodingerCLM_isSymmetric (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) :
    (schrodingerCLM V C hV : L2Z →ₗ[ℂ] L2Z).IsSymmetric := by
  intro f g
  show inner ℂ (schrodingerCLM V C hV f) g = inner ℂ f (schrodingerCLM V C hV g)
  simp only [schrodingerCLM, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, inner_add_left, inner_sub_left,
    inner_add_right, inner_sub_right, inner_smul_left, inner_smul_right,
    inner_shiftCLM_left, inner_multCLM_left, Equiv.symm_symm]
  simp only [Complex.conj_ofNat]
  ring

theorem schrodingerCLM_isSelfAdjoint (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) :
    IsSelfAdjoint (schrodingerCLM V C hV) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 (schrodingerCLM_isSymmetric V C hV)

/-! ### Main result -/

/-- **Essential self-adjointness of the discrete Schrödinger operator under weak regularity.**

Let `V : ℤ → ℝ` be a potential which is only assumed *bounded* (weak regularity: no continuity,
smoothness or decay is required), and let `T` be the Schrödinger operator
`(T f) n = 2 f n - f (n+1) - f (n-1) + V n * f n` defined on the (dense) subspace of finitely
supported sequences in `ℓ²(ℤ, ℂ)`. Then `T` is essentially self-adjoint: its adjoint is
self-adjoint, so `T` has a unique self-adjoint extension, namely its closure. -/
theorem schrodinger_essentiallySelfAdjoint_of_weakRegularity
    (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) (T : L2Z →ₗ.[ℂ] L2Z)
    (hdom : T.domain = finSupp)
    (hact : ∀ (f : T.domain) (n : ℤ),
      T f n = 2 * (f : L2Z) n - (f : L2Z) (n + 1) - (f : L2Z) (n - 1) + (V n : ℂ) * (f : L2Z) n) :
    EssentiallySelfAdjoint T := by
  have hT : T = ((schrodingerCLM V C hV : L2Z →ₗ[ℂ] L2Z).toPMap finSupp) := by
    refine LinearPMap.ext hdom ?_
    intro x hf hg
    refine lp.ext (funext fun n => ?_)
    rw [hact ⟨x, hf⟩ n]
    show _ = schrodingerCLM V C hV x n
    rw [schrodingerCLM_apply]
  rw [hT]
  exact essentiallySelfAdjoint_toPMap _ (schrodingerCLM_isSelfAdjoint V C hV) dense_finSupp

/-- The discrete Schrödinger operator with bounded potential `V`, as an unbounded operator
defined on the finitely supported sequences. -/
def schrodingerPMap (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) : L2Z →ₗ.[ℂ] L2Z :=
  (schrodingerCLM V C hV : L2Z →ₗ[ℂ] L2Z).toPMap finSupp

/-- The hypotheses of `schrodinger_essentiallySelfAdjoint_of_weakRegularity` are satisfiable:
`schrodingerPMap` is such an operator. -/
theorem schrodingerPMap_domain (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) :
    (schrodingerPMap V C hV).domain = finSupp := rfl

theorem schrodingerPMap_apply (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C)
    (f : (schrodingerPMap V C hV).domain) (n : ℤ) :
    schrodingerPMap V C hV f n =
      2 * (f : L2Z) n - (f : L2Z) (n + 1) - (f : L2Z) (n - 1) + (V n : ℂ) * (f : L2Z) n :=
  schrodingerCLM_apply V C hV (f : L2Z) n

/-- Unconditional form of the main theorem for the canonical realization of the operator. -/
theorem schrodingerPMap_essentiallySelfAdjoint (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) :
    EssentiallySelfAdjoint (schrodingerPMap V C hV) :=
  schrodinger_essentiallySelfAdjoint_of_weakRegularity V C hV _
    (schrodingerPMap_domain V C hV) (schrodingerPMap_apply V C hV)

end Brockian.Weyl.DeficiencyODE

