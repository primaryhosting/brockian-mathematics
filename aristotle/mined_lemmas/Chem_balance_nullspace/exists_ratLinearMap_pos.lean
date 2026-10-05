/-
# Balance Nullspace
Category: Chemistry
Target: Chem.balance_nullspace
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Chem

/-! ## A ℚ-linear functional that is positive on a finite family of positive reals -/

/-- Given finitely many *positive* real numbers `x s`, there is a `ℚ`-linear functional
`f : ℝ →ₗ[ℚ] ℚ` which is positive on all of them.  (Such an `f` is a rational
"approximation of the identity" on the `ℚ`-span of the `x s`.) -/

theorem exists_ratLinearMap_pos {S : Type*} [Fintype S] (x : S → ℝ) (hx : ∀ s, 0 < x s) :
    ∃ f : ℝ →ₗ[ℚ] ℚ, ∀ s, 0 < f (x s) := by
  classical
  rcases isEmpty_or_nonempty S with hS | hS
  · exact ⟨0, fun s => (hS.false s).elim⟩
  -- a uniform positive lower bound for the finitely many positive reals `x s`
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ s, m ≤ x s := by
    refine ⟨Finset.univ.inf' Finset.univ_nonempty x, ?_,
      fun s => Finset.inf'_le _ (Finset.mem_univ s)⟩
    rw [Finset.lt_inf'_iff]
    intro s _
    exact hx s
  -- the `ℚ`-span of the `x s` is a finite dimensional `ℚ`-vector space
  set W := Submodule.span ℚ (Set.range x) with hWdef
  haveI : FiniteDimensional ℚ W := FiniteDimensional.span_of_finite ℚ (Set.finite_range x)
  set b := Module.finBasis ℚ W with hb
  set v : S → W := fun s => ⟨x s, Submodule.subset_span (Set.mem_range_self s)⟩ with hv
  set c : S → Fin (Module.finrank ℚ W) → ℚ := fun s i => b.repr (v s) i with hc
  have hxr : ∀ s, ∑ i, ((c s i : ℚ) : ℝ) * ((b i : W) : ℝ) = x s := by
    intro s
    have h1 : ∑ i, (b.repr (v s)) i • b i = v s := b.sum_repr (v s)
    have h2 : (((∑ i, (b.repr (v s)) i • b i : W)) : ℝ) = x s := by rw [h1]
    rw [AddSubmonoidClass.coe_finset_sum] at h2
    simp only [SetLike.val_smul, Rat.smul_def] at h2
    exact h2
  set D : ℝ := 1 + ∑ s, ∑ i, |((c s i : ℚ) : ℝ)| with hDdef
  have hD1 : (1:ℝ) ≤ D := by
    have : (0:ℝ) ≤ ∑ s, ∑ i, |((c s i : ℚ) : ℝ)| :=
      Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  have hD0 : (0:ℝ) < D := lt_of_lt_of_le one_pos hD1
  have hcbound : ∀ s, ∑ i, |((c s i : ℚ) : ℝ)| ≤ D := by
    intro s
    have : ∑ i, |((c s i : ℚ) : ℝ)| ≤ ∑ t, ∑ i, |((c t i : ℚ) : ℝ)| :=
      Finset.single_le_sum (f := fun t => ∑ i, |((c t i : ℚ) : ℝ)|)
        (fun t _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ s)
    linarith
  -- rational approximations of the basis vectors
  set eps : ℝ := m / (2 * D) with hepsdef
  have heps : 0 < eps := div_pos hm0 (by linarith)
  have hqex : ∀ i, ∃ q : ℚ, |((b i : W) : ℝ) - (q:ℝ)| < eps := fun i => exists_rat_near _ heps
  choose q hq using hqex
  set f₀ : W →ₗ[ℚ] ℚ := ∑ i, q i • b.coord i with hf₀
  obtain ⟨f, hf⟩ := f₀.exists_extend
  refine ⟨f, fun s => ?_⟩
  have hfx : f (x s) = f₀ (v s) := by
    have := congrArg (fun g : W →ₗ[ℚ] ℚ => g (v s)) hf
    simpa [hv] using this
  have hval : f₀ (v s) = ∑ i, q i * c s i := by
    simp [hf₀, LinearMap.sum_apply, Module.Basis.coord_apply, hc]
  have hdiff : ((f₀ (v s) : ℚ) : ℝ) - x s
      = ∑ i, ((q i : ℝ) - ((b i : W) : ℝ)) * ((c s i : ℚ) : ℝ) := by
    rw [hval, ← hxr s]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hbound : |((f₀ (v s) : ℚ) : ℝ) - x s| ≤ m / 2 := by
    rw [hdiff]
    calc |∑ i, ((q i : ℝ) - ((b i : W) : ℝ)) * ((c s i : ℚ) : ℝ)|
        ≤ ∑ i, |((q i : ℝ) - ((b i : W) : ℝ)) * ((c s i : ℚ) : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, eps * |((c s i : ℚ) : ℝ)| := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (by rw [abs_sub_comm]; exact (hq i).le) (abs_nonneg _)
      _ = eps * ∑ i, |((c s i : ℚ) : ℝ)| := by rw [Finset.mul_sum]
      _ ≤ eps * D := mul_le_mul_of_nonneg_left (hcbound s) heps.le
      _ = m / 2 := by rw [hepsdef]; field_simp
  have hpos : (0:ℝ) < ((f₀ (v s) : ℚ) : ℝ) := by
    have h1 := (abs_le.mp hbound).1
    have h2 := hm s
    linarith
  rw [hfx]
  exact_mod_cast hpos

/-! ## From a positive real null vector to a positive rational one -/

