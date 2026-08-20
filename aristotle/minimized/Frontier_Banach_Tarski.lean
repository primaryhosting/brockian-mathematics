import Mathlib

/-!
# Abstract machinery for paradoxical decompositions

This file develops the general theory needed for the Banach–Tarski paradox, on top of
Mathlib's `Equidecomp` (equidecompositions for a group action).
-/

open Set Function Pointwise

namespace BT

variable {X G H : Type*} [Nonempty X] [Group G] [MulAction G X]

/-- Build an equidecomposition out of a function which is a bijection from `A` to `B` and
moves every point of `A` by an element of a fixed finite set of group elements. -/

lemma O3.smul_apply (M : O3) (x : E) (i : Fin 3) :
    (M • x) i = ∑ j, (M : Matrix (Fin 3) (Fin 3) ℝ) i j * x j := rfl

lemma O3.smul_eq (M : O3) (x : E) :
    M • x = WithLp.toLp 2 ((M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ WithLp.ofLp x) := rfl

lemma O3.mem_iff (M : O3) : (M : Matrix (Fin 3) (Fin 3) ℝ) * (M : Matrix (Fin 3) (Fin 3) ℝ)ᵀ = 1 :=
  (Matrix.mem_orthogonalGroup_iff _ _).1 M.2

lemma O3.transpose_mul (M : O3) :
    (M : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (M : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  have := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).1 M.2
  simpa using this

noncomputable instance : MulAction O3 E where
  one_smul x := by
    ext i; simp
  mul_smul M N x := by
    ext i
    simp only [O3.smul_apply, Submonoid.coe_mul]
    simp [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm

lemma O3.coe_inv (M : O3) :
    ((M⁻¹ : O3) : Matrix (Fin 3) (Fin 3) ℝ) = (M : Matrix (Fin 3) (Fin 3) ℝ)ᵀ := by
  have h : ((M⁻¹ : O3) : Matrix (Fin 3) (Fin 3) ℝ) = star (M : Matrix (Fin 3) (Fin 3) ℝ) := rfl
  rw [h]
  ext i j
  simp [Matrix.star_apply]

lemma O3.smul_sub (M : O3) (x y : E) : M • (x - y) = M • x - M • y := by
  ext i
  simp only [O3.smul_apply, PiLp.sub_apply, mul_sub]
  exact Finset.sum_sub_distrib (f := fun j => (M : Matrix (Fin 3) (Fin 3) ℝ) i j * x j)
    (g := fun j => (M : Matrix (Fin 3) (Fin 3) ℝ) i j * y j)

/-- Orthogonal matrices preserve the Euclidean norm. -/

lemma O3.norm_smul (M : O3) (x : E) : ‖M • x‖ = ‖x‖ := by
  set a : Matrix (Fin 3) (Fin 3) ℝ := (M : Matrix (Fin 3) (Fin 3) ℝ) with ha
  have h : ∀ j k : Fin 3, ∑ i, a i j * a i k = if j = k then 1 else 0 := by
    intro j k
    have := congrFun (congrFun (O3.transpose_mul M) j) k
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply] using this
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [O3.smul_apply, Real.norm_eq_abs, sq_abs]
  have h1 : ∀ i : Fin 3, (∑ j, a i j * x j) ^ 2 = ∑ j, ∑ k, (a i j * a i k) * (x j * x k) := by
    intro i
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]
  have h2 : ∀ j : Fin 3, ∑ i, ∑ k, (a i j * a i k) * (x j * x k) = (x j) ^ 2 := by
    intro j
    rw [Finset.sum_comm]
    have h3 : ∀ k : Fin 3,
        ∑ i, (a i j * a i k) * (x j * x k) = (if j = k then 1 else 0) * (x j * x k) := by
      intro k; rw [← h j k, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun k _ => h3 k]
    simp [Finset.sum_ite_eq]
    ring
  rw [Finset.sum_congr rfl fun j _ => h2 j]

lemma O3.smul_smul_real (M : O3) (r : ℝ) (x : E) : M • (r • x) = r • (M • x) := by
  ext i
  simp only [O3.smul_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma O3.smul_zero' (M : O3) : M • (0 : E) = 0 := by
  ext i; simp

/-- The group of isometries of Euclidean 3-space. -/
abbrev Isom := E ≃ᵢ E

instance : MulAction Isom E where
  smul f x := f x
  one_smul _ := rfl
  mul_smul f g x := IsometryEquiv.mul_apply f g x

lemma Isom.smul_def (f : Isom) (x : E) : f • x = f x := rfl

/-- An orthogonal matrix, viewed as an isometry of `E`. -/

noncomputable def O3.toIsomFun (M : O3) : E ≃ᵢ E where
  toEquiv :=
    { toFun := fun x => M • x
      invFun := fun x => M⁻¹ • x
      left_inv := fun x => by
        show M⁻¹ • (M • x) = x
        rw [← SemigroupAction.mul_smul, inv_mul_cancel, one_smul]
      right_inv := fun x => by
        show M • (M⁻¹ • x) = x
        rw [← SemigroupAction.mul_smul, mul_inv_cancel, one_smul] }
  isometry_toFun := by
    refine Isometry.of_dist_eq fun x y => ?_
    simp only [dist_eq_norm, ← O3.smul_sub, O3.norm_smul]

@[simp] lemma O3.toIsomFun_apply (M : O3) (x : E) : O3.toIsomFun M x = M • x := rfl

/-- The orthogonal group as a subgroup of the isometry group. -/

noncomputable def O3.toIsom : O3 →* Isom where
  toFun := O3.toIsomFun
  map_one' := by
    refine IsometryEquiv.ext fun x => ?_
    show (1 : O3) • x = x
    exact one_smul _ x
  map_mul' M N := by
    refine IsometryEquiv.ext fun x => ?_
    show (M * N) • x = M • (N • x)
    exact SemigroupAction.mul_smul M N x

lemma O3.toIsom_smul (M : O3) (x : E) : (O3.toIsom M) • x = M • x := rfl

end BT

import RequestProject.Space

/-!
# Fixed points of a rotation

A nontrivial rotation of `ℝ³` (an orthogonal matrix of determinant one) fixes only the two
points where its axis meets the unit sphere. In particular its fixed points on the sphere
form a countable (indeed, finite) set.
-/

open Matrix Set Function

namespace BT

noncomputable def e2 : E := WithLp.toLp 2 ![0, 1, 0]

noncomputable def rotY (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos t, 0, Real.sin t; 0, 1, 0; -Real.sin t, 0, Real.cos t]

lemma rotY_mem (t : ℝ) : rotY t ∈ O3 := by
  rw [Matrix.mem_orthogonalGroup_iff]
  have h := Real.sin_sq_add_cos_sq t
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotY, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [h]

/-- Rotation about the `y`-axis, as an element of the orthogonal group. -/

noncomputable def RY (t : ℝ) : O3 := ⟨rotY t, rotY_mem t⟩

lemma rotY_add (s t : ℝ) : rotY (s + t) = rotY s * rotY t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotY, Matrix.mul_apply, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;> ring

lemma RY_add (s t : ℝ) : RY (s + t) = RY s * RY t := by
  apply Subtype.ext
  simpa using rotY_add s t

lemma RY_zero : RY 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotY]

lemma RY_pow (t : ℝ) (n : ℕ) : RY t ^ n = RY (n * t) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, RY_zero]
  | succ m ih =>
      rw [pow_succ, ih, ← RY_add]
      congr 1
      push_cast
      ring

lemma RY_smul_apply (t : ℝ) (x : E) :
    ((RY t • x) 0 = Real.cos t * x 0 + Real.sin t * x 2) ∧
    ((RY t • x) 2 = -(Real.sin t) * x 0 + Real.cos t * x 2) := by
  constructor <;>
    simp [O3.smul_apply, rotY, Fin.sum_univ_three]

/-- A rotation about the `y`-axis fixing a point off the `y`-axis is trivial. -/

lemma cos_eq_one_of_fixed {t : ℝ} {y : E} (hy : RY t • y = y) (hax : y 0 ≠ 0 ∨ y 2 ≠ 0) :
    Real.cos t = 1 := by
  obtain ⟨h0, h2⟩ := RY_smul_apply t y
  have e0 : Real.cos t * y 0 + Real.sin t * y 2 = y 0 := by
    rw [← h0, hy]
  have e2 : -(Real.sin t) * y 0 + Real.cos t * y 2 = y 2 := by
    rw [← h2, hy]
  have hpyth := Real.sin_sq_add_cos_sq t
  by_contra hcos
  have hA : (Real.cos t - 1) * y 0 + Real.sin t * y 2 = 0 := by linarith
  have hB : -(Real.sin t) * y 0 + (Real.cos t - 1) * y 2 = 0 := by linarith
  have hne : (2 - 2 * Real.cos t) ≠ 0 := fun hc => hcos (by linarith)
  have h1 : (2 - 2 * Real.cos t) * y 0 = 0 := by
    linear_combination (Real.cos t - 1) * hA - Real.sin t * hB - y 0 * hpyth
  have h2' : (2 - 2 * Real.cos t) * y 2 = 0 := by
    linear_combination Real.sin t * hA + (Real.cos t - 1) * hB - y 2 * hpyth
  rcases hax with h | h
  · exact h ((mul_eq_zero.mp h1).resolve_left hne)
  · exact h ((mul_eq_zero.mp h2').resolve_left hne)

/-- There is a rotation about the `y`-axis moving a given countable set, disjoint from the
`y`-axis, completely off itself, together with all of its positive powers. -/

theorem exists_rotY_disjoint (D : Set E) (hD : D.Countable)
    (hax : ∀ d ∈ D, d 0 ≠ 0 ∨ d 2 ≠ 0) :
    ∃ t : ℝ, ∀ n : ℕ, 1 ≤ n → Disjoint ((RY t ^ n) • D) D := by
  classical
  -- for fixed data, the set of bad angles is countable
  have key : ∀ (m : ℕ) (d d' : E), d ∈ D → d' ∈ D →
      {t : ℝ | (RY t ^ (m + 1)) • d = d'}.Countable := by
    intro m d d' _ hd'
    rcases eq_empty_or_nonempty {t : ℝ | (RY t ^ (m + 1)) • d = d'} with h | ⟨t₀, ht₀⟩
    · rw [h]; exact countable_empty
    · refine Set.Countable.mono (s₂ := range fun k : ℤ => t₀ + k * (2 * Real.pi) / (m + 1)) ?_
        (countable_range _)
      intro t ht
      simp only [mem_setOf_eq] at ht ht₀
      rw [RY_pow] at ht ht₀
      -- `d'` is fixed by the rotation by the difference of the angles
      have hfix : RY ((m + 1 : ℕ) * t - (m + 1 : ℕ) * t₀) • d' = d' := by
        have : RY ((m + 1 : ℕ) * t - (m + 1 : ℕ) * t₀) • (RY ((m + 1 : ℕ) * t₀) • d) =
            RY ((m + 1 : ℕ) * t) • d := by
          rw [← SemigroupAction.mul_smul, ← RY_add]
          congr 2
          ring
        rw [ht₀] at this
        rw [this, ht]
      have hcos := cos_eq_one_of_fixed hfix (hax d' hd')
      obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hcos
      refine ⟨k, ?_⟩
      have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
      have : ((m : ℝ) + 1) * t - ((m : ℝ) + 1) * t₀ = k * (2 * Real.pi) := by
        push_cast at hk
        linarith [hk]
      field_simp
      linarith [this]
  set B : Set ℝ := ⋃ m : ℕ, ⋃ d ∈ D, ⋃ d' ∈ D, {t : ℝ | (RY t ^ (m + 1)) • d = d'} with hB
  have hBc : B.Countable := by
    refine countable_iUnion fun m => ?_
    refine hD.biUnion fun d hd => ?_
    exact hD.biUnion fun d' hd' => key m d d' hd hd'
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∉ B := by
    by_contra hc
    push_neg at hc
    exact Cardinal.not_countable_real (by rwa [Set.eq_univ_iff_forall.mpr hc] at hBc)
  refine ⟨t, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Set.disjoint_left]
  rintro x ⟨d, hd, rfl⟩ hx'
  exact ht (by
    rw [hB]
    refine mem_iUnion.2 ⟨m, ?_⟩
    refine mem_iUnion₂.2 ⟨d, hd, ?_⟩
    exact mem_iUnion₂.2 ⟨(RY t ^ (m + 1)) • d, hx', rfl⟩)

end BT
