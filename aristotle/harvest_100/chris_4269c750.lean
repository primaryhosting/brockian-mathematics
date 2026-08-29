import RequestProject.Equidecomp

/-!
# Rotations of `ℝ³`

Set-up for the Banach–Tarski paradox: the group `SO(3)` of rotations acting on
`E = EuclideanSpace ℝ (Fin 3)`, the group of isometries of `E`, and the fact that a
non-identity rotation fixes at most two points of the unit sphere.
-/

open Matrix

namespace BanachTarski

/-- Three dimensional Euclidean space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The group of rotations of `ℝ³`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

noncomputable instance : SMul ↥SO3 E :=
  ⟨fun M x => WithLp.toLp 2 ((M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ WithLp.ofLp x)⟩

theorem SO3.smul_def (M : ↥SO3) (x : E) :
    M • x = WithLp.toLp 2 ((M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ WithLp.ofLp x) := rfl

@[simp] theorem SO3.ofLp_smul (M : ↥SO3) (x : E) :
    WithLp.ofLp (M • x) = (M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ WithLp.ofLp x := rfl

theorem SO3.smul_apply (M : ↥SO3) (x : E) (i : Fin 3) :
    (M • x) i = ∑ j, (M : Matrix (Fin 3) (Fin 3) ℝ) i j * x j := by
  simp [SO3.smul_def, Matrix.mulVec, dotProduct]

noncomputable instance : MulAction ↥SO3 E where
  one_smul x := by ext i; simp [SO3.smul_def]
  mul_smul M N x := by
    ext i
    simp [SO3.smul_def, Submonoid.coe_mul, Matrix.mulVec_mulVec]

theorem SO3.transpose_mul (M : ↥SO3) :
    (M : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (M : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  have := M.2.1
  rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff'] at this
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose] using this

theorem SO3.mul_transpose (M : ↥SO3) :
    (M : Matrix (Fin 3) (Fin 3) ℝ) * (M : Matrix (Fin 3) (Fin 3) ℝ)ᵀ = 1 := by
  have := M.2.1
  rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff] at this
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose] using this

theorem SO3.det_eq_one (M : ↥SO3) : (M : Matrix (Fin 3) (Fin 3) ℝ).det = 1 := M.2.2

theorem dotProduct_ofLp_self (x : E) : WithLp.ofLp x ⬝ᵥ WithLp.ofLp x = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [dotProduct, Real.norm_eq_abs, sq_abs, pow_two]

@[simp] theorem SO3.norm_smul (M : ↥SO3) (x : E) : ‖M • x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  have key : ((M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ WithLp.ofLp x) ⬝ᵥ
      ((M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ WithLp.ofLp x) = WithLp.ofLp x ⬝ᵥ WithLp.ofLp x := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
      SO3.transpose_mul, Matrix.one_mulVec]
  simpa [dotProduct, Real.norm_eq_abs, sq_abs, SO3.smul_def, pow_two] using key

theorem SO3.smul_sub (M : ↥SO3) (x y : E) : M • (x - y) = M • x - M • y := by
  ext i
  simp [SO3.smul_def, Matrix.mulVec_sub]

theorem SO3.smul_smul_real (M : ↥SO3) (r : ℝ) (x : E) : M • (r • x) = r • (M • x) := by
  ext i
  simp [SO3.smul_def, Matrix.mulVec_smul]

/-! ### The isometry group -/

instance : SMul (E ≃ᵢ E) E := ⟨fun f x => f x⟩

instance : MulAction (E ≃ᵢ E) E where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem isom_smul_apply (f : E ≃ᵢ E) (x : E) : f • x = f x := rfl

/-- A rotation, viewed as an isometry of `ℝ³`. -/
noncomputable def SO3.toIsom : ↥SO3 →* (E ≃ᵢ E) where
  toFun M :=
    { toEquiv := MulAction.toPerm M
      isometry_toFun := by
        refine Isometry.of_dist_eq fun x y => ?_
        show dist (M • x) (M • y) = dist x y
        rw [dist_eq_norm, dist_eq_norm, ← SO3.smul_sub, SO3.norm_smul] }
  map_one' := IsometryEquiv.ext fun x => by
    show (1 : ↥SO3) • x = x
    rw [one_smul]
  map_mul' M N := IsometryEquiv.ext fun x => by
    show (M * N) • x = M • (N • x)
    exact MulAction.mul_smul M N x

@[simp] theorem SO3.toIsom_apply (M : ↥SO3) (x : E) : SO3.toIsom M x = M • x := rfl

theorem SO3.toIsom_smul (M : ↥SO3) (x : E) : SO3.toIsom M • x = M • x := rfl

/-! ### Fixed points of a rotation -/

private theorem transpose_mulVec_cross (M : Matrix (Fin 3) (Fin 3) ℝ) (v w : Fin 3 → ℝ) :
    Mᵀ *ᵥ ((M *ᵥ v) ⨯₃ (M *ᵥ w)) = M.det • (v ⨯₃ w) := by
  ext i
  fin_cases i <;>
    simp [cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.det_fin_three,
      Matrix.transpose_apply] <;> ring

private theorem cross_dot_self (v w : Fin 3 → ℝ) :
    (v ⨯₃ w) ⬝ᵥ (v ⨯₃ w) = (v ⬝ᵥ v) * (w ⬝ᵥ w) - (v ⬝ᵥ w) ^ 2 := by
  simp [cross_apply, dotProduct, Fin.sum_univ_three]; ring

private theorem det_of_three (u v w : Fin 3 → ℝ) :
    Matrix.det (Matrix.of ![u, v, w]) = u ⬝ᵥ (v ⨯₃ w) := by
  simp [Matrix.det_fin_three, cross_apply, dotProduct, Fin.sum_univ_three]; ring

/-- A rotation fixing two "independent" unit vectors is the identity. -/
theorem matrix_eq_one_of_two_fixed {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hMt' : M * Mᵀ = 1) (hdet : M.det = 1) {p q : Fin 3 → ℝ} (hp : p ⬝ᵥ p = 1) (hq : q ⬝ᵥ q = 1)
    (hpq : (p ⬝ᵥ q) ^ 2 ≠ 1) (hMp : M *ᵥ p = p) (hMq : M *ᵥ q = q) : M = 1 := by
  set u := p ⨯₃ q with hu
  have hMu : M *ᵥ u = u := by
    have h1 : Mᵀ *ᵥ u = u := by
      have := transpose_mulVec_cross M p q
      rw [hMp, hMq, hdet, one_smul] at this
      exact this
    calc M *ᵥ u = M *ᵥ (Mᵀ *ᵥ u) := by rw [h1]
      _ = (M * Mᵀ) *ᵥ u := by rw [Matrix.mulVec_mulVec]
      _ = u := by rw [hMt', Matrix.one_mulVec]
  have huu : u ⬝ᵥ u = 1 - (p ⬝ᵥ q) ^ 2 := by
    rw [hu, cross_dot_self, hp, hq]; ring
  have hune : u ⬝ᵥ u ≠ 0 := by
    rw [huu]
    intro h
    exact hpq (by linarith)
  set N : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![u, p, q] with hN
  have hdetN : N.det ≠ 0 := by
    rw [hN, det_of_three]
    exact hune
  have hrows : ∀ i, M *ᵥ (N i) = N i := by
    intro i
    fin_cases i
    · exact hMu
    · exact hMp
    · exact hMq
  have hNM : N * Mᵀ = N := by
    ext i j
    have := congrFun (hrows i) j
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have : N⁻¹ * (N * Mᵀ) = N⁻¹ * N := by rw [hNM]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul N (by simpa using hdetN), Matrix.one_mul] at this
  have hMT : Mᵀ = 1 := this
  have : M = Mᵀᵀ := (Matrix.transpose_transpose M).symm
  rw [this, hMT, Matrix.transpose_one]

/-- Two unit vectors whose inner product has absolute value one are equal up to sign. -/
theorem unit_eq_of_dot_sq_eq_one {p q : Fin 3 → ℝ} (hp : p ⬝ᵥ p = 1) (hq : q ⬝ᵥ q = 1)
    (h : (p ⬝ᵥ q) ^ 2 = 1) : q = p ∨ q = -p := by
  set c := p ⬝ᵥ q with hc
  have hr : (q - c • p) ⬝ᵥ (q - c • p) = 0 := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, hp, hq,
      smul_eq_mul]
    rw [dotProduct_comm q p, ← hc]
    nlinarith [h]
  have hq' : q = c • p := by
    have h0 : q - c • p = 0 := dotProduct_self_eq_zero.mp hr
    have := sub_eq_zero.mp h0
    exact this
  have hcc : (c - 1) * (c + 1) = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp hcc with h1 | h1
  · left
    rw [hq', show c = 1 by linarith, one_smul]
  · right
    rw [hq', show c = -1 by linarith]
    ext i
    simp

end BanachTarski

import Mathlib

/-!
# Equidecomposability and paradoxical decompositions

This file develops the elementary theory of equidecomposability of subsets of a `G`-set `X`.

Two sets `A B ⊆ X` are *equidecomposable* if there is a bijection `A → B` which is piecewise
given by finitely many elements of `G`.  This is equivalent to the usual formulation with
finite partitions (see `RequestProject.Pieces`), but is much more convenient to work with.
-/

namespace BanachTarski

open scoped Pointwise

variable {G X : Type*} [Group G] [MulAction G X]

/-- `A` and `B` are equidecomposable with respect to the group `G` acting on `X`: there is a
bijection from `A` to `B` which is piecewise given by finitely many elements of `G`. -/
def Equidecomp (G : Type*) [Group G] {X : Type*} [MulAction G X] (A B : Set X) : Prop :=
  ∃ (f : X → X) (S : Set G), S.Finite ∧ Set.BijOn f A B ∧ ∀ x ∈ A, ∃ g ∈ S, f x = g • x

namespace Equidecomp

theorem refl (A : Set X) : Equidecomp G A A :=
  ⟨id, {1}, Set.finite_singleton _, Set.bijOn_id _, fun x _ => ⟨1, rfl, by simp⟩⟩

theorem symm [Nonempty X] {A B : Set X} (h : Equidecomp G A B) : Equidecomp G B A := by
  obtain ⟨f, S, hSfin, hbij, hS⟩ := h
  refine ⟨Function.invFunOn f A, S⁻¹, hSfin.inv, hbij.invOn_invFunOn.symm.bijOn ?_ ?_, ?_⟩
  · intro y hy
    exact Function.invFunOn_mem (hbij.surjOn hy)
  · intro x hx
    exact hbij.mapsTo hx
  · intro y hy
    have hx : Function.invFunOn f A y ∈ A := Function.invFunOn_mem (hbij.surjOn hy)
    have hfx : f (Function.invFunOn f A y) = y := Function.invFunOn_eq (hbij.surjOn hy)
    obtain ⟨g, hg, hgx⟩ := hS _ hx
    refine ⟨g⁻¹, by simpa using hg, ?_⟩
    rw [hgx] at hfx
    conv_rhs => rw [← hfx]
    rw [inv_smul_smul]

theorem trans {A B C : Set X} (h₁ : Equidecomp G A B) (h₂ : Equidecomp G B C) :
    Equidecomp G A C := by
  obtain ⟨f₁, S₁, hS₁, hb₁, hs₁⟩ := h₁
  obtain ⟨f₂, S₂, hS₂, hb₂, hs₂⟩ := h₂
  refine ⟨f₂ ∘ f₁, S₂ * S₁, hS₂.mul hS₁, hb₂.comp hb₁, ?_⟩
  intro x hx
  obtain ⟨g₁, hg₁, h₁⟩ := hs₁ x hx
  obtain ⟨g₂, hg₂, h₂⟩ := hs₂ (f₁ x) (hb₁.mapsTo hx)
  exact ⟨g₂ * g₁, Set.mul_mem_mul hg₂ hg₁, by
    rw [Function.comp_apply, h₂, h₁, mul_smul]⟩

/-- Equidecomposability of a union of two disjoint pieces. -/
theorem union {A₁ A₂ B₁ B₂ : Set X} (h₁ : Equidecomp G A₁ B₁) (h₂ : Equidecomp G A₂ B₂)
    (hA : Disjoint A₁ A₂) (hB : Disjoint B₁ B₂) :
    Equidecomp G (A₁ ∪ A₂) (B₁ ∪ B₂) := by
  classical
  obtain ⟨f₁, S₁, hS₁, hb₁, hs₁⟩ := h₁
  obtain ⟨f₂, S₂, hS₂, hb₂, hs₂⟩ := h₂
  refine ⟨fun x => if x ∈ A₁ then f₁ x else f₂ x, S₁ ∪ S₂, hS₁.union hS₂, ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro x (hx | hx)
    · simp only [if_pos hx]; exact Or.inl (hb₁.mapsTo hx)
    · have hx1 : x ∉ A₁ := fun h => Set.disjoint_left.mp hA h hx
      simp only [if_neg hx1]; exact Or.inr (hb₂.mapsTo hx)
  · rintro x hx y hy hxy
    have hx' : x ∈ A₁ ∨ (x ∉ A₁ ∧ x ∈ A₂) := by
      rcases hx with h | h
      · exact Or.inl h
      · by_cases h1 : x ∈ A₁
        · exact Or.inl h1
        · exact Or.inr ⟨h1, h⟩
    have hy' : y ∈ A₁ ∨ (y ∉ A₁ ∧ y ∈ A₂) := by
      rcases hy with h | h
      · exact Or.inl h
      · by_cases h1 : y ∈ A₁
        · exact Or.inl h1
        · exact Or.inr ⟨h1, h⟩
    rcases hx' with hx1 | ⟨hx1, hx2⟩ <;> rcases hy' with hy1 | ⟨hy1, hy2⟩
    · simp only [if_pos hx1, if_pos hy1] at hxy; exact hb₁.injOn hx1 hy1 hxy
    · simp only [if_pos hx1, if_neg hy1] at hxy
      exact absurd (by rw [hxy]; exact hb₂.mapsTo hy2 : f₁ x ∈ B₂)
        (Set.disjoint_left.mp hB (hb₁.mapsTo hx1))
    · simp only [if_neg hx1, if_pos hy1] at hxy
      exact absurd (by rw [hxy]; exact hb₁.mapsTo hy1 : f₂ x ∈ B₁)
        (Set.disjoint_right.mp hB (hb₂.mapsTo hx2))
    · simp only [if_neg hx1, if_neg hy1] at hxy; exact hb₂.injOn hx2 hy2 hxy
  · rintro y (hy | hy)
    · obtain ⟨x, hx, rfl⟩ := hb₁.surjOn hy
      exact ⟨x, Or.inl hx, by simp [if_pos hx]⟩
    · obtain ⟨x, hx, rfl⟩ := hb₂.surjOn hy
      have hx1 : x ∉ A₁ := fun h => Set.disjoint_left.mp hA h hx
      exact ⟨x, Or.inr hx, by simp [if_neg hx1]⟩
  · rintro x (hx | hx)
    · obtain ⟨g, hg, hgx⟩ := hs₁ x hx
      exact ⟨g, Or.inl hg, by simpa [if_pos hx] using hgx⟩
    · have hx1 : x ∉ A₁ := fun h => Set.disjoint_left.mp hA h hx
      obtain ⟨g, hg, hgx⟩ := hs₂ x hx
      exact ⟨g, Or.inr hg, by simpa [if_neg hx1] using hgx⟩

/-- A set is equidecomposable with any translate of itself. -/
theorem smul_set (g : G) (A : Set X) : Equidecomp G A (g • A) := by
  refine ⟨fun x => g • x, {g}, Set.finite_singleton _, ⟨?_, ?_, ?_⟩, fun x _ => ⟨g, rfl, rfl⟩⟩
  · intro x hx; exact ⟨x, hx, rfl⟩
  · intro x _ y _ h; exact MulAction.injective g h
  · rintro y ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

/-- Any part of `A` can be matched with a part of `B`, with matching complements. -/
theorem subset_image {A B W : Set X} (h : Equidecomp G A B) (hW : W ⊆ A) :
    ∃ B' ⊆ B, Equidecomp G W B' ∧ Equidecomp G (A \ W) (B \ B') := by
  obtain ⟨f, S, hSfin, hbij, hS⟩ := h
  refine ⟨f '' W, ?_, ⟨f, S, hSfin, ⟨Set.mapsTo_image f W, hbij.injOn.mono hW, ?_⟩,
      fun x hx => hS x (hW hx)⟩, ⟨f, S, hSfin, ⟨?_, hbij.injOn.mono Set.diff_subset, ?_⟩,
      fun x hx => hS x hx.1⟩⟩
  · rintro y ⟨x, hx, rfl⟩; exact hbij.mapsTo (hW hx)
  · rintro y ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro x ⟨hx, hxW⟩
    refine ⟨hbij.mapsTo hx, ?_⟩
    rintro ⟨w, hw, hwx⟩
    exact hxW (hbij.injOn (hW hw) hx hwx ▸ hw)
  · rintro y ⟨hy, hy'⟩
    obtain ⟨x, hx, rfl⟩ := hbij.surjOn hy
    exact ⟨x, ⟨hx, fun hxW => hy' ⟨x, hxW, rfl⟩⟩, rfl⟩

/-- Transport equidecomposability along a group homomorphism compatible with the actions. -/
theorem map {H : Type*} [Group H] [MulAction H X] (σ : G →* H)
    (hσ : ∀ (g : G) (x : X), σ g • x = g • x) {A B : Set X} (h : Equidecomp G A B) :
    Equidecomp H A B := by
  obtain ⟨f, S, hSfin, hbij, hS⟩ := h
  refine ⟨f, σ '' S, hSfin.image _, hbij, fun x hx => ?_⟩
  obtain ⟨g, hg, hgx⟩ := hS x hx
  exact ⟨σ g, ⟨g, hg, rfl⟩, by rw [hσ, hgx]⟩

end Equidecomp

/-- `A` is `G`-paradoxical: it splits into two disjoint pieces, each equidecomposable with
the whole of `A`. -/
def Paradoxical (G : Type*) [Group G] {X : Type*} [MulAction G X] (A : Set X) : Prop :=
  ∃ Y₁ Y₂ : Set X, Y₁ ∪ Y₂ = A ∧ Disjoint Y₁ Y₂ ∧ Equidecomp G Y₁ A ∧ Equidecomp G Y₂ A

/-- Paradoxicality is invariant under equidecomposability. -/
theorem Paradoxical.congr [Nonempty X] {A B : Set X} (hA : Paradoxical G A)
    (hAB : Equidecomp G A B) : Paradoxical G B := by
  obtain ⟨Y₁, Y₂, hunion, hdisj, h₁, h₂⟩ := hA
  have hY₁ : Y₁ ⊆ A := hunion ▸ Set.subset_union_left
  obtain ⟨Z₁, hZ₁B, hZ₁, hZ₂⟩ := hAB.subset_image hY₁
  have hdiff : A \ Y₁ = Y₂ := by
    rw [← hunion]
    ext x
    simp only [Set.mem_diff, Set.mem_union]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact absurd h h'
      · exact h
    · intro h
      exact ⟨Or.inr h, fun h' => Set.disjoint_left.mp hdisj h' h⟩
  rw [hdiff] at hZ₂
  refine ⟨Z₁, B \ Z₁, by simp [Set.union_diff_cancel' (le_refl _) hZ₁B], ?_, ?_, ?_⟩
  · exact Set.disjoint_sdiff_right
  · exact (hZ₁.symm.trans h₁).trans hAB
  · exact (hZ₂.symm.trans h₂).trans hAB

/-- Transport paradoxicality along a group homomorphism compatible with the actions. -/
theorem Paradoxical.map {H : Type*} [Group H] [MulAction H X] (σ : G →* H)
    (hσ : ∀ (g : G) (x : X), σ g • x = g • x) {A : Set X} (h : Paradoxical G A) :
    Paradoxical H A := by
  obtain ⟨Y₁, Y₂, hu, hd, h₁, h₂⟩ := h
  exact ⟨Y₁, Y₂, hu, hd, h₁.map σ hσ, h₂.map σ hσ⟩

end BanachTarski

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

