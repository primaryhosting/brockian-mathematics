import RequestProject.Paradoxical

/-!
# Banach Tarski: a free group of rotations of `ℝ³`
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

namespace Frontier

open Set Function

/-! ## A free group of rotations of `ℝ³`

Following the classical argument, the two rotations by `arccos (3/5)` about the `z`- and the
`x`-axis generate a free subgroup of `SO(3)`.  Freeness is proved by a `5`-adic argument:
a nonempty reduced word of length `n`, applied to the integral vector `(1,0,2)` and rescaled
by `5 ^ n`, gives an integral vector which is nonzero modulo `5`.
-/

namespace FreeRotations

open Matrix

/-- The special orthogonal group of `ℝ³`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩


theorem isParadoxical_of_freeAction (Y : Set X)
    (hYinv : ∀ (h : H) {x : X}, x ∈ Y → h • x ∈ Y)
    (hfree : ∀ (h : H) {x : X}, x ∈ Y → h • x = x → h = 1)
    (hpar : IsParadoxical H (Set.univ : Set H)) : IsParadoxical H Y := by
  classical
  -- a choice of orbit representatives
  obtain ⟨rep, hrep_ex, hrep_smul⟩ :
      ∃ rep : X → X, (∀ x : X, ∃ h : H, x = h • rep x) ∧ (∀ (h : H) (x : X), rep (h • x) = rep x) := by
    refine ⟨fun x => Quotient.out (Quotient.mk (MulAction.orbitRel H X) x), ?_, ?_⟩
    · intro x
      have h0 : (MulAction.orbitRel H X) (Quotient.out (Quotient.mk (MulAction.orbitRel H X) x)) x :=
        Quotient.mk_out (s := MulAction.orbitRel H X) x
      rw [MulAction.orbitRel_apply] at h0
      obtain ⟨h, hh⟩ := h0
      exact ⟨h⁻¹, by simp [← hh]⟩
    · intro h x
      exact congrArg Quotient.out (Quotient.sound
        (show (MulAction.orbitRel H X) (h • x) x from (MulAction.orbitRel_apply).2 ⟨h, rfl⟩))
  choose elem helem using hrep_ex
  have hrep_eq : ∀ x : X, rep x = (elem x)⁻¹ • x := fun x =>
    eq_inv_smul_iff.mpr (helem x).symm
  have hrep_mem : ∀ {x : X}, x ∈ Y → rep x ∈ Y := by
    intro x hx; rw [hrep_eq]; exact hYinv _ hx
  -- the key equivariance property of the coefficient function `elem`
  have key : ∀ (h : H) {x : X}, x ∈ Y → elem (h • x) = h * elem x := by
    intro h x hx
    have h1 : h • x = elem (h • x) • rep x := by
      conv_lhs => rw [helem (h • x)]
      rw [hrep_smul]
    have h2 : h • x = (h * elem x) • rep x := by
      conv_lhs => rw [helem x]
      rw [mul_smul]
    have h3 : ((elem (h • x))⁻¹ * (h * elem x)) • rep x = rep x := by
      rw [mul_smul, ← h2, inv_smul_eq_iff]
      exact h1
    have h4 : (elem (h • x))⁻¹ * (h * elem x) = 1 := hfree _ (hrep_mem hx) h3
    have h5 := congrArg (fun z => elem (h • x) * z) h4
    simpa [← mul_assoc] using h5.symm
  -- the main construction
  have main : ∀ f : Equidecomp H H, f.target = Set.univ →
      IsEquidecomposable H {x | x ∈ Y ∧ elem x ∈ f.source} Y := by
    intro f hft
    have hmapY : ∀ {x : X}, x ∈ Y → ∀ c : H, c • x ∈ Y := fun hx c => hYinv c hx
    have hsrc : ∀ y : X, f.toPartialEquiv.symm (elem y) ∈ f.source := fun y =>
      f.toPartialEquiv.map_target (by rw [hft]; trivial)
    set F : X → X := fun x => (f (elem x) * (elem x)⁻¹) • x with hF
    set Fi : X → X := fun x => (f.toPartialEquiv.symm (elem x) * (elem x)⁻¹) • x with hFi
    have hFel : ∀ {x : X}, x ∈ Y → elem (F x) = f (elem x) := by
      intro x hx
      have := key (f (elem x) * (elem x)⁻¹) hx
      rw [hF]
      simpa [mul_assoc] using this
    have hFiel : ∀ {y : X}, y ∈ Y → elem (Fi y) = f.toPartialEquiv.symm (elem y) := by
      intro y hy
      have := key (f.toPartialEquiv.symm (elem y) * (elem y)⁻¹) hy
      rw [hFi]
      simpa [mul_assoc] using this
    refine ⟨⟨⟨F, Fi, {x | x ∈ Y ∧ elem x ∈ f.source}, Y, ?_, ?_, ?_, ?_⟩, ?_⟩, rfl, rfl⟩
    · rintro x ⟨hx, -⟩; exact hmapY hx _
    · intro y hy
      exact ⟨hmapY hy _, by rw [hFiel hy]; exact hsrc y⟩
    · rintro x ⟨hx, hxs⟩
      have h1 : Fi (F x) = (f.toPartialEquiv.symm (elem (F x)) * (elem (F x))⁻¹) • F x := rfl
      rw [h1, hFel hx, f.toPartialEquiv.left_inv hxs, hF]
      simp only [← mul_smul]
      group
      simp
    · intro y hy
      have h1 : F (Fi y) = (f (elem (Fi y)) * (elem (Fi y))⁻¹) • Fi y := rfl
      rw [h1, hFiel hy, f.toPartialEquiv.right_inv (by rw [hft]; trivial), hFi]
      simp only [← mul_smul]
      group
      simp
    · refine ⟨f.witness, ?_⟩
      rintro x ⟨-, hxs⟩
      obtain ⟨g, hg, hgx⟩ := f.isDecompOn (elem x) hxs
      refine ⟨g, hg, ?_⟩
      show F x = g • x
      rw [hF]
      simp only [hgx, smul_eq_mul, mul_inv_cancel_right]
  obtain ⟨A₁, A₂, -, -, hdisj, ⟨f₁, hf₁s, hf₁t⟩, ⟨f₂, hf₂s, hf₂t⟩⟩ := hpar
  refine ⟨{x | x ∈ Y ∧ elem x ∈ f₁.source}, {x | x ∈ Y ∧ elem x ∈ f₂.source},
    fun x hx => hx.1, fun x hx => hx.1, ?_, main f₁ hf₁t, main f₂ hf₂t⟩
  rw [Set.disjoint_left]
  rintro x ⟨-, hx₁⟩ ⟨-, hx₂⟩
  rw [hf₁s] at hx₁
  rw [hf₂s] at hx₂
  exact (Set.disjoint_left.1 hdisj hx₁) hx₂

end Transfer

/-! ## Basic properties of equidecomposability -/

section Algebra

variable {G X : Type*} [Group G] [MulAction G X]

