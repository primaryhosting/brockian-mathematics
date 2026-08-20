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


theorem IsEquidecomposable.image {A B A₁ : Set X} (h : IsEquidecomposable G A B) (hA₁ : A₁ ⊆ A) :
    ∃ B₁ ⊆ B, IsEquidecomposable G A₁ B₁ ∧
      ∀ A₂ ⊆ A, Disjoint A₁ A₂ → ∃ B₂ ⊆ B, IsEquidecomposable G A₂ B₂ ∧ Disjoint B₁ B₂ := by
  obtain ⟨f, hfs, hft⟩ := h
  have himg : ∀ S : Set X, S ⊆ A → IsEquidecomposable G S (f.toPartialEquiv '' S) ∧
      f.toPartialEquiv '' S ⊆ B := by
    intro S hS
    have hSsub : S ⊆ f.source := by rw [hfs]; exact hS
    refine ⟨⟨f.restr S, Equidecomp.source_restr f hSsub, ?_⟩, ?_⟩
    · show (f.toPartialEquiv.restr S).target = f.toPartialEquiv '' S
      rw [PartialEquiv.restr_target, f.toPartialEquiv.image_eq_target_inter_inv_preimage hSsub]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← hft]
      exact f.toPartialEquiv.map_source (hSsub hx)
  obtain ⟨h₁, hb₁⟩ := himg A₁ hA₁
  refine ⟨f.toPartialEquiv '' A₁, hb₁, h₁, ?_⟩
  intro A₂ hA₂ hdisj
  obtain ⟨h₂, hb₂⟩ := himg A₂ hA₂
  refine ⟨f.toPartialEquiv '' A₂, hb₂, h₂, ?_⟩
  rw [Set.disjoint_left]
  rintro y ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂, hx₂'⟩
  have hx₁s : x₁ ∈ f.source := by rw [hfs]; exact hA₁ hx₁
  have hx₂s : x₂ ∈ f.source := by rw [hfs]; exact hA₂ hx₂
  have : x₂ = x₁ := by
    have h1 := f.toPartialEquiv.left_inv hx₁s
    have h2 := f.toPartialEquiv.left_inv hx₂s
    rw [← h1, ← h2, hx₂']
  rw [this] at hx₂
  exact (Set.disjoint_left.1 hdisj hx₁) hx₂

/-- Paradoxicality is invariant under equidecomposability. -/
