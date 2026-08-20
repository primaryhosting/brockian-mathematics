/-
Absorbing the countable set of poles: the unit sphere is `SO(3)`-paradoxical.
-/
import RequestProject.Sphere

open Matrix Set Pointwise

namespace BT

noncomputable section

/-! ### Countability of the solution sets of rotation equations -/

/-- For a point `d` off the `z`-axis, only countably many angles `t` satisfy
`rZ (c * t) • d = d'`. -/

theorem Equidec.absorb {A D : Set X} (rho : G)
    (hsub : ∀ n : ℕ, (rho ^ n) • D ⊆ A)
    (hdisj : ∀ n : ℕ, 1 ≤ n → Disjoint ((rho ^ n) • D) D) :
    Equidec G A (A \ D) := by
  set U : Set X := ⋃ n : ℕ, (rho ^ n) • D with hU
  have hUA : U ⊆ A := Set.iUnion_subset hsub
  have hDU : D ⊆ U := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨0, by simpa using hx⟩
  have hrhoU : rho • U = U \ D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hy
      have hmem : rho • y ∈ (rho ^ (n + 1)) • D := by
        obtain ⟨d, hd, rfl⟩ := hn
        exact ⟨d, hd, by rw [← mul_smul, ← pow_succ']⟩
      refine ⟨Set.mem_iUnion.2 ⟨n + 1, hmem⟩, ?_⟩
      intro hxD
      exact ((hdisj (n + 1) (Nat.le_add_left 1 n)).le_bot ⟨hmem, hxD⟩ : _ ∈ (⊥ : Set X))
    · rintro ⟨hxU, hxD⟩
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hxU
      match n, hn with
      | 0, hn => exact absurd (by simpa using hn) hxD
      | (m + 1), hn =>
        obtain ⟨d, hd, rfl⟩ := hn
        refine ⟨(rho ^ m) • d, Set.mem_iUnion.2 ⟨m, ⟨d, hd, rfl⟩⟩, ?_⟩
        show rho • (rho ^ m • d) = rho ^ (m + 1) • d
        rw [← mul_smul, ← pow_succ']
  have hsplit : A = U ∪ (A \ U) := by
    rw [Set.union_diff_cancel hUA]
  have hsplit' : A \ D = (U \ D) ∪ (A \ U) := by
    ext x
    simp only [Set.mem_diff, Set.mem_union]
    constructor
    · rintro ⟨hxA, hxD⟩
      by_cases hxU : x ∈ U
      · exact Or.inl ⟨hxU, hxD⟩
      · exact Or.inr ⟨hxA, hxU⟩
    · rintro (⟨hxU, hxD⟩ | ⟨hxA, hxU⟩)
      · exact ⟨hUA hxU, hxD⟩
      · exact ⟨hxA, fun hxD => hxU (hDU hxD)⟩
  have key : Equidec G (U ∪ (A \ U)) ((U \ D) ∪ (A \ U)) := by
    refine Equidec.union ?_ (Equidec.refl _) ?_ ?_
    · have h := Equidec.smul_set rho U
      rwa [hrhoU] at h
    · exact Set.disjoint_sdiff_right.mono_left le_rfl
    · exact Set.disjoint_of_subset_left Set.diff_subset Set.disjoint_sdiff_right
  rw [← hsplit'] at key
  rw [← hsplit] at key
  exact key

end Basic

end BT

/-
From the sphere to the ball: the Banach–Tarski paradox.
-/
import RequestProject.Absorb

open Matrix Set Pointwise

namespace BT

noncomputable section

/-! ### The isometry group of `ℝ³` acting on `ℝ³` -/

/-- The group of isometries of `ℝ³`. -/
abbrev Iso3 := E ≃ᵢ E

instance : MulAction Iso3 E where
  smul g x := g x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

