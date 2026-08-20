import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# Molecular point groups are finite subgroups of O(3)

A *molecule* is modelled as an assignment of an atomic number to each point of
Euclidean 3-space, with only finitely many points carrying an atom (the atoms),
placed so that the atoms are not all contained in a single line through the
origin (equivalently, the linear span of the atom positions has dimension at
least 2).  As is standard in chemistry, the origin is taken to be the fixed
point common to all symmetry operations (e.g. the centre of mass).

The *point group* of the molecule is the group of all linear isometries of
Euclidean 3-space (i.e. elements of `O(3)`) that map every point to a point
carrying the same atomic number.  By construction this is a subgroup of `O(3)`;
the main theorem `Chem.point_group_finite_O3` shows that it is finite.

The hypothesis that the atoms do not all lie on one line through the origin is
necessary: for a linear molecule the corresponding group contains all rotations
about the molecular axis and is infinite (the point groups `C∞v`, `D∞h`).
-/

namespace Chem

/-- Euclidean three-space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The orthogonal group `O(3)`: the group of linear isometries of Euclidean
three-space onto itself. -/
abbrev O3 : Type := E3 ≃ₗᵢ[ℝ] E3

/-- A molecule: an atomic-number function on Euclidean three-space with finite
support (the atoms), whose atoms span a subspace of dimension at least `2`
(i.e. the atoms are not all on a single line through the origin). -/
structure Molecule where
  /-- `atomicNumber x` is the atomic number of the atom sitting at `x`
  (`0` meaning that there is no atom at `x`). -/
  atomicNumber : E3 → ℕ
  /-- A molecule has finitely many atoms. -/
  finite_support : (Function.support atomicNumber).Finite
  /-- The atoms are not all contained in a line through the origin. -/
  two_le_finrank :
    2 ≤ Module.finrank ℝ (Submodule.span ℝ (Function.support atomicNumber))

namespace Molecule

variable (M : Molecule)

/-- The set of positions occupied by atoms of the molecule. -/

theorem finite_of_stabilizes_finite_set (S : Set E3) (hS : S.Finite)
    (hdim : 2 ≤ Module.finrank ℝ (Submodule.span ℝ S))
    (G : Subgroup O3) (hG : ∀ f ∈ G, ∀ x ∈ S, f x ∈ S) : Finite G := by
  classical
  haveI : Finite S := hS.to_subtype
  -- every element of `G` maps the span of `S` into itself
  have hmapV : ∀ f ∈ G, ∀ v ∈ Submodule.span ℝ S, (f : E3 → E3) v ∈ Submodule.span ℝ S := by
    intro f hf v hv
    have hle : Submodule.map (f.toLinearEquiv.toLinearMap) (Submodule.span ℝ S)
        ≤ Submodule.span ℝ S := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : (f : E3 → E3) x ∈ S := hG f hf x hx
      exact Submodule.subset_span (by simpa using hx')
    have hmem : (f.toLinearEquiv.toLinearMap) v ∈
        Submodule.map (f.toLinearEquiv.toLinearMap) (Submodule.span ℝ S) :=
      Submodule.mem_map_of_mem hv
    simpa using hle hmem
  -- hence also the orthogonal complement of that span into itself
  have hmapW : ∀ f ∈ G, ∀ w ∈ (Submodule.span ℝ S)ᗮ,
      (f : E3 → E3) w ∈ (Submodule.span ℝ S)ᗮ := by
    intro f hf w hw
    rw [Submodule.mem_orthogonal] at hw ⊢
    intro u hu
    have hfu : (f⁻¹ : O3) u ∈ Submodule.span ℝ S := hmapV f⁻¹ (G.inv_mem hf) u hu
    have h1 : ⟪(f⁻¹ : O3) u, w⟫ = 0 := hw _ hfu
    have h2 : ⟪u, (f : E3 → E3) w⟫ = ⟪(f⁻¹ : O3) u, w⟫ := by
      rw [← LinearIsometryEquiv.inner_map_map f ((f⁻¹ : O3) u) w]
      simp
    rw [h2]
    exact h1
  -- the orthogonal complement has dimension at most one
  have hsum : Module.finrank ℝ (Submodule.span ℝ S)
      + Module.finrank ℝ ((Submodule.span ℝ S)ᗮ) = 3 := by
    have h := Submodule.finrank_add_finrank_orthogonal (K := Submodule.span ℝ S) (𝕜 := ℝ)
    rw [h]
    simp
  have hW1 : Module.finrank ℝ ((Submodule.span ℝ S)ᗮ) ≤ 1 := by omega
  -- so it is spanned by a single vector `b`
  obtain ⟨b, hbW, hspanb⟩ : ∃ b : E3, b ∈ (Submodule.span ℝ S)ᗮ ∧
      (Submodule.span ℝ S)ᗮ = Submodule.span ℝ ({b} : Set E3) := by
    rcases eq_or_ne ((Submodule.span ℝ S)ᗮ) ⊥ with h | h
    · exact ⟨0, by simp, by simp [h]⟩
    · obtain ⟨b, hbW, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      refine ⟨b, hbW, (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm⟩
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact hbW
      · rw [finrank_span_singleton hb0]
        exact hW1
  -- `S ∪ {b}` spans all of `E3`
  have htop : Submodule.span ℝ (S ∪ ({b} : Set E3)) = ⊤ := by
    rw [Submodule.span_union, ← hspanb]
    exact (Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
      (K := Submodule.span ℝ S)).sup_eq_top
  -- every element of `G` fixes `b` up to sign
  have hsign : ∀ f ∈ G, (f : E3 → E3) b = b ∨ (f : E3 → E3) b = -b := by
    intro f hf
    have h1 : (f : E3 → E3) b ∈ Submodule.span ℝ ({b} : Set E3) := by
      rw [← hspanb]
      exact hmapW f hf b hbW
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 h1
    rcases eq_or_ne b 0 with hb0 | hb0
    · left
      rw [hb0]
      simp
    · have hnorm : ‖(f : E3 → E3) b‖ = ‖b‖ := f.norm_map b
      rw [← ht, norm_smul, Real.norm_eq_abs] at hnorm
      have hb : ‖b‖ ≠ 0 := by simpa using hb0
      have habs : |t| = 1 := by
        have : |t| * ‖b‖ = 1 * ‖b‖ := by rw [one_mul]; exact hnorm
        exact mul_right_cancel₀ hb this
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).1 habs with h | h
      · left
        rw [← ht, h, one_smul]
      · right
        rw [← ht, h, neg_one_smul]
  -- the injection into a finite type
  set Φ : G → ((S : Type) → (S : Type)) × Bool := fun f =>
    (fun x => ⟨(f : O3) (x : E3), hG (f : O3) f.2 (x : E3) x.2⟩,
      decide ((f : O3) b = b)) with hΦ
  have hinj : Function.Injective Φ := by
    intro f g hfg
    have h1 : ∀ x ∈ S, (f : O3) x = (g : O3) x := by
      intro x hx
      have h := congrArg (fun p => ((p.1 ⟨x, hx⟩ : (S : Type)) : E3)) hfg
      simpa [hΦ] using h
    have h2 : (f : O3) b = (g : O3) b := by
      have hb := congrArg Prod.snd hfg
      simp only [hΦ, decide_eq_decide] at hb
      by_cases hfb : (f : O3) b = b
      · rw [hfb, hb.1 hfb]
      · have hgb : (g : O3) b ≠ b := fun h => hfb (hb.2 h)
        rcases hsign (f : O3) f.2 with h | h
        · exact absurd h hfb
        · rcases hsign (g : O3) g.2 with h' | h'
          · exact absurd h' hgb
          · rw [h, h']
    have hall : ∀ x : E3, (f : O3) x = (g : O3) x := by
      intro x
      have hx : x ∈ Submodule.span ℝ (S ∪ ({b} : Set E3)) := by
        rw [htop]
        trivial
      induction hx using Submodule.span_induction with
      | mem y hy =>
          rcases hy with hy | hy
          · exact h1 y hy
          · simp only [Set.mem_singleton_iff] at hy
            subst hy
            exact h2
      | zero => simp
      | add u v _ _ hu hv => simp [map_add, hu, hv]
      | smul c u _ hu => simp [map_smul, hu]
    exact Subtype.ext (LinearIsometryEquiv.ext hall)
  exact Finite.of_injective Φ hinj

/-- **Every molecular point group is a finite subgroup of `O(3)`.**

By construction `Molecule.pointGroup M` is a `Subgroup` of
`O3 = E3 ≃ₗᵢ[ℝ] E3`, the orthogonal group of Euclidean three-space; this
