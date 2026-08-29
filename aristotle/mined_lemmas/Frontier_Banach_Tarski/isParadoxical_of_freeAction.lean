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
# Rotations of three dimensional Euclidean space

Explicit rotations about the `z`- and `x`-axes, the cross product, and the fact that a
nontrivial rotation fixes at most two points of the unit sphere.
-/

open scoped RealInnerProductSpace

namespace BT

/-- Three dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- A vector of `E3` given by its three coordinates. -/

theorem isParadoxical_of_freeAction {X G : Type*} [Group G] [MulAction G X]
    (φ : F →* G) (E : Set X)
    (hinv : ∀ (w : F) {x : X}, x ∈ E → φ w • x ∈ E)
    (hfree : ∀ (w : F) {x : X}, x ∈ E → w ≠ 1 → φ w • x ≠ x) :
    IsParadoxical G E := by
  classical
  -- the orbit equivalence relation
  let s : Setoid X :=
    { r := fun x y => ∃ w : F, φ w • x = y
      iseqv :=
        { refl := fun x => ⟨1, by simp⟩
          symm := by
            rintro x y ⟨w, rfl⟩
            exact ⟨w⁻¹, by rw [map_inv, inv_smul_smul]⟩
          trans := by
            rintro x y z ⟨w₁, rfl⟩ ⟨w₂, rfl⟩
            exact ⟨w₂ * w₁, by rw [map_mul, mul_smul]⟩ } }
  set rep : X → X := fun x => (Quotient.mk s x).out with hrep_def
  have hrep_rel : ∀ x : X, ∃ w : F, φ w • rep x = x := by
    intro x
    exact Quotient.exact (Quotient.out_eq (Quotient.mk s x))
  have hrep_eq : ∀ x y : X, (∃ w : F, φ w • x = y) → rep x = rep y := by
    intro x y h
    simp only [hrep_def]
    congr 1
    exact Quotient.sound h
  set ww : X → F := fun x => (hrep_rel x).choose with hww_def
  have hww : ∀ x : X, φ (ww x) • rep x = x := fun x => (hrep_rel x).choose_spec
  have hrepE : ∀ {x : X}, x ∈ E → rep x ∈ E := by
    intro x hx
    obtain ⟨w, hw⟩ := hrep_rel x
    have hx' : rep x = φ w⁻¹ • x := by
      conv_rhs => rw [← hw]
      rw [map_inv, inv_smul_smul]
    rw [hx']
    exact hinv _ hx
  have huniq : ∀ {m : X}, m ∈ E → ∀ u v : F, φ u • m = φ v • m → u = v := by
    intro m hm u v huv
    have h1 : φ (v⁻¹ * u) • m = m := by
      rw [map_mul, mul_smul, huv, map_inv, inv_smul_smul]
    by_contra hne
    exact hfree (v⁻¹ * u) hm (fun h0 => hne (inv_mul_eq_one.mp h0).symm) h1
  have hww_smul : ∀ (u : F) {x : X}, x ∈ E → ww (φ u • x) = u * ww x := by
    intro u x hx
    have h1 : rep (φ u • x) = rep x := (hrep_eq x (φ u • x) ⟨u, rfl⟩).symm
    have h2 : φ (ww (φ u • x)) • rep x = φ u • x := by
      rw [← h1]; exact hww _
    have h3 : φ (u * ww x) • rep x = φ u • x := by rw [map_mul, mul_smul, hww x]
    exact huniq (hrepE hx) _ _ (h2.trans h3.symm)
  -- pieces of `E` indexed by subsets of the free group
  set P : Set F → Set X := fun S => {x | x ∈ E ∧ ww x ∈ S} with hP_def
  have hP_sub : ∀ S, P S ⊆ E := fun S x hx => hx.1
  have hP_smul : ∀ (u : F) (S : Set F), φ u • P S = P (u • S) := by
    intro u S
    ext y
    constructor
    · rintro ⟨x, ⟨hxE, hxS⟩, rfl⟩
      refine ⟨hinv _ hxE, ?_⟩
      rw [hww_smul u hxE]
      exact ⟨ww x, hxS, rfl⟩
    · rintro ⟨hyE, v, hvS, hv⟩
      have hv' : u * v = ww y := hv
      refine ⟨φ u⁻¹ • y, ⟨hinv _ hyE, ?_⟩, ?_⟩
      · rw [hww_smul u⁻¹ hyE, ← hv']
        simpa using hvS
      · show φ u • (φ u⁻¹ • y) = y
        rw [map_inv, smul_inv_smul]
  have hP_disj : ∀ S T : Set F, Disjoint S T → Disjoint (P S) (P T) := by
    intro S T hST
    rw [Set.disjoint_left]
    rintro x ⟨-, hxS⟩ ⟨-, hxT⟩
    exact (hST.le_bot ⟨hxS, hxT⟩ : ww x ∈ (⊥ : Set F))
  obtain ⟨A, B, C, D, hcover, hAB, hCD, hABCD, hcovA, hdisA, hcovC, hdisC⟩ :=
    exists_paradoxical_partition
  refine ⟨P A ∪ P B, P C ∪ P D, ?_, ?_, ?_, ?_⟩
  · -- the two parts cover `E`
    apply Set.Subset.antisymm
    · rintro x ((hx | hx) | (hx | hx)) <;> exact hx.1
    · intro x hx
      rcases hcover (ww x) with h | h | h | h
      · exact Or.inl (Or.inl ⟨hx, h⟩)
      · exact Or.inl (Or.inr ⟨hx, h⟩)
      · exact Or.inr (Or.inl ⟨hx, h⟩)
      · exact Or.inr (Or.inr ⟨hx, h⟩)
  · -- the two parts are disjoint
    rw [Set.disjoint_left]
    rintro x hx hx'
    have h1 : ww x ∈ A ∪ B := by
      rcases hx with h | h
      · exact Or.inl h.2
      · exact Or.inr h.2
    have h2 : ww x ∈ C ∪ D := by
      rcases hx' with h | h
      · exact Or.inl h.2
      · exact Or.inr h.2
    exact (hABCD.le_bot ⟨h1, h2⟩ : ww x ∈ (⊥ : Set F))
  · -- first part is equidecomposable with `E`
    refine Equidecomposable.ofTwoPieces (1 : G) (φ ga) (hP_disj _ _ hAB) ?_ ?_
    · rw [MulAction.one_smul, hP_smul]
      exact hP_disj _ _ hdisA
    · rw [MulAction.one_smul, hP_smul]
      apply Set.Subset.antisymm
      · intro x hx
        rcases hcovA (ww x) with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
      · rintro x (hx | hx) <;> exact hx.1
  · -- second part is equidecomposable with `E`
    refine Equidecomposable.ofTwoPieces (1 : G) (φ gb) (hP_disj _ _ hCD) ?_ ?_
    · rw [MulAction.one_smul, hP_smul]
      exact hP_disj _ _ hdisC
    · rw [MulAction.one_smul, hP_smul]
      apply Set.Subset.antisymm
      · intro x hx
        rcases hcovC (ww x) with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
      · rintro x (hx | hx) <;> exact hx.1

end BT

import Mathlib

/-!
# Equidecomposability and paradoxical sets

Basic definitions and API used in the formalization of the Banach–Tarski paradox.
-/

open Set Pointwise

namespace BT

/-- The isometry group of a metric space acts on the space. -/
instance isometryEquivAction (M : Type*) [PseudoEMetricSpace M] : MulAction (M ≃ᵢ M) M where
  smul g x := g x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

