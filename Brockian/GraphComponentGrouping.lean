import Mathlib
import Brockian.GraphComponentMatrix

/-!
# Grouping connected-component products by component cardinality

This module supplies the finite-product bookkeeping used after a graph matrix has been decomposed
over its connected components. If every component has one, two, or three vertices and its factor
depends only on that cardinality, the total product is the corresponding product of three powers.
-/

namespace Brockian.GraphComponentGrouping

open Brockian.GraphComponentMatrix

noncomputable section

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Number of connected components of `G` having exactly `k` vertices. -/
def componentCount (G : SimpleGraph V) (k : Nat) : Nat := by
  exact Nat.card {c : G.ConnectedComponent // Nat.card (ComponentFiber G c) = k}

private theorem filter_card_eq_componentCount (G : SimpleGraph V)
    (s : Finset G.ConnectedComponent) (hs : ∀ c, c ∈ s) (k : Nat) :
    (s.filter (fun c => Nat.card (ComponentFiber G c) = k)).card =
      componentCount G k := by
  classical
  rw [componentCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply congrArg Finset.card
  ext c
  simp [hs c]

/-- Regroup a component-indexed product when every factor is determined by whether its component
has one, two, or three vertices. -/
theorem prod_components_eq_three_powers
    {R : Type v} [CommMonoid R] (G : SimpleGraph V)
    (s : Finset G.ConnectedComponent) (hs : ∀ c, c ∈ s)
    (f : G.ConnectedComponent -> R) (a1 a2 a3 : R)
    (hcard : ∀ c : G.ConnectedComponent,
      Nat.card (ComponentFiber G c) = 1 ∨
        Nat.card (ComponentFiber G c) = 2 ∨
        Nat.card (ComponentFiber G c) = 3)
    (hf1 : ∀ c, Nat.card (ComponentFiber G c) = 1 -> f c = a1)
    (hf2 : ∀ c, Nat.card (ComponentFiber G c) = 2 -> f c = a2)
    (hf3 : ∀ c, Nat.card (ComponentFiber G c) = 3 -> f c = a3) :
    ∏ c ∈ s, f c =
      a1 ^ componentCount G 1 * a2 ^ componentCount G 2 * a3 ^ componentCount G 3 := by
  classical
  let s1 : Finset G.ConnectedComponent :=
    s.filter (fun c => Nat.card (ComponentFiber G c) = 1)
  let s2 : Finset G.ConnectedComponent :=
    s.filter (fun c => Nat.card (ComponentFiber G c) = 2)
  let s3 : Finset G.ConnectedComponent :=
    s.filter (fun c => Nat.card (ComponentFiber G c) = 3)
  have hd12 : Disjoint s1 s2 := by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and, s1, s2]
    intro c h1 h2
    omega
  have hd13 : Disjoint s1 s3 := by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and, s1, s3]
    intro c h1 h3
    omega
  have hd23 : Disjoint s2 s3 := by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and, s2, s3]
    intro c h2 h3
    omega
  have hd123 : Disjoint (s1 ∪ s2) s3 := Finset.disjoint_union_left.mpr ⟨hd13, hd23⟩
  have hall : (s1 ∪ s2) ∪ s3 = s := by
    ext c
    simp only [Finset.mem_union, Finset.mem_filter, s1, s2, s3]
    constructor
    · rintro ((⟨hcs, _⟩ | ⟨hcs, _⟩) | ⟨hcs, _⟩) <;> exact hcs
    · intro hcs
      rcases hcard c with h1 | h2 | h3
      · exact Or.inl (Or.inl ⟨hcs, h1⟩)
      · exact Or.inl (Or.inr ⟨hcs, h2⟩)
      · exact Or.inr ⟨hcs, h3⟩
  have hp1 : (∏ c ∈ s1, f c) = a1 ^ s1.card :=
    Finset.prod_eq_pow_card fun c hc => by
      apply hf1 c
      exact (Finset.mem_filter.mp (show c ∈ s.filter
        (fun d => Nat.card (ComponentFiber G d) = 1) by simpa [s1] using hc)).2
  have hp2 : (∏ c ∈ s2, f c) = a2 ^ s2.card :=
    Finset.prod_eq_pow_card fun c hc => by
      apply hf2 c
      exact (Finset.mem_filter.mp (show c ∈ s.filter
        (fun d => Nat.card (ComponentFiber G d) = 2) by simpa [s2] using hc)).2
  have hp3 : (∏ c ∈ s3, f c) = a3 ^ s3.card :=
    Finset.prod_eq_pow_card fun c hc => by
      apply hf3 c
      exact (Finset.mem_filter.mp (show c ∈ s.filter
        (fun d => Nat.card (ComponentFiber G d) = 3) by simpa [s3] using hc)).2
  have hc1 : s1.card = componentCount G 1 := by
    exact filter_card_eq_componentCount G s hs 1
  have hc2 : s2.card = componentCount G 2 := by
    exact filter_card_eq_componentCount G s hs 2
  have hc3 : s3.card = componentCount G 3 := by
    exact filter_card_eq_componentCount G s hs 3
  calc
    (∏ c ∈ s, f c) =
        ∏ c ∈ (s1 ∪ s2) ∪ s3, f c := by
      apply Finset.prod_congr
      · exact hall.symm
      · intro c _
        rfl
    _ = (∏ c ∈ s1, f c) * (∏ c ∈ s2, f c) * (∏ c ∈ s3, f c) := by
      rw [Finset.prod_union hd123, Finset.prod_union hd12]
    _ = a1 ^ componentCount G 1 * a2 ^ componentCount G 2 *
        a3 ^ componentCount G 3 := by rw [hp1, hp2, hp3, hc1, hc2, hc3]

/-- If all components have one, two, or three vertices, the total vertex count is the weighted
sum of the three component counts. -/
theorem sum_component_card_eq_counts
    (G : SimpleGraph V)
    (s : Finset G.ConnectedComponent) (hs : ∀ c, c ∈ s)
    (hcard : ∀ c : G.ConnectedComponent,
      Nat.card (ComponentFiber G c) = 1 ∨
        Nat.card (ComponentFiber G c) = 2 ∨
        Nat.card (ComponentFiber G c) = 3) :
    (∑ c ∈ s, Nat.card (ComponentFiber G c)) =
      componentCount G 1 + 2 * componentCount G 2 + 3 * componentCount G 3 := by
  classical
  let s1 : Finset G.ConnectedComponent :=
    s.filter (fun c => Nat.card (ComponentFiber G c) = 1)
  let s2 : Finset G.ConnectedComponent :=
    s.filter (fun c => Nat.card (ComponentFiber G c) = 2)
  let s3 : Finset G.ConnectedComponent :=
    s.filter (fun c => Nat.card (ComponentFiber G c) = 3)
  have hd12 : Disjoint s1 s2 := by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and, s1, s2]
    intro c h1 h2
    omega
  have hd13 : Disjoint s1 s3 := by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and, s1, s3]
    intro c h1 h3
    omega
  have hd23 : Disjoint s2 s3 := by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and, s2, s3]
    intro c h2 h3
    omega
  have hd123 : Disjoint (s1 ∪ s2) s3 := Finset.disjoint_union_left.mpr ⟨hd13, hd23⟩
  have hall : (s1 ∪ s2) ∪ s3 = s := by
    ext c
    simp only [Finset.mem_union, Finset.mem_filter, s1, s2, s3]
    constructor
    · rintro ((⟨hcs, _⟩ | ⟨hcs, _⟩) | ⟨hcs, _⟩) <;> exact hcs
    · intro hcs
      rcases hcard c with h1 | h2 | h3
      · exact Or.inl (Or.inl ⟨hcs, h1⟩)
      · exact Or.inl (Or.inr ⟨hcs, h2⟩)
      · exact Or.inr ⟨hcs, h3⟩
  have hs1 : (∑ c ∈ s1, Nat.card (ComponentFiber G c)) = s1.card := by
    calc
      _ = ∑ _c ∈ s1, 1 := Finset.sum_congr rfl fun c hc =>
        (Finset.mem_filter.mp (show c ∈ s.filter
          (fun d => Nat.card (ComponentFiber G d) = 1) by simpa [s1] using hc)).2
      _ = s1.card := by simp
  have hs2 : (∑ c ∈ s2, Nat.card (ComponentFiber G c)) = 2 * s2.card := by
    calc
      _ = ∑ _c ∈ s2, 2 := Finset.sum_congr rfl fun c hc =>
        (Finset.mem_filter.mp (show c ∈ s.filter
          (fun d => Nat.card (ComponentFiber G d) = 2) by simpa [s2] using hc)).2
      _ = 2 * s2.card := by simp [Nat.mul_comm]
  have hs3 : (∑ c ∈ s3, Nat.card (ComponentFiber G c)) = 3 * s3.card := by
    calc
      _ = ∑ _c ∈ s3, 3 := Finset.sum_congr rfl fun c hc =>
        (Finset.mem_filter.mp (show c ∈ s.filter
          (fun d => Nat.card (ComponentFiber G d) = 3) by simpa [s3] using hc)).2
      _ = 3 * s3.card := by simp [Nat.mul_comm]
  have hc1 : s1.card = componentCount G 1 := by
    exact filter_card_eq_componentCount G s hs 1
  have hc2 : s2.card = componentCount G 2 := by
    exact filter_card_eq_componentCount G s hs 2
  have hc3 : s3.card = componentCount G 3 := by
    exact filter_card_eq_componentCount G s hs 3
  calc
    (∑ c ∈ s, Nat.card (ComponentFiber G c)) =
        ∑ c ∈ (s1 ∪ s2) ∪ s3, Nat.card (ComponentFiber G c) := by
      apply Finset.sum_congr
      · exact hall.symm
      · intro c _
        rfl
    _ = (∑ c ∈ s1, Nat.card (ComponentFiber G c)) +
        (∑ c ∈ s2, Nat.card (ComponentFiber G c)) +
        (∑ c ∈ s3, Nat.card (ComponentFiber G c)) := by
      rw [Finset.sum_union hd123, Finset.sum_union hd12]
    _ = componentCount G 1 + 2 * componentCount G 2 + 3 * componentCount G 3 := by
      rw [hs1, hs2, hs3, hc1, hc2, hc3]

/-- The canonical component equivalence turns the preceding sum identity into a formula for the
cardinality of the original vertex type. -/
theorem vertex_card_eq_component_counts
    (G : SimpleGraph V)
    (hcard : ∀ c : G.ConnectedComponent,
      Nat.card (ComponentFiber G c) = 1 ∨
        Nat.card (ComponentFiber G c) = 2 ∨
        Nat.card (ComponentFiber G c) = 3) :
    Fintype.card V =
      componentCount G 1 + 2 * componentCount G 2 + 3 * componentCount G 3 := by
  calc
    Fintype.card V = Nat.card V := Nat.card_eq_fintype_card.symm
    _ = Nat.card (Σ c : G.ConnectedComponent, ComponentFiber G c) :=
      Nat.card_congr (componentEquiv G)
    _ = ∑ c : G.ConnectedComponent, Nat.card (ComponentFiber G c) :=
      Nat.card_sigma
    _ = componentCount G 1 + 2 * componentCount G 2 + 3 * componentCount G 3 :=
      sum_component_card_eq_counts G Finset.univ (fun _ => Finset.mem_univ _) hcard

end

end Brockian.GraphComponentGrouping
