/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open Finset SimpleGraph

/-! ## A decidable reformulation of `CliqueFree` -/

/-- `G.CliqueFree n` says: no finset of `n` pairwise-adjacent vertices. -/

theorem exists_independent_three (h3 : G.CliqueFree 3) (S : Finset V) (hS : 6 ≤ S.card) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj b c := by
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hSne
  set T := S.erase x with hT
  have hTcard : 5 ≤ T.card := by
    have h : T.card = S.card - 1 := by rw [hT]; exact Finset.card_erase_of_mem hx
    omega
  set A := T.filter (fun y => G.Adj x y) with hA
  set B := T.filter (fun y => ¬ G.Adj x y) with hB
  have hsplit : A.card + B.card = T.card := Finset.card_filter_add_card_filter_not _
  -- three vertices adjacent to `x` are pairwise non-adjacent
  by_cases hcase : 3 ≤ A.card
  · obtain ⟨A', hA'sub, hA'card⟩ := Finset.exists_subset_card_eq hcase
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hA'card
    have hmemA : ∀ y ∈ ({a, b, c} : Finset V), y ∈ S ∧ G.Adj x y := by
      intro y hy
      have hyA := hA'sub hy
      rw [hA, Finset.mem_filter] at hyA
      exact ⟨Finset.mem_of_mem_erase hyA.1, hyA.2⟩
    have key : ∀ p ∈ ({a, b, c} : Finset V), ∀ q ∈ ({a, b, c} : Finset V), p ≠ q →
        ¬ G.Adj p q := by
      intro p hp q hq hpq hadj
      obtain ⟨hpS, hxp⟩ := hmemA p hp
      obtain ⟨hqS, hxq⟩ := hmemA q hq
      exact card_ne_of_cliqueFree h3 {x, p, q} (by
        intro u hu w hw huw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
        rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
          first
            | exact absurd rfl huw
            | exact hxp | exact hxq | exact hadj
            | exact hxp.symm | exact hxq.symm | exact hadj.symm) (by
        rw [Finset.card_insert_of_notMem (by simp [hxp.ne, hxq.ne]),
          Finset.card_insert_of_notMem (by simp [hpq]), Finset.card_singleton])
    have ha : a ∈ ({a, b, c} : Finset V) := by simp
    have hb : b ∈ ({a, b, c} : Finset V) := by simp
    have hc : c ∈ ({a, b, c} : Finset V) := by simp
    exact ⟨a, (hmemA a ha).1, b, (hmemA b hb).1, c, (hmemA c hc).1, hab, hac, hbc,
      key a ha b hb hab, key a ha c hc hac, key b hb c hc hbc⟩
  · -- three vertices non-adjacent to `x`
    have hcase' : 3 ≤ B.card := by omega
    obtain ⟨B', hB'sub, hB'card⟩ := Finset.exists_subset_card_eq hcase'
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hB'card
    have hmemB : ∀ y ∈ ({a, b, c} : Finset V), y ∈ S ∧ ¬ G.Adj x y ∧ x ≠ y := by
      intro y hy
      have hyB := hB'sub hy
      rw [hB, Finset.mem_filter] at hyB
      exact ⟨Finset.mem_of_mem_erase hyB.1, hyB.2, fun h => (Finset.ne_of_mem_erase hyB.1) h.symm⟩
    have ha := hmemB a (by simp)
    have hb := hmemB b (by simp)
    have hc := hmemB c (by simp)
    by_cases hab' : G.Adj a b
    · by_cases hac' : G.Adj a c
      · by_cases hbc' : G.Adj b c
        · exact absurd (card_ne_of_cliqueFree h3 {a, b, c} (by
            intro u hu w hw huw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
            rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
              first
                | exact absurd rfl huw
                | exact hab' | exact hac' | exact hbc'
                | exact hab'.symm | exact hac'.symm | exact hbc'.symm) (by
            rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
              Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]))
            (by simp)
        · exact ⟨x, hx, b, hb.1, c, hc.1, hb.2.2, hc.2.2, hbc, hb.2.1, hc.2.1, hbc'⟩
      · exact ⟨x, hx, a, ha.1, c, hc.1, ha.2.2, hc.2.2, hac, ha.2.1, hc.2.1, hac'⟩
    · exact ⟨x, hx, a, ha.1, b, hb.1, ha.2.2, hb.2.2, hab, ha.2.1, hb.2.1, hab'⟩

/-- In a triangle-free graph on 9 vertices with no independent set of size 4, every vertex
has degree at least 3. -/
