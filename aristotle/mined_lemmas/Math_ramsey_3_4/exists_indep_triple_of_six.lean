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

set_option maxRecDepth 10000
set_option synthInstance.maxSize 400
set_option synthInstance.maxHeartbeats 1000000

namespace Math

open Finset SimpleGraph

/-- `HasRamseyProp34 n` holds when every simple graph on `n` vertices contains either a
clique of size `3` or an independent set of size `4`; equivalently, every red/blue colouring
of the edges of `K n` contains a red triangle or a blue `K 4`. -/

theorem exists_indep_triple_of_six {V : Type} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (htri : ∀ a b c : V, G.Adj a b → G.Adj a c → G.Adj b c → False)
    (S : Finset V) (hS : 6 ≤ S.card) :
    ∃ a b c : V, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj b c := by
  obtain ⟨v, hv⟩ : ∃ v, v ∈ S := Finset.card_pos.mp (by omega)
  have hcard' : 5 ≤ (S.erase v).card := by
    rw [Finset.card_erase_of_mem hv]; omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := S.erase v)
    (p := fun w => G.Adj v w)
  have hcase : 3 ≤ ((S.erase v).filter (fun w => G.Adj v w)).card ∨
      3 ≤ ((S.erase v).filter (fun w => ¬ G.Adj v w)).card := by omega
  rcases hcase with hA | hB
  · obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := exists_three_mem hA
    simp only [Finset.mem_filter, Finset.mem_erase] at ha hb hc
    exact ⟨a, b, c, ha.1.2, hb.1.2, hc.1.2, hab, hac, hbc,
      fun h => htri v a b ha.2 hb.2 h, fun h => htri v a c ha.2 hc.2 h,
      fun h => htri v b c hb.2 hc.2 h⟩
  · obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := exists_three_mem hB
    simp only [Finset.mem_filter, Finset.mem_erase] at ha hb hc
    by_cases h1 : G.Adj a b
    · by_cases h2 : G.Adj a c
      · by_cases h3 : G.Adj b c
        · exact absurd h3 (fun h => htri a b c h1 h2 h)
        · exact ⟨v, b, c, hv, hb.1.2, hc.1.2, Ne.symm hb.1.1, Ne.symm hc.1.1, hbc,
            hb.2, hc.2, h3⟩
      · exact ⟨v, a, c, hv, ha.1.2, hc.1.2, Ne.symm ha.1.1, Ne.symm hc.1.1, hac,
          ha.2, hc.2, h2⟩
    · exact ⟨v, a, b, hv, ha.1.2, hb.1.2, Ne.symm ha.1.1, Ne.symm hb.1.1, hab,
        ha.2, hb.2, h1⟩

/-- There is no triangle-free graph on nine vertices whose independence number is at most
three: this is the upper bound `R(3,4) ≤ 9`. -/
