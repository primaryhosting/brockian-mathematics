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

namespace Math

/-- `RamseyProp s t n` says that for every graph `G` on `n` vertices (equivalently, every
two-colouring of the edges of the complete graph on `n` vertices) either `G` contains a clique
of size `s`, or the complement of `G` contains a clique of size `t` (i.e. `G` contains an
independent set of size `t`). -/

theorem exists_indep_three {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (htri : ∀ a b c : V, G.Adj a b → G.Adj a c → G.Adj b c → False)
    (s : Finset V) (hs : 6 ≤ s.card) :
    ∃ t ⊆ s, t.card = 3 ∧ ∀ a ∈ t, ∀ b ∈ t, a ≠ b → ¬ G.Adj a b := by
  obtain ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  have hs' : 5 ≤ (s.erase v).card := by
    rw [Finset.card_erase_of_mem hv]; omega
  have hcount := Finset.card_filter_add_card_filter_not (s := s.erase v) (fun x => G.Adj v x)
  by_cases hA : 3 ≤ ((s.erase v).filter (fun x => G.Adj v x)).card
  · obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hA
    refine ⟨t, ?_, htc, ?_⟩
    · intro x hx
      exact Finset.mem_of_mem_erase (Finset.mem_filter.mp (hts hx)).1
    · intro a ha b hb _ hadj
      exact htri v a b (Finset.mem_filter.mp (hts ha)).2 (Finset.mem_filter.mp (hts hb)).2 hadj
  · have hB : 3 ≤ ((s.erase v).filter (fun x => ¬ G.Adj v x)).card := by omega
    obtain ⟨u, hus, huc⟩ := Finset.exists_subset_card_eq hB
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp huc
    have key : ∀ x y : V, x ≠ y → x ∈ ({a, b, c} : Finset V) → y ∈ ({a, b, c} : Finset V) →
        ¬ G.Adj x y → ∃ t ⊆ s, t.card = 3 ∧ ∀ p ∈ t, ∀ q ∈ t, p ≠ q → ¬ G.Adj p q := by
      intro x y hxy hx hy hnadj
      have hx' := Finset.mem_filter.mp (hus hx)
      have hy' := Finset.mem_filter.mp (hus hy)
      have hxv : x ≠ v := (Finset.mem_erase.mp hx'.1).1
      have hyv : y ≠ v := (Finset.mem_erase.mp hy'.1).1
      refine ⟨{v, x, y}, ?_, ?_, ?_⟩
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hv
        · exact (Finset.mem_erase.mp hx'.1).2
        · exact (Finset.mem_erase.mp hy'.1).2
      · rw [Finset.card_insert_of_notMem (by simp [Ne.symm hxv, Ne.symm hyv]),
          Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
      · intro p hp q hq hpq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
        rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
          simp_all <;>
          first
            | exact hx'.2
            | exact hy'.2
            | exact fun h => hx'.2 h.symm
            | exact fun h => hy'.2 h.symm
            | exact hnadj
            | exact fun h => hnadj h.symm
    by_cases h1 : G.Adj a b
    · by_cases h2 : G.Adj a c
      · exact key b c hbc (by simp) (by simp) (fun h => htri a b c h1 h2 h)
      · exact key a c hac (by simp) (by simp) h2
    · exact key a b hab (by simp) (by simp) h1

/-- Upper bound: `R(3,4) ≤ 9`. -/
