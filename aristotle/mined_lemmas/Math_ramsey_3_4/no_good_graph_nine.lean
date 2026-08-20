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

theorem no_good_graph_nine (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj]
    (htri : ∀ a b c : Fin 9, G.Adj a b → G.Adj a c → G.Adj b c → False)
    (hind : ∀ a b c d : Fin 9, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ¬ G.Adj a b → ¬ G.Adj a c → ¬ G.Adj a d → ¬ G.Adj b c → ¬ G.Adj b d → ¬ G.Adj c d →
      False) : False := by
  have hle : ∀ v : Fin 9, G.degree v ≤ 3 := by
    intro v
    by_contra hlt
    have h4 : 4 ≤ (G.neighborFinset v).card := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree] at hlt; omega
    obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ := exists_four_mem h4
    rw [SimpleGraph.mem_neighborFinset] at ha hb hc hd
    exact hind a b c d hab hac had hbc hbd hcd
      (fun h => htri v a b ha hb h) (fun h => htri v a c ha hc h) (fun h => htri v a d ha hd h)
      (fun h => htri v b c hb hc h) (fun h => htri v b d hb hd h) (fun h => htri v c d hc hd h)
  have hge : ∀ v : Fin 9, 3 ≤ G.degree v := by
    intro v
    by_contra hlt
    push_neg at hlt
    set S : Finset (Fin 9) := Finset.univ \ insert v (G.neighborFinset v) with hSdef
    have hcardins : (insert v (G.neighborFinset v)).card ≤ 3 := by
      have := Finset.card_insert_le v (G.neighborFinset v)
      rw [SimpleGraph.card_neighborFinset_eq_degree] at this
      omega
    have hcardS : 6 ≤ S.card := by
      have : S.card = 9 - (insert v (G.neighborFinset v)).card := by
        rw [hSdef, Finset.card_univ_diff]; simp
      omega
    have hmem : ∀ w ∈ S, w ≠ v ∧ ¬ G.Adj v w := by
      intro w hw
      rw [hSdef, Finset.mem_sdiff, Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hw
      push_neg at hw
      exact ⟨hw.2.1, hw.2.2⟩
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc, n1, n2, n3⟩ :=
      exists_indep_triple_of_six G htri S hcardS
    obtain ⟨hva, hna⟩ := hmem a ha
    obtain ⟨hvb, hnb⟩ := hmem b hb
    obtain ⟨hvc, hnc⟩ := hmem c hc
    exact hind v a b c (Ne.symm hva) (Ne.symm hvb) (Ne.symm hvc) hab hac hbc
      hna hnb hnc n1 n2 n3
  have hdeg : ∀ v : Fin 9, G.degree v = 3 := fun v => le_antisymm (hle v) (hge v)
  have hsum : ∑ v : Fin 9, G.degree v = 2 * G.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges G
  rw [Finset.sum_congr rfl (fun v _ => hdeg v)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

/-! ### The extremal graph on eight vertices (the Wagner graph) -/

/-- The circulant graph on `ZMod 8`-like vertex set `Fin 8` with connection set `{1, 4, 7}`
(an 8-cycle together with its four main diagonals). It is triangle-free and has
independence number 3. -/
