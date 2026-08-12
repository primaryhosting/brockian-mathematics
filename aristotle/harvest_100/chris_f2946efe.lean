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
def HasRamseyProp34 (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (∃ s : Finset (Fin n), s.card = 3 ∧ G.IsClique (↑s : Set (Fin n))) ∨
    (∃ t : Finset (Fin n), t.card = 4 ∧ G.IsIndepSet (↑t : Set (Fin n)))

/-! ### Building cliques and independent sets from explicit vertices -/

theorem clique_three_of_adj {V : Type} [DecidableEq V] (G : SimpleGraph V) (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : G.Adj a b) (h2 : G.Adj a c) (h3 : G.Adj b c) :
    ∃ s : Finset V, s.card = 3 ∧ G.IsClique (↑s : Set V) := by
  refine ⟨{a, b, c}, by rw [Finset.card_eq_three]; exact ⟨a, b, c, hab, hac, hbc, rfl⟩, ?_⟩
  simp only [Finset.coe_insert, Finset.coe_singleton]
  rw [SimpleGraph.isClique_iff]
  intro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hxy
      | assumption
      | exact h1.symm
      | exact h2.symm
      | exact h3.symm

theorem indep_four_of_not_adj {V : Type} [DecidableEq V] (G : SimpleGraph V) (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h1 : ¬ G.Adj a b) (h2 : ¬ G.Adj a c) (h3 : ¬ G.Adj a d)
    (h4 : ¬ G.Adj b c) (h5 : ¬ G.Adj b d) (h6 : ¬ G.Adj c d) :
    ∃ t : Finset V, t.card = 4 ∧ G.IsIndepSet (↑t : Set V) := by
  refine ⟨{a, b, c, d}, by
    rw [Finset.card_eq_four]; exact ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩, ?_⟩
  simp only [Finset.coe_insert, Finset.coe_singleton]
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hxy
      | assumption
      | exact fun h => h1 h.symm
      | exact fun h => h2 h.symm
      | exact fun h => h3 h.symm
      | exact fun h => h4 h.symm
      | exact fun h => h5 h.symm
      | exact fun h => h6 h.symm

/-- Extract three distinct elements from a finset of cardinality at least three. -/
theorem exists_three_mem {V : Type} [DecidableEq V] {s : Finset V} (hs : 3 ≤ s.card) :
    ∃ a b c : V, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq hs
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht
  exact ⟨a, b, c, hts (by simp), hts (by simp), hts (by simp), hab, hac, hbc⟩

/-- Extract four distinct elements from a finset of cardinality at least four. -/
theorem exists_four_mem {V : Type} [DecidableEq V] {s : Finset V} (hs : 4 ≤ s.card) :
    ∃ a b c d : V, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq hs
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.mp ht
  exact ⟨a, b, c, d, hts (by simp), hts (by simp), hts (by simp), hts (by simp),
    hab, hac, had, hbc, hbd, hcd⟩

/-! ### The key combinatorial lemmas -/

/-- `R(3,3) ≤ 6`, in the form: in a triangle-free graph, any set of at least six vertices
contains three pairwise non-adjacent vertices. -/
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
def G8 : SimpleGraph (Fin 8) where
  Adj a b := ((a.val + 8 - b.val) % 8) ∈ ({1, 4, 7} : Finset ℕ)
  symm := by
    have h : ∀ x y : Fin 8, ((x.val + 8 - y.val) % 8) ∈ ({1, 4, 7} : Finset ℕ) →
        ((y.val + 8 - x.val) % 8) ∈ ({1, 4, 7} : Finset ℕ) := by decide
    exact fun {x y} => h x y
  loopless := ⟨by decide⟩

instance G8Dec : DecidableRel G8.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

theorem G8_triangle_free : ∀ a b c : Fin 8, G8.Adj a b → G8.Adj a c → G8.Adj b c → False := by
  decide

theorem G8_no_indep_four : ∀ a b c d : Fin 8, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ¬ G8.Adj a b → ¬ G8.Adj a c → ¬ G8.Adj a d → ¬ G8.Adj b c → ¬ G8.Adj b d →
    ¬ G8.Adj c d → False := by
  decide

theorem not_hasRamseyProp34_eight : ¬ HasRamseyProp34 8 := by
  intro h
  rcases h G8 with ⟨s, hs, hcl⟩ | ⟨t, ht, hin⟩
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs
    exact G8_triangle_free a b c (hcl (by simp) (by simp) hab) (hcl (by simp) (by simp) hac)
      (hcl (by simp) (by simp) hbc)
  · obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.mp ht
    exact G8_no_indep_four a b c d hab hac had hbc hbd hcd
      (hin (by simp) (by simp) hab) (hin (by simp) (by simp) hac) (hin (by simp) (by simp) had)
      (hin (by simp) (by simp) hbc) (hin (by simp) (by simp) hbd) (hin (by simp) (by simp) hcd)

/-! ### Monotonicity -/

theorem hasRamseyProp34_mono {m n : ℕ} (hmn : m ≤ n) (hm : HasRamseyProp34 m) :
    HasRamseyProp34 n := by
  intro G
  have hinj : Function.Injective (Fin.castLE hmn) := Fin.castLE_injective hmn
  rcases hm (G.comap (Fin.castLE hmn)) with ⟨s, hs, hcl⟩ | ⟨t, ht, hin⟩
  · left
    refine ⟨s.image (Fin.castLE hmn), by rw [Finset.card_image_of_injective _ hinj]; exact hs, ?_⟩
    intro x hx y hy hxy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact hcl hx' hy' (fun h => hxy (by rw [h]))
  · right
    refine ⟨t.image (Fin.castLE hmn), by rw [Finset.card_image_of_injective _ hinj]; exact ht, ?_⟩
    intro x hx y hy hxy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact hin hx' hy' (fun h => hxy (by rw [h]))

/-! ### The main theorem -/

theorem hasRamseyProp34_nine : HasRamseyProp34 9 := by
  intro G
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  refine no_good_graph_nine G ?_ ?_
  · intro a b c hab hac hbc
    obtain ⟨s, hcard, hcl⟩ := clique_three_of_adj G a b c hab.ne hac.ne hbc.ne hab hac hbc
    exact h1 s hcard hcl
  · intro a b c d hab hac had hbc hbd hcd n1 n2 n3 n4 n5 n6
    obtain ⟨t, hcard, hin⟩ :=
      indep_four_of_not_adj G a b c d hab hac had hbc hbd hcd n1 n2 n3 n4 n5 n6
    exact h2 t hcard hin

/-- **The Ramsey number `R(3,4)` equals `9`**: nine is the least `n` such that every graph
on `n` vertices contains a triangle or an independent set of size four. -/
theorem ramsey_3_4 : IsLeast {n : ℕ | HasRamseyProp34 n} 9 := by
  refine ⟨hasRamseyProp34_nine, ?_⟩
  intro n hn
  by_contra hlt
  exact not_hasRamseyProp34_eight (hasRamseyProp34_mono (by omega) hn)

end Math

