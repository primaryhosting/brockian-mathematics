/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph

namespace Math

/-- The `(3,4)`-Ramsey property for `n`: every simple graph on `n` vertices contains
either a triangle (a `3`-clique) or an independent set of size `4`. -/
def RamseyProp34 (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (∃ s : Finset (Fin n), G.IsNClique 3 s) ∨ (∃ t : Finset (Fin n), G.IsNIndepSet 4 t)

section Helpers

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Three pairwise distinct, pairwise nonadjacent vertices form an independent set of size 3. -/
lemma isNIndepSet_three {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (nab : ¬ G.Adj a b) (nac : ¬ G.Adj a c) (nbc : ¬ G.Adj b c) :
    G.IsNIndepSet 3 ({a, b, c} : Finset V) := by
  constructor
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hxy
        | exact nab | exact nac | exact nbc
        | exact fun h => nab h.symm | exact fun h => nac h.symm | exact fun h => nbc h.symm
  · exact Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩

/-- `R(3,3) ≤ 6`, in the form: among any 6 vertices of a graph there is either a triangle or
an independent set of size 3. -/
lemma ramsey_33_on (G : SimpleGraph V) (s : Finset V) (hs : 6 ≤ s.card) :
    (∃ t ⊆ s, G.IsNClique 3 t) ∨ (∃ t ⊆ s, G.IsNIndepSet 3 t) := by
  classical
  obtain ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  have hs' : 5 ≤ (s.erase v).card := by
    rw [Finset.card_erase_of_mem hv]; omega
  have hAB : ((s.erase v).filter (fun w => G.Adj v w)).card +
      ((s.erase v).filter (fun w => ¬ G.Adj v w)).card = (s.erase v).card :=
    Finset.card_filter_add_card_filter_not _
  rcases (show 3 ≤ ((s.erase v).filter (fun w => G.Adj v w)).card ∨
      3 ≤ ((s.erase v).filter (fun w => ¬ G.Adj v w)).card by omega) with h | h
  · obtain ⟨t, hts, ht3⟩ := Finset.exists_subset_card_eq h
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp ht3
    have hx := Finset.mem_filter.mp (hts (by simp : x ∈ ({x, y, z} : Finset V)))
    have hy := Finset.mem_filter.mp (hts (by simp : y ∈ ({x, y, z} : Finset V)))
    have hz := Finset.mem_filter.mp (hts (by simp : z ∈ ({x, y, z} : Finset V)))
    have hxs : x ∈ s := Finset.mem_of_mem_erase hx.1
    have hys : y ∈ s := Finset.mem_of_mem_erase hy.1
    have hzs : z ∈ s := Finset.mem_of_mem_erase hz.1
    by_cases hxy' : G.Adj x y
    · exact Or.inl ⟨{v, x, y}, by simp [Finset.insert_subset_iff, hv, hxs, hys],
        SimpleGraph.is3Clique_triple_iff.mpr ⟨hx.2, hy.2, hxy'⟩⟩
    · by_cases hxz' : G.Adj x z
      · exact Or.inl ⟨{v, x, z}, by simp [Finset.insert_subset_iff, hv, hxs, hzs],
          SimpleGraph.is3Clique_triple_iff.mpr ⟨hx.2, hz.2, hxz'⟩⟩
      · by_cases hyz' : G.Adj y z
        · exact Or.inl ⟨{v, y, z}, by simp [Finset.insert_subset_iff, hv, hys, hzs],
            SimpleGraph.is3Clique_triple_iff.mpr ⟨hy.2, hz.2, hyz'⟩⟩
        · exact Or.inr ⟨{x, y, z}, by simp [Finset.insert_subset_iff, hxs, hys, hzs],
            isNIndepSet_three hxy hxz hyz hxy' hxz' hyz'⟩
  · obtain ⟨t, hts, ht3⟩ := Finset.exists_subset_card_eq h
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp ht3
    have hx := Finset.mem_filter.mp (hts (by simp : x ∈ ({x, y, z} : Finset V)))
    have hy := Finset.mem_filter.mp (hts (by simp : y ∈ ({x, y, z} : Finset V)))
    have hz := Finset.mem_filter.mp (hts (by simp : z ∈ ({x, y, z} : Finset V)))
    have hxs : x ∈ s := Finset.mem_of_mem_erase hx.1
    have hys : y ∈ s := Finset.mem_of_mem_erase hy.1
    have hzs : z ∈ s := Finset.mem_of_mem_erase hz.1
    have hvx : v ≠ x := fun e => (Finset.ne_of_mem_erase hx.1) e.symm
    have hvy : v ≠ y := fun e => (Finset.ne_of_mem_erase hy.1) e.symm
    have hvz : v ≠ z := fun e => (Finset.ne_of_mem_erase hz.1) e.symm
    by_cases hxy' : G.Adj x y
    · by_cases hxz' : G.Adj x z
      · by_cases hyz' : G.Adj y z
        · exact Or.inl ⟨{x, y, z}, by simp [Finset.insert_subset_iff, hxs, hys, hzs],
            SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy', hxz', hyz'⟩⟩
        · exact Or.inr ⟨{v, y, z}, by simp [Finset.insert_subset_iff, hv, hys, hzs],
            isNIndepSet_three hvy hvz hyz hy.2 hz.2 hyz'⟩
      · exact Or.inr ⟨{v, x, z}, by simp [Finset.insert_subset_iff, hv, hxs, hzs],
          isNIndepSet_three hvx hvz hxz hx.2 hz.2 hxz'⟩
    · exact Or.inr ⟨{v, x, y}, by simp [Finset.insert_subset_iff, hv, hxs, hys],
        isNIndepSet_three hvx hvy hxy hx.2 hy.2 hxy'⟩

end Helpers

/-- **Key intermediate lemma**: `R(3,4) ≤ 9`. Every graph on 9 vertices contains a triangle
or an independent set of size 4. -/
theorem ramsey_34_upper : RamseyProp34 9 := by
  intro G
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h4⟩ := hcon
  -- No vertex has four neighbours: they would form an independent set of size 4.
  have hdeg_le : ∀ v : Fin 9, G.degree v ≤ 3 := by
    intro v
    by_contra hd
    push_neg at hd
    have hcard : 4 ≤ (G.neighborFinset v).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; omega
    obtain ⟨t, hts, ht4⟩ := Finset.exists_subset_card_eq hcard
    refine h4 t ⟨?_, ht4⟩
    intro a ha b hb hab hadj
    have hva : G.Adj v a := SimpleGraph.mem_neighborFinset .. |>.mp (hts ha)
    have hvb : G.Adj v b := SimpleGraph.mem_neighborFinset .. |>.mp (hts hb)
    exact h3 {v, a, b} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hva, hvb, hadj⟩)
  -- Every vertex has at least three neighbours: otherwise its six non-neighbours would
  -- contain a triangle or an independent triple, the latter extending to an independent 4-set.
  have hdeg_ge : ∀ v : Fin 9, 3 ≤ G.degree v := by
    intro v
    by_contra hd
    push_neg at hd
    have hvnot : v ∉ G.neighborFinset v := by simp
    have hcard_ins : (insert v (G.neighborFinset v)).card = G.degree v + 1 := by
      rw [Finset.card_insert_of_notMem hvnot, SimpleGraph.card_neighborFinset_eq_degree]
    have hcard : 6 ≤ ((Finset.univ : Finset (Fin 9)) \ insert v (G.neighborFinset v)).card := by
      have hsub := Finset.card_univ_diff (insert v (G.neighborFinset v))
      rw [hsub, hcard_ins]
      simp only [Fintype.card_fin]
      omega
    have hmem : ∀ w ∈ (Finset.univ : Finset (Fin 9)) \ insert v (G.neighborFinset v),
        w ≠ v ∧ ¬ G.Adj v w := by
      intro w hw
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        SimpleGraph.mem_neighborFinset, not_or] at hw
      exact hw
    rcases ramsey_33_on G ((Finset.univ : Finset (Fin 9)) \ insert v (G.neighborFinset v))
      hcard with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
    · exact h3 t ht
    · have hvt : v ∉ t := fun hvt => ((hmem v (hts hvt)).1) rfl
      refine h4 (insert v t) ⟨?_, ?_⟩
      · intro a ha b hb hab
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
        rcases ha with rfl | ha
        · rcases hb with rfl | hb
          · exact absurd rfl hab
          · exact (hmem b (hts hb)).2
        · rcases hb with rfl | hb
          · exact fun hadj => (hmem a (hts ha)).2 hadj.symm
          · exact ht.1 ha hb hab
      · rw [Finset.card_insert_of_notMem hvt, ht.2]
  -- Hence the graph is 3-regular on 9 vertices, contradicting the handshake lemma.
  have hdeg : ∀ v : Fin 9, G.degree v = 3 := fun v => le_antisymm (hdeg_le v) (hdeg_ge v)
  have hsum : ∑ v : Fin 9, G.degree v = 2 * G.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges G
  rw [Finset.sum_congr rfl (fun v _ => hdeg v)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

/-- The circulant graph on `ℤ/8` with connection set `{±1, 4}` (the Wagner graph). It is
triangle-free and has independence number 3, witnessing `R(3,4) > 8`. -/
def G8 : SimpleGraph (Fin 8) where
  Adj i j := j.val = (i.val + 1) % 8 ∨ i.val = (j.val + 1) % 8 ∨ j.val = (i.val + 4) % 8
  symm := by intro i j; revert i j; decide
  loopless := ⟨by decide⟩

instance : DecidableRel G8.Adj := fun i j =>
  inferInstanceAs (Decidable (j.val = (i.val + 1) % 8 ∨ i.val = (j.val + 1) % 8 ∨
    j.val = (i.val + 4) % 8))

set_option maxRecDepth 100000 in
lemma G8_no_triangle : ∀ s : Finset (Fin 8), ¬ G8.IsNClique 3 s := by decide

set_option maxRecDepth 100000 in
lemma G8_no_indep4 : ∀ t : Finset (Fin 8), ¬ G8.IsNIndepSet 4 t := by decide

/-- Lower bound: `R(3,4) > 8`, hence any `n` with the Ramsey property satisfies `9 ≤ n`. -/
theorem ramsey_34_lower {n : ℕ} (h : RamseyProp34 n) : 9 ≤ n := by
  by_contra hn
  push_neg at hn
  have hn8 : n ≤ 8 := by omega
  set f : Fin n → Fin 8 := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hn8⟩ with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 : (f a).val = (f b).val := by rw [hab]
    exact Fin.ext h1
  rcases h (G8.comap f) with ⟨s, hs⟩ | ⟨t, ht⟩
  · refine G8_no_triangle (s.image f) ⟨?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact hs.1 ha hb (fun h => hxy (by rw [h]))
    · rw [Finset.card_image_of_injective _ hfinj, hs.2]
  · refine G8_no_indep4 (t.image f) ⟨?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ht.1 ha hb (fun h => hxy (by rw [h]))
    · rw [Finset.card_image_of_injective _ hfinj, ht.2]

/-- **R(3,4) = 9**: `9` is the least `n` such that every two-colouring of the edges of `K_n`
contains a triangle in the first colour or an independent set of size 4 (i.e. a `4`-clique in
the second colour). -/
theorem ramsey_3_4 : IsLeast {n : ℕ | RamseyProp34 n} 9 :=
  ⟨ramsey_34_upper, fun _ hn => ramsey_34_lower hn⟩

end Math

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

