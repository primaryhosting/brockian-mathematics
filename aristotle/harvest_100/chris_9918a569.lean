import Mathlib
/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
A self-contained development of Hall's marriage theorem.

* `Math.hall_exists_injective_iff` : the combinatorial ("system of distinct representatives")
  form, proved from scratch by induction (it does *not* use Mathlib's Hall theorem).
* `Math.halls_marriage` : a bipartite graph has a perfect matching iff Hall's condition holds.
-/

namespace Math

open Finset

section Core

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

omit [DecidableEq ι] in
private theorem biUnion_erase (t : ι → Finset α) (x : α) (u : Finset ι) :
    (u.biUnion fun i => (t i).erase x) = (u.biUnion t).erase x := by
  ext y
  simp only [Finset.mem_biUnion, Finset.mem_erase]
  constructor
  · rintro ⟨i, hi, hy1, hy2⟩; exact ⟨hy1, i, hi, hy2⟩
  · rintro ⟨hy1, i, hi, hy2⟩; exact ⟨i, hi, hy1, hy2⟩

omit [DecidableEq ι] in
private theorem biUnion_sdiff (t : ι → Finset α) (w : Finset α) (u : Finset ι) :
    (u.biUnion fun i => t i \ w) = (u.biUnion t) \ w := by
  ext y
  simp only [Finset.mem_biUnion, Finset.mem_sdiff]
  constructor
  · rintro ⟨i, hi, hy1, hy2⟩; exact ⟨⟨i, hi, hy1⟩, hy2⟩
  · rintro ⟨⟨i, hi, hy1⟩, hy2⟩; exact ⟨i, hi, hy1, hy2⟩

/-- Auxiliary induction: with an upper bound `n` on the cardinality of `s`, Hall's condition
on all subsets of `s` yields a system of distinct representatives for `s`. -/
theorem hall_aux [Nonempty α] :
    ∀ (n : ℕ) (t : ι → Finset α) (s : Finset ι), s.card ≤ n →
      (∀ u ⊆ s, u.card ≤ (u.biUnion t).card) →
      ∃ f : ι → α, Set.InjOn f ↑s ∧ ∀ i ∈ s, f i ∈ t i := by
  intro n
  induction n with
  | zero =>
      intro t s hs _
      have : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs)
      subst this
      exact ⟨fun _ => Classical.arbitrary α, by simp, by simp⟩
  | succ n ih =>
      intro t s hs hall
      rcases Nat.lt_or_ge s.card (n + 1) with hlt | hge
      · exact ih t s (Nat.lt_succ_iff.mp hlt) hall
      · have hcard : s.card = n + 1 := le_antisymm hs hge
        by_cases hA : ∀ u ⊆ s, u.Nonempty → u ≠ s → u.card < (u.biUnion t).card
        · -- Case A: every nonempty proper subset expands strictly.
          have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
          obtain ⟨i₀, hi₀⟩ := hsne
          have h1 : ({i₀} : Finset ι).card ≤ (({i₀} : Finset ι).biUnion t).card :=
            hall _ (by simpa using hi₀)
          rw [Finset.card_singleton, Finset.singleton_biUnion] at h1
          obtain ⟨x, hx⟩ : (t i₀).Nonempty := Finset.card_pos.mp (by omega)
          have hall' : ∀ u ⊆ s.erase i₀, u.card ≤ (u.biUnion fun i => (t i).erase x).card := by
            intro u hu
            rcases u.eq_empty_or_nonempty with rfl | hune
            · simp
            · have hus : u ⊆ s := hu.trans (Finset.erase_subset _ _)
              have hne' : u ≠ s := by
                rintro rfl
                exact (Finset.notMem_erase i₀ u) (hu hi₀)
              have hlt2 := hA u hus hune hne'
              have hpred := Finset.pred_card_le_card_erase (s := u.biUnion t) (a := x)
              rw [biUnion_erase]
              omega
          have hcard' : (s.erase i₀).card ≤ n := by
            have := Finset.card_erase_of_mem hi₀
            omega
          obtain ⟨f', hinj'', hmem''⟩ := ih (fun i => (t i).erase x) _ hcard' hall'
          have hmem' : ∀ i ∈ s.erase i₀, f' i ≠ x ∧ f' i ∈ t i := fun i hi =>
            Finset.mem_erase.mp (hmem'' i hi)
          have hinj' : Set.InjOn f' ↑(s.erase i₀) := hinj''
          refine ⟨Function.update f' i₀ x, ?_, ?_⟩
          · intro a ha b hb hab
            simp only [Finset.mem_coe] at ha hb
            by_cases hai : a = i₀ <;> by_cases hbi : b = i₀
            · rw [hai, hbi]
            · exfalso
              have hb' := hmem' b (Finset.mem_erase.mpr ⟨hbi, hb⟩)
              rw [hai, Function.update_self, Function.update_of_ne hbi] at hab
              exact hb'.1 hab.symm
            · exfalso
              have ha' := hmem' a (Finset.mem_erase.mpr ⟨hai, ha⟩)
              rw [hbi, Function.update_self, Function.update_of_ne hai] at hab
              exact ha'.1 hab
            · simp only [Function.update_of_ne hai, Function.update_of_ne hbi] at hab
              exact hinj' (by simp [ha, hai]) (by simp [hb, hbi]) hab
          · intro i hi
            by_cases hii : i = i₀
            · subst hii; simpa using hx
            · rw [Function.update_of_ne hii]
              exact (hmem' i (Finset.mem_erase.mpr ⟨hii, hi⟩)).2
        · -- Case B: some nonempty proper subset is tight.
          push_neg at hA
          obtain ⟨u, hus, hune, hnes, hle⟩ := hA
          have htight : u.card = (u.biUnion t).card := le_antisymm (hall u hus) hle
          have hucard : u.card ≤ n := by
            have h1 : u.card < s.card :=
              Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hus, hnes⟩)
            omega
          obtain ⟨f₁, hinj₁, hmem₁⟩ := ih t u hucard (fun v hv => hall v (hv.trans hus))
          have hall'' : ∀ v ⊆ s \ u,
              v.card ≤ (v.biUnion fun i => t i \ (u.biUnion t)).card := by
            intro v hv
            have hdisj : Disjoint v u :=
              Finset.disjoint_left.mpr fun a ha hau => (Finset.mem_sdiff.mp (hv ha)).2 hau
            have hkey : (v ∪ u).card ≤ ((v ∪ u).biUnion t).card :=
              hall _ (Finset.union_subset (hv.trans Finset.sdiff_subset) hus)
            have hun : (v ∪ u).biUnion t = (v.biUnion t) ∪ (u.biUnion t) := Finset.union_biUnion
            have hsplit : ((v.biUnion t) ∪ (u.biUnion t)).card
                = ((v.biUnion t) \ (u.biUnion t)).card + (u.biUnion t).card := by
              rw [← Finset.card_union_of_disjoint (Finset.sdiff_disjoint),
                Finset.sdiff_union_self_eq_union]
            rw [hun, hsplit, Finset.card_union_of_disjoint hdisj, ← htight] at hkey
            rw [biUnion_sdiff]
            omega
          have hs''card : (s \ u).card ≤ n := by
            have h1 : (s \ u).card = s.card - u.card := Finset.card_sdiff_of_subset hus
            have h2 : 0 < u.card := Finset.card_pos.mpr hune
            omega
          obtain ⟨f₂, hinj₂', hmem₂'⟩ := ih (fun i => t i \ (u.biUnion t)) _ hs''card hall''
          have hmem₂ : ∀ i ∈ s \ u, f₂ i ∈ t i ∧ f₂ i ∉ u.biUnion t := fun i hi =>
            Finset.mem_sdiff.mp (hmem₂' i hi)
          have hinj₂ : Set.InjOn f₂ ↑(s \ u) := hinj₂'
          refine ⟨fun i => if i ∈ u then f₁ i else f₂ i, ?_, ?_⟩
          · intro a ha b hb hab
            simp only [Finset.mem_coe] at ha hb
            by_cases hau : a ∈ u <;> by_cases hbu : b ∈ u
            · exact hinj₁ (by simpa using hau) (by simpa using hbu)
                (by simpa [hau, hbu] using hab)
            · exfalso
              have h2 := hmem₂ b (Finset.mem_sdiff.mpr ⟨hb, hbu⟩)
              have h1 : f₁ a ∈ u.biUnion t := Finset.mem_biUnion.mpr ⟨a, hau, hmem₁ a hau⟩
              simp only [hau, hbu, if_true, if_false] at hab
              exact h2.2 (hab ▸ h1)
            · exfalso
              have h2 := hmem₂ a (Finset.mem_sdiff.mpr ⟨ha, hau⟩)
              have h1 : f₁ b ∈ u.biUnion t := Finset.mem_biUnion.mpr ⟨b, hbu, hmem₁ b hbu⟩
              simp only [hau, hbu, if_true, if_false] at hab
              exact h2.2 (hab ▸ h1)
            · exact hinj₂ (by simpa using Finset.mem_sdiff.mpr ⟨ha, hau⟩)
                (by simpa using Finset.mem_sdiff.mpr ⟨hb, hbu⟩) (by simpa [hau, hbu] using hab)
          · intro i hi
            by_cases hiu : i ∈ u
            · simpa [hiu] using hmem₁ i hiu
            · simpa [hiu] using (hmem₂ i (Finset.mem_sdiff.mpr ⟨hi, hiu⟩)).1

/-- **Hall's marriage theorem**, combinatorial form: a finite family `t : ι → Finset α` of finite
sets has a system of distinct representatives iff every subfamily of `k` sets covers at least `k`
elements. -/
theorem hall_exists_injective_iff [Fintype ι] (t : ι → Finset α) :
    (∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ t i) ↔
      ∀ s : Finset ι, s.card ≤ (s.biUnion t).card := by
  constructor
  · rintro ⟨f, hf, hmem⟩ s
    calc s.card = (s.image f).card := (Finset.card_image_of_injective s hf).symm
      _ ≤ (s.biUnion t).card := by
          refine Finset.card_le_card fun y hy => ?_
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
          exact Finset.mem_biUnion.mpr ⟨i, hi, hmem i⟩
  · intro hall
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨fun i => (IsEmpty.false i).elim, fun a => (IsEmpty.false a).elim,
        fun i => (IsEmpty.false i).elim⟩
    · have hαne : Nonempty α := by
        obtain ⟨i⟩ := hι
        have h1 := hall {i}
        rw [Finset.card_singleton, Finset.singleton_biUnion] at h1
        obtain ⟨x, _⟩ := Finset.card_pos.mp (show 0 < (t i).card by omega)
        exact ⟨x⟩
      obtain ⟨f, hinj, hmem⟩ :=
        hall_aux (Fintype.card ι) t Finset.univ (by simp) (fun u _ => hall u)
      exact ⟨f, fun a b hab => hinj (by simp) (by simp) hab, fun i => hmem i (Finset.mem_univ i)⟩

end Core

section Graph

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B : Set V}

omit [DecidableEq V] in
/-- A graph admitting a perfect matching satisfies Hall's condition. -/
theorem hall_condition_of_isPerfectMatching {M : G.Subgraph} (hM : M.IsPerfectMatching)
    (s : Set V) : s.ncard ≤ (⋃ v ∈ s, G.neighborSet v).ncard := by
  classical
  have hM' := Subgraph.isPerfectMatching_iff.mp hM
  choose g hg huniq using hM'
  refine Set.ncard_le_ncard_of_injOn g (fun v hv => ?_) (fun a _ b _ hab => ?_) (Set.toFinite _)
  · exact Set.mem_biUnion hv (M.adj_sub (hg v))
  · have ha : M.Adj (g a) a := (hg a).symm
    have hb : M.Adj (g b) b := (hg b).symm
    rw [hab] at ha
    exact ((huniq (g b) a ha).trans (huniq (g b) b hb).symm)

omit [Fintype V] [DecidableEq V] in
/-- From an adjacency-respecting involution one builds a perfect matching. -/
theorem exists_isPerfectMatching_of_involutive (sigma : V → V) (hadj : ∀ v, G.Adj v (sigma v))
    (hinv : ∀ v, sigma (sigma v) = v) : ∃ M : G.Subgraph, M.IsPerfectMatching := by
  refine ⟨{ verts := Set.univ
            Adj := fun v w => G.Adj v w ∧ sigma v = w
            adj_sub := fun h => h.1
            edge_vert := fun _ => Set.mem_univ _
            symm := ?_ }, ?_⟩
  · rintro v w ⟨h1, rfl⟩
    exact ⟨h1.symm, hinv v⟩
  · refine Subgraph.isPerfectMatching_iff.mpr fun v => ⟨sigma v, ⟨hadj v, rfl⟩, ?_⟩
    rintro y ⟨-, rfl⟩
    rfl

/-- Under Hall's condition, a bipartite graph carries an adjacency-respecting involution
(the matching partner map). -/
theorem exists_involutive_of_hall [DecidableRel G.Adj] (hb : G.IsBipartiteWith A B)
    (hall : ∀ s : Set V, s.ncard ≤ (⋃ v ∈ s, G.neighborSet v).ncard) :
    ∃ sigma : V → V, (∀ v, G.Adj v (sigma v)) ∧ ∀ v, sigma (sigma v) = v := by
  classical
  have hfin : ∀ s : Finset V, s.card ≤ (s.biUnion fun v => G.neighborFinset v).card := by
    intro s
    have h := hall ↑s
    have hset : (⋃ v ∈ (↑s : Set V), G.neighborSet v)
        = ↑(s.biUnion fun v => G.neighborFinset v) := by
      ext y
      simp
    rwa [hset, Set.ncard_coe_finset, Set.ncard_coe_finset] at h
  obtain ⟨f, hinj, hmem⟩ :=
    (hall_exists_injective_iff (fun v => G.neighborFinset v)).mpr hfin
  have hadj : ∀ v, G.Adj v (f v) := fun v => (G.mem_neighborFinset v (f v)).mp (hmem v)
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hinj
  set e : V ≃ V := Equiv.ofBijective f hbij with he
  have hef : ∀ v, e v = f v := fun v => rfl
  have hmemAB : ∀ v, v ∈ A ∨ v ∈ B := by
    intro v
    rcases hb.mem_of_adj (hadj v) with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hfA : ∀ v ∈ A, f v ∈ B := fun v hv => hb.mem_of_mem_adj hv (hadj v)
  have hfB : ∀ v ∈ B, f v ∈ A := fun v hv => hb.symm.mem_of_mem_adj hv (hadj v)
  have hnotA : ∀ v ∈ B, v ∉ A := fun v hv hv' => (Set.disjoint_left.mp hb.disjoint hv') hv
  refine ⟨fun v => if v ∈ A then f v else e.symm v, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ A
    · simpa [hv] using hadj v
    · have hvB : v ∈ B := (hmemAB v).resolve_left hv
      have hfe : f (e.symm v) = v := by
        rw [← hef]; exact e.apply_symm_apply v
      have := hadj (e.symm v)
      rw [hfe] at this
      simpa [hv] using this.symm
  · intro v
    by_cases hv : v ∈ A
    · have h1 : f v ∉ A := hnotA _ (hfA v hv)
      simp only [hv, if_true, h1, if_false]
      rw [← hef v, e.symm_apply_apply]
    · have hvB : v ∈ B := (hmemAB v).resolve_left hv
      have hfe : f (e.symm v) = v := by
        rw [← hef]; exact e.apply_symm_apply v
      have hsA : e.symm v ∈ A := by
        rcases hmemAB (e.symm v) with h | h
        · exact h
        · exact absurd (hfe ▸ hfB _ h) hv
      simp only [hv, if_false, hsA, if_true, hfe]

/-- **Hall's marriage theorem** for bipartite graphs: a bipartite graph (on a finite vertex type,
with parts `A` and `B`) has a perfect matching if and only if Hall's condition holds, i.e. every
set of vertices has at least as many neighbours as it has elements. -/
theorem halls_marriage [DecidableRel G.Adj] (hb : G.IsBipartiteWith A B) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      ∀ s : Set V, s.ncard ≤ (⋃ v ∈ s, G.neighborSet v).ncard := by
  constructor
  · rintro ⟨M, hM⟩
    exact hall_condition_of_isPerfectMatching hM
  · intro hall
    obtain ⟨sigma, hadj, hinv⟩ := exists_involutive_of_hall hb hall
    exact exists_isPerfectMatching_of_involutive sigma hadj hinv

/-- A sanity check that the hypotheses of `Math.halls_marriage` are satisfiable and that the
theorem really produces matchings: the single-edge graph on `Bool` is bipartite with parts
`{false}`, `{true}`, satisfies Hall's condition, and hence has a perfect matching. -/
example : ∃ M : (⊤ : SimpleGraph Bool).Subgraph, M.IsPerfectMatching := by
  have hb : (⊤ : SimpleGraph Bool).IsBipartiteWith {false} {true} := by
    constructor
    · simp
    · rintro v w h; cases v <;> cases w <;> simp_all
  refine (halls_marriage hb).mpr fun s => ?_
  have h : (⋃ v ∈ s, (⊤ : SimpleGraph Bool).neighborSet v) = (fun b => !b) '' s := by
    ext y
    simp only [Set.mem_iUnion, SimpleGraph.mem_neighborSet, top_adj, Set.mem_image, exists_prop]
    constructor
    · rintro ⟨v, hv, hne⟩; exact ⟨v, hv, by cases v <;> cases y <;> simp_all⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, by cases v <;> simp⟩
  rw [h, Set.ncard_image_of_injective _ (fun a b => by cases a <;> cases b <;> simp)]

end Graph

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

