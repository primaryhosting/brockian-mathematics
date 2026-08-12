import Mathlib

/-!
# Upper bound for the Ramsey number R(4,4)

This file develops, from scratch, the classical inductive bounds on two-colour Ramsey
numbers, culminating in `Math.ramsey_upper_4_4`: every graph on a vertex set of size at
least `18` contains a `4`-clique or an independent set of size `4`.
-/

namespace Math

open Finset

variable {V : Type*} [DecidableEq V]

open scoped Classical in
/-- The neighbours of `v` inside `s` (excluding `v` itself). -/
noncomputable def redN (G : SimpleGraph V) (s : Finset V) (v : V) : Finset V :=
  {w ∈ s.erase v | G.Adj v w}

open scoped Classical in
/-- The non-neighbours of `v` inside `s` (excluding `v` itself). -/
noncomputable def blueN (G : SimpleGraph V) (s : Finset V) (v : V) : Finset V :=
  {w ∈ s.erase v | ¬ G.Adj v w}

variable {G : SimpleGraph V} {s : Finset V} {v w : V}

lemma mem_redN : w ∈ redN G s v ↔ (w ∈ s ∧ w ≠ v) ∧ G.Adj v w := by
  classical
  simp [redN, Finset.mem_filter, Finset.mem_erase, and_comm]

lemma mem_blueN : w ∈ blueN G s v ↔ (w ∈ s ∧ w ≠ v) ∧ ¬ G.Adj v w := by
  classical
  simp [blueN, Finset.mem_filter, Finset.mem_erase, and_comm]

lemma redN_subset : redN G s v ⊆ s := fun _ hw => (mem_redN.1 hw).1.1

lemma blueN_subset : blueN G s v ⊆ s := fun _ hw => (mem_blueN.1 hw).1.1

lemma card_redN_add_card_blueN (hv : v ∈ s) :
    (redN G s v).card + (blueN G s v).card + 1 = s.card := by
  classical
  have h : (redN G s v).card + (blueN G s v).card = (s.erase v).card := by
    simpa [redN, blueN] using
      Finset.card_filter_add_card_filter_not (s := s.erase v) (p := fun w => G.Adj v w)
  rw [h, Finset.card_erase_add_one hv]

/-- Extending a clique in the neighbourhood of `v` by `v`. -/
lemma insert_isNClique_of_redN {t : Finset V} {k : ℕ} (hv : v ∈ s) (ht : t ⊆ redN G s v)
    (hcl : G.IsNClique k t) : insert v t ⊆ s ∧ G.IsNClique (k + 1) (insert v t) := by
  refine ⟨?_, hcl.insert (fun b hb => ?_)⟩
  · intro x hx
    rcases Finset.mem_insert.1 hx with h | h
    · exact h ▸ hv
    · exact redN_subset (ht h)
  · exact (mem_redN.1 (ht hb)).2

/-- Extending a co-clique in the non-neighbourhood of `v` by `v`. -/
lemma insert_isNClique_of_blueN {t : Finset V} {k : ℕ} (hv : v ∈ s) (ht : t ⊆ blueN G s v)
    (hcl : Gᶜ.IsNClique k t) : insert v t ⊆ s ∧ Gᶜ.IsNClique (k + 1) (insert v t) := by
  refine ⟨?_, hcl.insert (fun b hb => ?_)⟩
  · intro x hx
    rcases Finset.mem_insert.1 hx with h | h
    · exact h ▸ hv
    · exact blueN_subset (ht h)
  · have := mem_blueN.1 (ht hb)
    exact (SimpleGraph.compl_adj _ _ _).2 ⟨fun h => this.1.2 h.symm, this.2⟩

/-- The Ramsey property, relative to a fixed graph `G` and localised to subsets. -/
def RamR (G : SimpleGraph V) (k l N : ℕ) : Prop :=
  ∀ s : Finset V, N ≤ s.card →
    (∃ t ⊆ s, G.IsNClique k t) ∨ (∃ t ⊆ s, Gᶜ.IsNClique l t)

omit [DecidableEq V] in
lemma RamR.mono {k l N M : ℕ} (h : RamR G k l N) (hNM : N ≤ M) : RamR G k l M :=
  fun s hs => h s (le_trans hNM hs)

omit [DecidableEq V] in
/-- Symmetry of the Ramsey property under swapping the two colours. -/
lemma RamR.compl {k l N : ℕ} (h : RamR Gᶜ k l N) : RamR G l k N := by
  intro s hs
  rcases h s hs with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
  · exact Or.inr ⟨t, hts, ht⟩
  · rw [compl_compl] at ht
    exact Or.inl ⟨t, hts, ht⟩

/-- `R(2, l) ≤ l`. -/
lemma ramR_two_left (l : ℕ) : RamR G 2 l l := by
  intro s hs
  by_cases h : ∃ a ∈ s, ∃ b ∈ s, G.Adj a b
  · obtain ⟨a, ha, b, hb, hab⟩ := h
    refine Or.inl ⟨{a, b}, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with h | h
      · exact h ▸ ha
      · exact (Finset.mem_singleton.1 h) ▸ hb
    · refine ⟨?_, Finset.card_pair hab.ne⟩
      simp only [Finset.coe_insert, Finset.coe_singleton,
        Set.pairwise_insert_of_symmetric G.symm, Set.pairwise_singleton, Set.mem_singleton_iff]
      exact ⟨trivial, fun b hb _ => hb ▸ hab⟩
  · push_neg at h
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hs
    refine Or.inr ⟨t, hts, ⟨?_, htc⟩⟩
    intro a ha b hb hab
    exact (SimpleGraph.compl_adj _ _ _).2 ⟨hab, h a (hts ha) b (hts hb)⟩

/-- `R(k, 2) ≤ k`. -/
lemma ramR_two_right (k : ℕ) : RamR G k 2 k :=
  RamR.compl (ramR_two_left k)

/-- The basic inductive step `R(k+1, l+1) ≤ R(k, l+1) + R(k+1, l)`. -/
lemma ramR_step {k l a b : ℕ} (ha : 0 < a) (h1 : RamR G k (l + 1) a) (h2 : RamR G (k + 1) l b) :
    RamR G (k + 1) (l + 1) (a + b) := by
  intro s hs
  have hsne : s.Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨v, hv⟩ := hsne
  have hcard := card_redN_add_card_blueN (G := G) hv
  by_cases hR : a ≤ (redN G s v).card
  · rcases h1 _ hR with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
    · obtain ⟨h1', h2'⟩ := insert_isNClique_of_redN hv hts ht
      exact Or.inl ⟨insert v t, h1', h2'⟩
    · exact Or.inr ⟨t, hts.trans redN_subset, ht⟩
  · have hB : b ≤ (blueN G s v).card := by omega
    rcases h2 _ hB with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
    · exact Or.inl ⟨t, hts.trans blueN_subset, ht⟩
    · obtain ⟨h1', h2'⟩ := insert_isNClique_of_blueN hv hts ht
      exact Or.inr ⟨insert v t, h1', h2'⟩

lemma redN_insert_self (G : SimpleGraph V) {a : V} {s : Finset V} (ha : a ∉ s) :
    ∀ w, w ∈ redN G (insert a s) a ↔ w ∈ s ∧ G.Adj a w := by
  intro w
  rw [mem_redN]
  constructor
  · rintro ⟨⟨hw, hwa⟩, hadj⟩
    exact ⟨(Finset.mem_insert.1 hw).resolve_left hwa, hadj⟩
  · rintro ⟨hw, hadj⟩
    exact ⟨⟨Finset.mem_insert_of_mem hw, fun h => ha (h ▸ hw)⟩, hadj⟩

lemma redN_insert_of_adj (G : SimpleGraph V) {a v : V} {s : Finset V} (ha : a ∉ s) (hv : v ∈ s)
    (hadj : G.Adj v a) : redN G (insert a s) v = insert a (redN G s v) := by
  have hva : v ≠ a := fun h => ha (h ▸ hv)
  ext w
  simp only [Finset.mem_insert, mem_redN]
  constructor
  · rintro ⟨⟨hw | hw, hwv⟩, hadj'⟩
    · exact Or.inl hw
    · exact Or.inr ⟨⟨hw, hwv⟩, hadj'⟩
  · rintro (rfl | ⟨⟨hw, hwv⟩, hadj'⟩)
    · exact ⟨⟨Or.inl rfl, fun h => hva h.symm⟩, hadj⟩
    · exact ⟨⟨Or.inr hw, hwv⟩, hadj'⟩

lemma redN_insert_of_not_adj (G : SimpleGraph V) {a v : V} {s : Finset V}
    (hadj : ¬ G.Adj v a) : redN G (insert a s) v = redN G s v := by
  ext w
  simp only [mem_redN, Finset.mem_insert]
  constructor
  · rintro ⟨⟨hw | hw, hwv⟩, hadj'⟩
    · exact absurd (hw ▸ hadj') hadj
    · exact ⟨⟨hw, hwv⟩, hadj'⟩
  · rintro ⟨⟨hw, hwv⟩, hadj'⟩
    exact ⟨⟨Or.inr hw, hwv⟩, hadj'⟩

/-- Handshake lemma, in the localised form we need. -/
lemma even_sum_card_redN (G : SimpleGraph V) (s : Finset V) :
    Even (∑ v ∈ s, (redN G s v).card) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    set X := redN G (insert a s) a with hX
    have hXmem : ∀ w, w ∈ X ↔ w ∈ s ∧ G.Adj a w := redN_insert_self G ha
    have hXsub : X ⊆ s := fun w hw => ((hXmem w).1 hw).1
    have hstep : ∀ v ∈ s, (redN G (insert a s) v).card
        = (redN G s v).card + (if G.Adj v a then 1 else 0) := by
      intro v hv
      by_cases hadj : G.Adj v a
      · have hnot : a ∉ redN G s v := fun h => ha (mem_redN.1 h).1.1
        rw [redN_insert_of_adj G ha hv hadj, Finset.card_insert_of_notMem hnot, if_pos hadj]
      · rw [redN_insert_of_not_adj G hadj, if_neg hadj, Nat.add_zero]
    have hsum : ∑ v ∈ s, (if G.Adj v a then 1 else 0) = X.card := by
      have h1 : ∑ v ∈ X, (if G.Adj v a then 1 else 0)
          = ∑ v ∈ s, (if G.Adj v a then 1 else 0) := by
        refine Finset.sum_subset hXsub ?_
        intro x hx hxX
        have hnadj : ¬ G.Adj x a := fun h => hxX ((hXmem x).2 ⟨hx, h.symm⟩)
        simp [hnadj]
      rw [← h1, Finset.sum_congr rfl (fun x hx => if_pos ((hXmem x).1 hx).2.symm),
        Finset.sum_const, smul_eq_mul, mul_one]
    rw [Finset.sum_insert ha, Finset.sum_congr rfl hstep, Finset.sum_add_distrib, hsum, ← hX]
    obtain ⟨m, hm⟩ := ih
    exact ⟨X.card + m, by omega⟩

/-- The parity-improved inductive step. -/
lemma ramR_step_parity {k l a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hae : Even a) (hbe : Even b)
    (h1 : RamR G k (l + 1) a) (h2 : RamR G (k + 1) l b) :
    RamR G (k + 1) (l + 1) (a + b - 1) := by
  intro s hs
  by_cases hex : ∃ v ∈ s, a ≤ (redN G s v).card ∨ b ≤ (blueN G s v).card
  · obtain ⟨v, hv, hcase⟩ := hex
    rcases hcase with hR | hB
    · rcases h1 _ hR with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
      · obtain ⟨h1', h2'⟩ := insert_isNClique_of_redN hv hts ht
        exact Or.inl ⟨insert v t, h1', h2'⟩
      · exact Or.inr ⟨t, hts.trans redN_subset, ht⟩
    · rcases h2 _ hB with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
      · exact Or.inl ⟨t, hts.trans blueN_subset, ht⟩
      · obtain ⟨h1', h2'⟩ := insert_isNClique_of_blueN hv hts ht
        exact Or.inr ⟨insert v t, h1', h2'⟩
  · exfalso
    push_neg at hex
    have hne : s.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨v0, hv0⟩ := hne
    have hcard : s.card = a + b - 1 := by
      have h := card_redN_add_card_blueN (G := G) hv0
      have := hex v0 hv0
      omega
    have hall : ∀ v ∈ s, (redN G s v).card = a - 1 := by
      intro v hv
      have h := card_redN_add_card_blueN (G := G) hv
      have := hex v hv
      omega
    have hsum : ∑ v ∈ s, (redN G s v).card = s.card * (a - 1) := by
      rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_eq_mul]
    have heven := even_sum_card_redN G s
    rw [hsum, hcard] at heven
    have hodd1 : Odd (a + b - 1) := by
      rw [Nat.odd_iff]
      rw [Nat.even_iff] at hae hbe
      omega
    have hodd2 : Odd (a - 1) := by
      rw [Nat.odd_iff]
      rw [Nat.even_iff] at hae
      omega
    rw [Nat.even_iff] at heven
    rw [Nat.odd_iff] at hodd1 hodd2
    have hm := Nat.mul_mod (a + b - 1) (a - 1) 2
    rw [hodd1, hodd2] at hm
    omega

lemma ramR_3_3 : RamR G 3 3 6 :=
  ramR_step (by norm_num) (ramR_two_left 3) (ramR_two_right 3)

lemma ramR_2_4 : RamR G 2 4 4 := ramR_two_left 4

lemma ramR_3_4 : RamR G 3 4 9 := by
  have := ramR_step_parity (G := G) (k := 2) (l := 3) (a := 4) (b := 6)
    (by norm_num) (by norm_num) (by decide) (by decide) ramR_2_4 ramR_3_3
  simpa using this

lemma ramR_4_3 : RamR G 4 3 9 := RamR.compl ramR_3_4

lemma ramR_4_4 : RamR G 4 4 18 := by
  have := ramR_step (G := G) (k := 3) (l := 3) (a := 9) (b := 9)
    (by norm_num) ramR_3_4 ramR_4_3
  simpa using this

/-- **Upper bound**: any graph on at least 18 vertices contains a monochromatic `K₄`. -/
theorem ramsey_upper_4_4 {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    (hW : 18 ≤ Fintype.card W) :
    (∃ t : Finset W, G.IsNClique 4 t) ∨ (∃ t : Finset W, Gᶜ.IsNClique 4 t) := by
  have := ramR_4_4 (G := G) Finset.univ (by simpa using hW)
  rcases this with ⟨t, _, ht⟩ | ⟨t, _, ht⟩
  · exact Or.inl ⟨t, ht⟩
  · exact Or.inr ⟨t, ht⟩

end Math

import Mathlib

/-!
# Lower bound for the Ramsey number R(4,4)

The Paley graph on 17 vertices (`Math.paley17`) has no clique of size 4 and no
independent set of size 4, which shows `R(4,4) > 17`.
-/

namespace Math

/-- The nonzero quadratic residues modulo 17. -/
def qr17 : List ℕ := [1, 2, 4, 8, 9, 13, 15, 16]

/-- Adjacency in the Paley graph of order 17: `i ~ j` iff `i - j` is a quadratic
residue mod 17. -/
def padj (i j : Fin 17) : Bool := qr17.contains ((i.val + 17 - j.val) % 17)

set_option maxRecDepth 10000 in
theorem padj_symm : ∀ i j : Fin 17, padj i j = padj j i := by decide

set_option maxRecDepth 10000 in
theorem padj_irrefl : ∀ i : Fin 17, padj i i = false := by decide

/-- The Paley graph of order 17. -/
def paley17 : SimpleGraph (Fin 17) where
  Adj i j := padj i j = true
  symm := by
    intro i j h
    rw [padj_symm]
    exact h
  loopless := ⟨by
    intro i h
    rw [padj_irrefl i] at h
    exact Bool.noConfusion h⟩

instance : DecidableRel paley17.Adj := fun i j =>
  inferInstanceAs (Decidable (padj i j = true))

/-- Adjacency in the complement of the Paley graph, as a boolean function. -/
def cadj (i j : Fin 17) : Bool := (i != j) && !padj i j

/-- Any `4`-clique yields four vertices which are pairwise adjacent. -/
lemma exists_adj_of_isNClique_four {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {t : Finset V} (h : G.IsNClique 4 t) :
    ∃ a b c d : V, G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d := by
  obtain ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, rfl⟩ := Finset.card_eq_four.1 h.2
  exact ⟨x, y, z, w,
    h.1 (by simp) (by simp) hxy, h.1 (by simp) (by simp) hxz, h.1 (by simp) (by simp) hxw,
    h.1 (by simp) (by simp) hyz, h.1 (by simp) (by simp) hyw, h.1 (by simp) (by simp) hzw⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem no_padj_clique : ∀ a b c d : Fin 17,
    ¬ (padj a b ∧ padj a c ∧ padj a d ∧ padj b c ∧ padj b d ∧ padj c d) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem no_cadj_clique : ∀ a b c d : Fin 17,
    ¬ (cadj a b ∧ cadj a c ∧ cadj a d ∧ cadj b c ∧ cadj b d ∧ cadj c d) := by decide

/-- The Paley graph of order 17 has no `4`-clique. -/
theorem paley17_cliqueFree : ∀ t : Finset (Fin 17), ¬ paley17.IsNClique 4 t := by
  intro t ht
  obtain ⟨a, b, c, d, h1, h2, h3, h4, h5, h6⟩ := exists_adj_of_isNClique_four ht
  exact no_padj_clique a b c d ⟨h1, h2, h3, h4, h5, h6⟩

/-- The complement of the Paley graph of order 17 has no `4`-clique. -/
theorem paley17_compl_cliqueFree : ∀ t : Finset (Fin 17), ¬ paley17ᶜ.IsNClique 4 t := by
  intro t ht
  obtain ⟨a, b, c, d, h1, h2, h3, h4, h5, h6⟩ := exists_adj_of_isNClique_four ht
  have key : ∀ i j : Fin 17, paley17ᶜ.Adj i j → cadj i j = true := by
    intro i j h
    rw [SimpleGraph.compl_adj] at h
    simp only [cadj, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
    exact ⟨h.1, by simpa [paley17] using h.2⟩
  exact no_cadj_clique a b c d
    ⟨key _ _ h1, key _ _ h2, key _ _ h3, key _ _ h4, key _ _ h5, key _ _ h6⟩

end Math

import Mathlib
import RequestProject.RamseyUpper
import RequestProject.RamseyLower

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# The Ramsey number `R(4,4) = 18`
-/

namespace Math

/-- `IsRamsey k l N` says that every graph on `N` vertices contains either a clique of
size `k` or an independent set of size `l`. -/
def IsRamsey (k l N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    (∃ s : Finset (Fin N), G.IsNClique k s) ∨ (∃ s : Finset (Fin N), Gᶜ.IsNClique l s)

/-- The (diagonal) two-colour Ramsey number `R(k, l)`. -/
noncomputable def ramseyNumber (k l : ℕ) : ℕ := sInf {N | IsRamsey k l N}

section Transfer

variable {V W : Type*}

lemma comap_compl (f : V ↪ W) (G : SimpleGraph W) :
    (SimpleGraph.comap f G)ᶜ = SimpleGraph.comap f Gᶜ := by
  ext x y
  simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj, ne_eq, f.apply_eq_iff_eq]

lemma isNClique_map_comap {k : ℕ} (f : V ↪ W) (G : SimpleGraph W) {t : Finset V}
    (h : (SimpleGraph.comap f G).IsNClique k t) : G.IsNClique k (t.map f) := by
  refine ⟨?_, by rw [Finset.card_map]; exact h.2⟩
  intro a ha b hb hab
  simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at ha hb
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  exact h.1 hx hy (fun h' => hab (by rw [h']))

end Transfer

lemma IsRamsey.mono {k l N M : ℕ} (h : IsRamsey k l N) (hNM : N ≤ M) : IsRamsey k l M := by
  intro G
  set f : Fin N ↪ Fin M := (Fin.castLEEmb hNM) with hf
  rcases h (SimpleGraph.comap f G) with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact Or.inl ⟨t.map f, isNClique_map_comap f G ht⟩
  · rw [comap_compl f G] at ht
    exact Or.inr ⟨t.map f, isNClique_map_comap f Gᶜ ht⟩

/-- Every two-colouring of the edges of `K₁₈` contains a monochromatic `K₄`. -/
theorem isRamsey_4_4_18 : IsRamsey 4 4 18 := by
  intro G
  classical
  exact ramsey_upper_4_4 G (by simp)

/-- The Paley graph on 17 vertices witnesses that `K₁₇` admits a two-colouring with no
monochromatic `K₄`. -/
theorem not_isRamsey_4_4_17 : ¬ IsRamsey 4 4 17 := by
  intro h
  rcases h paley17 with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact paley17_cliqueFree s hs
  · exact paley17_compl_cliqueFree s hs

/-- **The Ramsey number `R(4,4)` equals `18`.** -/
theorem ramsey_4_4 : ramseyNumber 4 4 = 18 := by
  refine le_antisymm (Nat.sInf_le isRamsey_4_4_18) ?_
  by_contra hlt
  push_neg at hlt
  have hmem : ramseyNumber 4 4 ∈ {N | IsRamsey 4 4 N} :=
    Nat.sInf_mem ⟨18, isRamsey_4_4_18⟩
  exact not_isRamsey_4_4_17 (IsRamsey.mono hmem (by omega))

end Math

