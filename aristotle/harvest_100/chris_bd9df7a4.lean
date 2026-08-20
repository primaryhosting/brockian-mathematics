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

/-
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-! ## Relative (Finset-localized) triangles and independent sets -/

section Rel

variable {V : Type*} [LinearOrder V]

/-- `t` is an independent set of `G`. -/
def IndepOn (G : SimpleGraph V) (t : Finset V) : Prop :=
  ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ¬ G.Adj x y

/-- The vertex set `s` contains a triangle of `G`. -/
def HasTriIn (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∃ t ⊆ s, t.card = 3 ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → G.Adj x y

/-- The vertex set `s` contains an independent set of `G` of size `k`. -/
def HasIndepIn (G : SimpleGraph V) (k : ℕ) (s : Finset V) : Prop :=
  ∃ t ⊆ s, t.card = k ∧ IndepOn G t

omit [LinearOrder V] in
lemma mono_tri {G : SimpleGraph V} {s s' : Finset V} (h : s ⊆ s') :
    HasTriIn G s → HasTriIn G s' := by
  rintro ⟨t, hts, hcard, hadj⟩
  exact ⟨t, hts.trans h, hcard, hadj⟩

omit [LinearOrder V] in
lemma mono_indep {G : SimpleGraph V} {k : ℕ} {s s' : Finset V} (h : s ⊆ s') :
    HasIndepIn G k s → HasIndepIn G k s' := by
  rintro ⟨t, hts, hcard, hind⟩
  exact ⟨t, hts.trans h, hcard, hind⟩

lemma indepOn_pair {G : SimpleGraph V} {a b : V} (h : ¬ G.Adj a b) : IndepOn G {a, b} := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact h
  · exact fun hadj => h hadj.symm
  · exact absurd rfl hxy

/-- `R(3,2) ≤ 3`. -/
lemma key2 (G : SimpleGraph V) (s : Finset V) (hs : 3 ≤ s.card) :
    HasTriIn G s ∨ HasIndepIn G 2 s := by
  classical
  obtain ⟨t, hts, hcard⟩ := Finset.exists_subset_card_eq hs
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  have ha : a ∈ s := hts (by simp)
  have hb : b ∈ s := hts (by simp)
  have hc : c ∈ s := hts (by simp)
  by_cases h1 : G.Adj a b
  · by_cases h2 : G.Adj a c
    · by_cases h3 : G.Adj b c
      · refine Or.inl ⟨{a, b, c}, hts, hcard, ?_⟩
        intro x hx y hy hxy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
          first
            | exact absurd rfl hxy
            | assumption
            | exact h1.symm
            | exact h2.symm
            | exact h3.symm
      · exact Or.inr ⟨{b, c}, Finset.insert_subset hb (Finset.singleton_subset_iff.mpr hc),
          Finset.card_pair hbc, indepOn_pair h3⟩
    · exact Or.inr ⟨{a, c}, Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hc),
        Finset.card_pair hac, indepOn_pair h2⟩
  · exact Or.inr ⟨{a, b}, Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb),
      Finset.card_pair hab, indepOn_pair h1⟩

/-- The Ramsey recursion `R(3, k+1) ≤ R(3,k) + k + 1`. -/
lemma step (G : SimpleGraph V) (k m : ℕ)
    (IH : ∀ s : Finset V, m ≤ s.card → HasTriIn G s ∨ HasIndepIn G k s)
    (s : Finset V) (hs : k + m + 1 ≤ s.card) :
    HasTriIn G s ∨ HasIndepIn G (k + 1) s := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hT, hI⟩ := hcon
  have hne : s.Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨v, hv⟩ := hne
  set N := s.filter (fun u => G.Adj v u) with hNdef
  set M := s.filter (fun u => ¬ G.Adj v u ∧ u ≠ v) with hMdef
  have hunion : N ∪ M = s.erase v := by
    ext u
    simp only [hNdef, hMdef, Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro (⟨hu, ha⟩ | ⟨hu, _, hne⟩)
      · exact ⟨fun h => G.irrefl (h ▸ ha), hu⟩
      · exact ⟨hne, hu⟩
    · rintro ⟨hne, hu⟩
      by_cases ha : G.Adj v u
      · exact Or.inl ⟨hu, ha⟩
      · exact Or.inr ⟨hu, ha, hne⟩
  have hdisj : Disjoint N M := by
    rw [Finset.disjoint_left]
    rintro a ha hb
    simp only [hNdef, hMdef, Finset.mem_filter] at ha hb
    exact hb.2.1 ha.2
  have hcards : N.card + M.card = s.card - 1 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_erase_of_mem hv]
  -- the neighbourhood of `v` is independent, since `G` has no triangle inside `s`
  have hNb : N.card ≤ k := by
    by_contra hbig
    push_neg at hbig
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show k + 1 ≤ N.card by omega)
    refine hI ⟨t, hts.trans (Finset.filter_subset _ _), htc, ?_⟩
    intro x hx y hy hxy hadj
    have hxN := hts hx
    have hyN := hts hy
    simp only [hNdef, Finset.mem_filter] at hxN hyN
    have hvx : G.Adj v x := hxN.2
    have hvy : G.Adj v y := hyN.2
    refine hT ⟨{v, x, y}, ?_, ?_, ?_⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hv
      · exact hxN.1
      · exact hyN.1
    · have hvx' : v ≠ x := fun h => G.irrefl (h ▸ hvx)
      have hvy' : v ≠ y := fun h => G.irrefl (h ▸ hvy)
      rw [Finset.card_insert_of_notMem (by simp [hvx', hvy']),
        Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
    · intro p hp q hq hpq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
      rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
        first
          | exact absurd rfl hpq
          | assumption
          | exact hvx.symm
          | exact hvy.symm
          | exact hadj.symm
  -- the non-neighbourhood of `v` contains no independent set of size `k`
  have hMb : M.card < m := by
    by_contra hbig
    push_neg at hbig
    rcases IH M hbig with h | h
    · exact hT (mono_tri (Finset.filter_subset _ _) h)
    · obtain ⟨t, htM, htc, htind⟩ := h
      have hMnb : ∀ z ∈ t, ¬ G.Adj v z ∧ z ≠ v := by
        intro z hz
        have := htM hz
        simp only [hMdef, Finset.mem_filter] at this
        exact this.2
      have hvt : v ∉ t := fun hvt => (hMnb v hvt).2 rfl
      refine hI ⟨insert v t, ?_, ?_, ?_⟩
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hv
        · exact (Finset.filter_subset _ _) (htM hz)
      · rw [Finset.card_insert_of_notMem hvt, htc]
      · intro x hx y hy hxy
        have hxs := Finset.mem_insert.mp hx
        have hys := Finset.mem_insert.mp hy
        rcases hxs with rfl | hx' <;> rcases hys with rfl | hy'
        · exact absurd rfl hxy
        · exact (hMnb y hy').1
        · exact fun hadj => (hMnb x hx').1 hadj.symm
        · exact htind x hx' y hy' hxy
  omega

/-- `R(3,3) ≤ 6`. -/
lemma key3 (G : SimpleGraph V) (s : Finset V) (hs : 6 ≤ s.card) :
    HasTriIn G s ∨ HasIndepIn G 3 s :=
  step G 2 3 (fun s hs => key2 G s hs) s (by omega)

/-- `R(3,4) ≤ 9`: here a parity (handshake) argument is needed. -/
lemma key4 (G : SimpleGraph V) (s : Finset V) (hs : 9 ≤ s.card) :
    HasTriIn G s ∨ HasIndepIn G 4 s := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hT0, hI0⟩ := hcon
  obtain ⟨s, hsub, hcard9⟩ := Finset.exists_subset_card_eq hs
  have hT : ¬ HasTriIn G s := fun h => hT0 (mono_tri hsub h)
  have hI : ¬ HasIndepIn G 4 s := fun h => hI0 (mono_indep hsub h)
  -- every vertex of `s` has exactly 3 neighbours inside `s`
  have hdeg : ∀ v ∈ s, (s.filter (fun u => G.Adj v u)).card = 3 := by
    intro v hv
    set N := s.filter (fun u => G.Adj v u) with hNdef
    set M := s.filter (fun u => ¬ G.Adj v u ∧ u ≠ v) with hMdef
    have hunion : N ∪ M = s.erase v := by
      ext u
      simp only [hNdef, hMdef, Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro (⟨hu, ha⟩ | ⟨hu, _, hne⟩)
        · exact ⟨fun h => G.irrefl (h ▸ ha), hu⟩
        · exact ⟨hne, hu⟩
      · rintro ⟨hne, hu⟩
        by_cases ha : G.Adj v u
        · exact Or.inl ⟨hu, ha⟩
        · exact Or.inr ⟨hu, ha, hne⟩
    have hdisj : Disjoint N M := by
      rw [Finset.disjoint_left]
      rintro a ha hb
      simp only [hNdef, hMdef, Finset.mem_filter] at ha hb
      exact hb.2.1 ha.2
    have hcards : N.card + M.card = 8 := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_erase_of_mem hv, hcard9]
    have hNb : N.card ≤ 3 := by
      by_contra hbig
      push_neg at hbig
      obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show 4 ≤ N.card by omega)
      refine hI ⟨t, hts.trans (Finset.filter_subset _ _), htc, ?_⟩
      intro x hx y hy hxy hadj
      have hxN := hts hx
      have hyN := hts hy
      simp only [hNdef, Finset.mem_filter] at hxN hyN
      have hvx : G.Adj v x := hxN.2
      have hvy : G.Adj v y := hyN.2
      refine hT ⟨{v, x, y}, ?_, ?_, ?_⟩
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hv
        · exact hxN.1
        · exact hyN.1
      · have hvx' : v ≠ x := fun h => G.irrefl (h ▸ hvx)
        have hvy' : v ≠ y := fun h => G.irrefl (h ▸ hvy)
        rw [Finset.card_insert_of_notMem (by simp [hvx', hvy']),
          Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
      · intro p hp q hq hpq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
        rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
          first
            | exact absurd rfl hpq
            | assumption
            | exact hvx.symm
            | exact hvy.symm
            | exact hadj.symm
    have hMb : M.card < 6 := by
      by_contra hbig
      push_neg at hbig
      rcases key3 G M hbig with h | h
      · exact hT (mono_tri (Finset.filter_subset _ _) h)
      · obtain ⟨t, htM, htc, htind⟩ := h
        have hMnb : ∀ z ∈ t, ¬ G.Adj v z ∧ z ≠ v := by
          intro z hz
          have := htM hz
          simp only [hMdef, Finset.mem_filter] at this
          exact this.2
        have hvt : v ∉ t := fun hvt => (hMnb v hvt).2 rfl
        refine hI ⟨insert v t, ?_, ?_, ?_⟩
        · intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact hv
          · exact (Finset.filter_subset _ _) (htM hz)
        · rw [Finset.card_insert_of_notMem hvt, htc]
        · intro x hx y hy hxy
          have hxs := Finset.mem_insert.mp hx
          have hys := Finset.mem_insert.mp hy
          rcases hxs with rfl | hx' <;> rcases hys with rfl | hy'
          · exact absurd rfl hxy
          · exact (hMnb y hy').1
          · exact fun hadj => (hMnb x hx').1 hadj.symm
          · exact htind x hx' y hy' hxy
    omega
  -- double counting the ordered adjacent pairs inside `s`
  set P := (s ×ˢ s).filter (fun p => G.Adj p.1 p.2) with hPdef
  have hP27 : P.card = 27 := by
    rw [hPdef, Finset.card_filter, Finset.sum_product]
    have hsum : ∀ v ∈ s, (∑ u ∈ s, if G.Adj v u then 1 else 0) = 3 := by
      intro v hv
      rw [← Finset.card_filter]
      exact hdeg v hv
    rw [Finset.sum_congr rfl hsum, Finset.sum_const, hcard9]
    simp
  have hswap : (P.filter (fun p => p.1 < p.2)).image Prod.swap
      = P.filter (fun p => ¬ p.1 < p.2) := by
    ext p
    simp only [Finset.mem_image, Finset.mem_filter, hPdef, Finset.mem_product]
    constructor
    · rintro ⟨q, ⟨⟨⟨hq1, hq2⟩, hqadj⟩, hqlt⟩, rfl⟩
      exact ⟨⟨⟨hq2, hq1⟩, hqadj.symm⟩, by simpa using le_of_lt hqlt⟩
    · rintro ⟨⟨⟨hp1, hp2⟩, hpadj⟩, hple⟩
      refine ⟨p.swap, ⟨⟨⟨hp2, hp1⟩, hpadj.symm⟩, ?_⟩, by simp⟩
      have hne : p.1 ≠ p.2 := fun h => G.irrefl (h ▸ hpadj)
      simp only [Prod.fst_swap, Prod.snd_swap]
      exact lt_of_le_of_ne (not_lt.mp hple) (Ne.symm hne)
  have hhalf : (P.filter (fun p => p.1 < p.2)).card
      + (P.filter (fun p => ¬ p.1 < p.2)).card = P.card :=
    Finset.card_filter_add_card_filter_not _
  rw [← hswap, Finset.card_image_of_injective _ Prod.swap_injective, hP27] at hhalf
  omega

/-- `R(3,5) ≤ 14`. -/
lemma key5 (G : SimpleGraph V) (s : Finset V) (hs : 14 ≤ s.card) :
    HasTriIn G s ∨ HasIndepIn G 5 s :=
  step G 4 9 (fun s hs => key4 G s hs) s (by omega)

end Rel

/-! ## The Ramsey property -/

/-- Every graph on `n` vertices contains a triangle or an independent set of size 5;
equivalently, every red/blue colouring of the edges of `Kₙ` has a red triangle or a blue `K₅`. -/
def RamseyProp (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (∃ s : Finset (Fin n), s.card = 3 ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y) ∨
    (∃ s : Finset (Fin n), s.card = 5 ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ G.Adj x y)

lemma ramseyProp_14 : RamseyProp 14 := by
  intro G
  have h : (14 : ℕ) ≤ (Finset.univ : Finset (Fin 14)).card := by simp
  rcases key5 G Finset.univ h with ⟨t, _, hc, hadj⟩ | ⟨t, _, hc, hind⟩
  · exact Or.inl ⟨t, hc, hadj⟩
  · exact Or.inr ⟨t, hc, hind⟩

lemma ramseyProp_mono {n m : ℕ} (hnm : n ≤ m) (h : RamseyProp n) : RamseyProp m := by
  classical
  intro G
  set f : Fin n → Fin m := fun i => ⟨i.1, lt_of_lt_of_le i.2 hnm⟩ with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    simpa [hf, Fin.ext_iff] using hab
  rcases h (SimpleGraph.comap f G) with ⟨s, hc, hadj⟩ | ⟨s, hc, hind⟩
  · refine Or.inl ⟨s.image f, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hfinj, hc]
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      exact hadj a ha b hb (fun h => hxy (by rw [h]))
  · refine Or.inr ⟨s.image f, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hfinj, hc]
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      exact hind a ha b hb (fun h => hxy (by rw [h]))

/-! ## The lower bound: the circulant graph `C₁₃(1,5)` -/

/-- Adjacency of the circulant graph on `ℤ/13` with connection set `{±1, ±5}`. -/
def cB (a b : Fin 13) : Bool :=
  ((a.val + 13 - b.val) % 13 = 1) || ((a.val + 13 - b.val) % 13 = 5) ||
  ((a.val + 13 - b.val) % 13 = 8) || ((a.val + 13 - b.val) % 13 = 12)

/-- The circulant graph `C₁₃(1,5)`: it is triangle-free and has independence number 4,
which witnesses `R(3,5) > 13`. -/
def C13 : SimpleGraph (Fin 13) where
  Adj a b := cB a b = true
  symm := by
    have h : ∀ a b : Fin 13, cB a b = true → cB b a = true := by decide
    intro a b hab
    exact h a b hab
  loopless := by
    have h : ∀ a : Fin 13, cB a a = false := by decide
    constructor
    intro a ha
    simp [h a] at ha

lemma C13_triangle_free :
    ∀ a b c : Fin 13, cB a b = true → cB b c = true → cB a c = true → False := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma C13_no_indep5 : ∀ a b c d e : Fin 13, a < b → b < c → c < d → d < e →
    (cB a b = true ∨ cB a c = true ∨ cB a d = true ∨ cB a e = true ∨ cB b c = true ∨
      cB b d = true ∨ cB b e = true ∨ cB c d = true ∨ cB c e = true ∨ cB d e = true) := by
  decide

lemma not_ramseyProp_13 : ¬ RamseyProp 13 := by
  intro h
  rcases h C13 with ⟨s, hc, hadj⟩ | ⟨s, hc, hind⟩
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hc
    exact C13_triangle_free a b c
      (hadj a (by simp) b (by simp) hab)
      (hadj b (by simp) c (by simp) hbc)
      (hadj a (by simp) c (by simp) hac)
  · set g := s.orderIsoOfFin hc with hg
    set f : Fin 5 → Fin 13 := fun i => (g i : Fin 13) with hfdef
    have hmem : ∀ i, f i ∈ s := fun i => (g i).2
    have hlt : ∀ i j : Fin 5, i < j → f i < f j := fun i j hij => g.lt_iff_lt.mpr hij
    have key := C13_no_indep5 (f 0) (f 1) (f 2) (f 3) (f 4)
      (hlt 0 1 (by decide)) (hlt 1 2 (by decide)) (hlt 2 3 (by decide)) (hlt 3 4 (by decide))
    have hnadj : ∀ i j : Fin 5, i < j → cB (f i) (f j) = false := by
      intro i j hij
      have hne : f i ≠ f j := ne_of_lt (hlt i j hij)
      have := hind (f i) (hmem i) (f j) (hmem j) hne
      simpa [C13] using this
    rcases key with h | h | h | h | h | h | h | h | h | h
    · simp [hnadj 0 1 (by decide)] at h
    · simp [hnadj 0 2 (by decide)] at h
    · simp [hnadj 0 3 (by decide)] at h
    · simp [hnadj 0 4 (by decide)] at h
    · simp [hnadj 1 2 (by decide)] at h
    · simp [hnadj 1 3 (by decide)] at h
    · simp [hnadj 1 4 (by decide)] at h
    · simp [hnadj 2 3 (by decide)] at h
    · simp [hnadj 2 4 (by decide)] at h
    · simp [hnadj 3 4 (by decide)] at h

/-- **R(3,5) = 14**: 14 is the least `n` such that every graph on `n` vertices contains a
triangle or an independent set of size 5. -/
theorem ramsey_3_5 : IsLeast {n : ℕ | RamseyProp n} 14 := by
  refine ⟨ramseyProp_14, ?_⟩
  intro n hn
  by_contra hlt
  push_neg at hlt
  exact not_ramseyProp_13 (ramseyProp_mono (by omega) hn)

end Math

