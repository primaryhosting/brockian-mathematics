import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Ramsey

/-- A `b`-monochromatic set of vertices for the edge colouring `c`. -/
def Mono (c : ℕ → ℕ → Bool) (b : Bool) (t : Finset ℕ) : Prop :=
  ∀ x ∈ t, ∀ y ∈ t, x ≠ y → c x y = b

/-- The arrow relation: any colouring of the edges on the vertex set `s` contains
either a `true`-coloured clique of size `p` or a `false`-coloured clique of size `q`. -/
def Arrows (c : ℕ → ℕ → Bool) (s : Finset ℕ) (p q : ℕ) : Prop :=
  (∃ t ⊆ s, t.card = p ∧ Mono c true t) ∨ (∃ t ⊆ s, t.card = q ∧ Mono c false t)

/-- The set of `b`-coloured neighbours of `v` inside `s`. -/
def Nbr (c : ℕ → ℕ → Bool) (s : Finset ℕ) (v : ℕ) (b : Bool) : Finset ℕ :=
  (s.erase v).filter (fun u => c v u = b)

lemma mem_Nbr {c : ℕ → ℕ → Bool} {s : Finset ℕ} {v u : ℕ} {b : Bool} :
    u ∈ Nbr c s v b ↔ (u ∈ s ∧ u ≠ v) ∧ c v u = b := by
  simp [Nbr, Finset.mem_filter, Finset.mem_erase, and_comm]

lemma Nbr_subset {c : ℕ → ℕ → Bool} {s : Finset ℕ} {v : ℕ} {b : Bool} :
    Nbr c s v b ⊆ s := by
  intro u hu
  exact (mem_Nbr.mp hu).1.1

lemma card_Nbr_add (c : ℕ → ℕ → Bool) {s : Finset ℕ} {v : ℕ} (hv : v ∈ s) :
    (Nbr c s v true).card + (Nbr c s v false).card = s.card - 1 := by
  have h1 : Nbr c s v false = (s.erase v).filter (fun u => ¬ (c v u = true)) := by
    apply Finset.filter_congr
    intro u _
    simp
  rw [Nbr, h1, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]

lemma Arrows.of_subset {c : ℕ → ℕ → Bool} {s s' : Finset ℕ} {p q : ℕ} (hss : s ⊆ s')
    (h : Arrows c s p q) : Arrows c s' p q := by
  rcases h with ⟨t, hts, hcard, hmono⟩ | ⟨t, hts, hcard, hmono⟩
  · exact Or.inl ⟨t, hts.trans hss, hcard, hmono⟩
  · exact Or.inr ⟨t, hts.trans hss, hcard, hmono⟩

/-- Adjoining the vertex `v` to a monochromatic clique inside its `b`-neighbourhood. -/
lemma extend {c : ℕ → ℕ → Bool} (hsym : ∀ x y, c x y = c y x) {s t : Finset ℕ} {v : ℕ}
    {b : Bool} (hv : v ∈ s) (hts : t ⊆ Nbr c s v b) (ht : Mono c b t) :
    ∃ t' ⊆ s, t'.card = t.card + 1 ∧ Mono c b t' := by
  have hvt : v ∉ t := by
    intro hvt
    exact ((mem_Nbr.mp (hts hvt)).1.2) rfl
  refine ⟨insert v t, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hv
    · exact (mem_Nbr.mp (hts hx)).1.1
  · exact Finset.card_insert_of_notMem hvt
  · intro x hx y hy hxy
    rw [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact absurd rfl hxy
      · exact (mem_Nbr.mp (hts hy)).2
    · rcases hy with rfl | hy
      · rw [hsym]
        exact (mem_Nbr.mp (hts hx)).2
      · exact ht x hx y hy hxy

/-- `R(2, q) ≤ q`. -/
lemma arrow_two_left {c : ℕ → ℕ → Bool} (hsym : ∀ x y, c x y = c y x) {s : Finset ℕ} {q : ℕ}
    (hq : q ≤ s.card) : Arrows c s 2 q := by
  by_cases h : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ c x y = true
  · obtain ⟨x, hx, y, hy, hxy, hc⟩ := h
    refine Or.inl ⟨{x, y}, ?_, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · rw [Finset.mem_singleton] at hz; exact hz ▸ hy
    · rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
    · intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hc
      · rw [hsym]; exact hc
      · exact absurd rfl hab
  · push_neg at h
    obtain ⟨t, hts, hcard⟩ := Finset.exists_subset_card_eq hq
    refine Or.inr ⟨t, hts, hcard, ?_⟩
    intro x hx y hy hxy
    have := h x (hts hx) y (hts hy) hxy
    simpa using this

/-- `R(p, 2) ≤ p`. -/
lemma arrow_two_right {c : ℕ → ℕ → Bool} (hsym : ∀ x y, c x y = c y x) {s : Finset ℕ} {p : ℕ}
    (hp : p ≤ s.card) : Arrows c s p 2 := by
  by_cases h : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ c x y = false
  · obtain ⟨x, hx, y, hy, hxy, hc⟩ := h
    refine Or.inr ⟨{x, y}, ?_, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · rw [Finset.mem_singleton] at hz; exact hz ▸ hy
    · rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
    · intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hc
      · rw [hsym]; exact hc
      · exact absurd rfl hab
  · push_neg at h
    obtain ⟨t, hts, hcard⟩ := Finset.exists_subset_card_eq hp
    refine Or.inl ⟨t, hts, hcard, ?_⟩
    intro x hx y hy hxy
    have := h x (hts hx) y (hts hy) hxy
    simpa using this

/-- `R(3,3) ≤ 6`. -/
lemma ramsey_33 {c : ℕ → ℕ → Bool} (hsym : ∀ x y, c x y = c y x) {s : Finset ℕ}
    (hcard : 6 ≤ s.card) : Arrows c s 3 3 := by
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hne
  have hsplit := card_Nbr_add c hv
  by_cases hR : 3 ≤ (Nbr c s v true).card
  · rcases arrow_two_left hsym hR with ⟨t, hts, hcard2, hmono⟩ | ⟨t, hts, hcard3, hmono⟩
    · obtain ⟨t', ht's, hcard', hmono'⟩ := extend hsym hv hts hmono
      exact Or.inl ⟨t', ht's, by omega, hmono'⟩
    · exact Or.inr ⟨t, hts.trans Nbr_subset, hcard3, hmono⟩
  · have hB : 3 ≤ (Nbr c s v false).card := by omega
    rcases arrow_two_right hsym hB with ⟨t, hts, hcard3, hmono⟩ | ⟨t, hts, hcard2, hmono⟩
    · exact Or.inl ⟨t, hts.trans Nbr_subset, hcard3, hmono⟩
    · obtain ⟨t', ht's, hcard', hmono'⟩ := extend hsym hv hts hmono
      exact Or.inr ⟨t', ht's, by omega, hmono'⟩

/-- Handshake lemma: the sum of the red degrees is even. -/
lemma even_sum_deg (c : ℕ → ℕ → Bool) (hsym : ∀ x y, c x y = c y x) (s : Finset ℕ) :
    Even (∑ v ∈ s, (Nbr c s v true).card) := by
  classical
  set f : ℕ → ℕ → ℕ := fun v u => if v ≠ u ∧ c v u = true then 1 else 0 with hf
  have hfsym : ∀ v u, f v u = f u v := by
    intro v u
    simp only [hf]
    rw [hsym v u]
    by_cases h : v = u
    · subst h; simp
    · simp [h, Ne.symm h]
  have hdeg : ∀ v, (Nbr c s v true).card = ∑ u ∈ s, f v u := by
    intro v
    have : Nbr c s v true = s.filter (fun u => v ≠ u ∧ c v u = true) := by
      ext u
      simp only [mem_Nbr, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hu, hne⟩, hc⟩; exact ⟨hu, Ne.symm hne, hc⟩
      · rintro ⟨hu, hne, hc⟩; exact ⟨⟨hu, Ne.symm hne⟩, hc⟩
    rw [this, Finset.card_filter]
  have hsum : ∑ v ∈ s, (Nbr c s v true).card = ∑ v ∈ s, ∑ u ∈ s, f v u :=
    Finset.sum_congr rfl (fun v _ => hdeg v)
  set g : ℕ → ℕ → ℕ := fun v u => if v < u then f v u else 0 with hg
  set h : ℕ → ℕ → ℕ := fun v u => if u < v then f v u else 0 with hh
  have hsplit : ∀ v u, f v u = g v u + h v u := by
    intro v u
    simp only [hg, hh]
    rcases lt_trichotomy v u with hlt | rfl | hlt
    · simp [hlt, not_lt.mpr hlt.le]
    · simp [hf]
    · simp [hlt, not_lt.mpr hlt.le]
  have hgh : ∑ v ∈ s, ∑ u ∈ s, h v u = ∑ v ∈ s, ∑ u ∈ s, g v u := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun u _ => ?_))
    simp only [hg, hh]
    by_cases hvu : v < u
    · simp [hvu, hfsym u v]
    · simp [hvu]
  refine ⟨∑ v ∈ s, ∑ u ∈ s, g v u, ?_⟩
  rw [hsum]
  have : ∑ v ∈ s, ∑ u ∈ s, f v u
      = (∑ v ∈ s, ∑ u ∈ s, g v u) + ∑ v ∈ s, ∑ u ∈ s, h v u := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun u _ => hsplit v u)
  rw [this, hgh]

/-- `R(3,4) ≤ 9`. -/
lemma ramsey_34_card {c : ℕ → ℕ → Bool} (hsym : ∀ x y, c x y = c y x) {s : Finset ℕ}
    (hcard : s.card = 9) : Arrows c s 3 4 := by
  by_contra hcon
  rw [Arrows, not_or] at hcon
  obtain ⟨h3, h4⟩ := hcon
  push_neg at h3 h4
  have hdeg : ∀ v ∈ s, (Nbr c s v true).card = 3 := by
    intro v hv
    have hsplit := card_Nbr_add c hv
    have hR : (Nbr c s v true).card ≤ 3 := by
      by_contra hR
      push_neg at hR
      have h4le : (4 : ℕ) ≤ (Nbr c s v true).card := hR
      rcases arrow_two_left hsym h4le with ⟨t, hts, hc2, hmono⟩ | ⟨t, hts, hc4, hmono⟩
      · obtain ⟨t', ht's, hcard', hmono'⟩ := extend hsym hv hts hmono
        exact absurd hmono' (h3 t' ht's (by omega))
      · exact absurd hmono (h4 t (hts.trans Nbr_subset) hc4)
    have hB : (Nbr c s v false).card ≤ 5 := by
      by_contra hB
      push_neg at hB
      have h6le : (6 : ℕ) ≤ (Nbr c s v false).card := hB
      rcases ramsey_33 hsym h6le with ⟨t, hts, hc3, hmono⟩ | ⟨t, hts, hc3, hmono⟩
      · exact absurd hmono (h3 t (hts.trans Nbr_subset) hc3)
      · obtain ⟨t', ht's, hcard', hmono'⟩ := extend hsym hv hts hmono
        exact absurd hmono' (h4 t' ht's (by omega))
    omega
  have hsum : ∑ v ∈ s, (Nbr c s v true).card = 27 := by
    rw [Finset.sum_congr rfl hdeg, Finset.sum_const, hcard, smul_eq_mul]
  have heven := even_sum_deg c hsym s
  rw [hsum] at heven
  exact (by decide : ¬ Even 27) heven

/-- `R(3,4) ≤ 9`, monotone form. -/
lemma ramsey_34 {c : ℕ → ℕ → Bool} (hsym : ∀ x y, c x y = c y x) {s : Finset ℕ}
    (hcard : 9 ≤ s.card) : Arrows c s 3 4 := by
  obtain ⟨t, hts, hc⟩ := Finset.exists_subset_card_eq hcard
  exact Arrows.of_subset hts (ramsey_34_card hsym hc)

/-- `R(3,5) ≤ 14`. -/
lemma ramsey_35 {c : ℕ → ℕ → Bool} (hsym : ∀ x y, c x y = c y x) {s : Finset ℕ}
    (hcard : 14 ≤ s.card) : Arrows c s 3 5 := by
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hne
  have hsplit := card_Nbr_add c hv
  by_cases hR : 5 ≤ (Nbr c s v true).card
  · rcases arrow_two_left hsym hR with ⟨t, hts, hc2, hmono⟩ | ⟨t, hts, hc5, hmono⟩
    · obtain ⟨t', ht's, hcard', hmono'⟩ := extend hsym hv hts hmono
      exact Or.inl ⟨t', ht's, by omega, hmono'⟩
    · exact Or.inr ⟨t, hts.trans Nbr_subset, hc5, hmono⟩
  · have hB : 9 ≤ (Nbr c s v false).card := by omega
    rcases ramsey_34 hsym hB with ⟨t, hts, hc3, hmono⟩ | ⟨t, hts, hc4, hmono⟩
    · exact Or.inl ⟨t, hts.trans Nbr_subset, hc3, hmono⟩
    · obtain ⟨t', ht's, hcard', hmono'⟩ := extend hsym hv hts hmono
      exact Or.inr ⟨t', ht's, by omega, hmono'⟩

/-- The critical colouring: the circulant graph on `ℤ/13` with connection set `{±1, ±5}`. -/
def cQ (x y : ℕ) : Bool :=
  let d := (x + 12 * y) % 13
  decide (d = 1 ∨ d = 5 ∨ d = 8 ∨ d = 12)

lemma cQ_symm : ∀ x y, cQ x y = cQ y x := by
  intro x y
  simp only [cQ, decide_eq_decide]
  omega

lemma cQ_no_red_triangle :
    ∀ t ∈ (Finset.range 13).powersetCard 3,
      ¬ (∀ x ∈ t, ∀ y ∈ t, x ≠ y → cQ x y = true) := by decide

lemma cQ_no_blue_five :
    ∀ t ∈ (Finset.range 13).powersetCard 5,
      ¬ (∀ x ∈ t, ∀ y ∈ t, x ≠ y → cQ x y = false) := by decide

end Ramsey

namespace Math

/-- **The Ramsey number `R(3,5)` equals `14`**: `14` is the least `N` such that every
graph on `N` vertices contains a triangle or an independent set of size `5`. -/
theorem ramsey_3_5 :
    IsLeast {N : ℕ | ∀ G : SimpleGraph (Fin N),
      (∃ s : Finset (Fin N), G.IsNClique 3 s) ∨ (∃ s : Finset (Fin N), Gᶜ.IsNClique 5 s)} 14 := by
  constructor
  · -- upper bound: every graph on 14 vertices works
    intro G
    set c : ℕ → ℕ → Bool :=
      fun x y => decide (∃ (hx : x < 14) (hy : y < 14), G.Adj ⟨x, hx⟩ ⟨y, hy⟩) with hc
    have hsym : ∀ x y, c x y = c y x := by
      intro x y
      simp only [hc, decide_eq_decide]
      constructor
      · rintro ⟨hx, hy, hadj⟩; exact ⟨hy, hx, hadj.symm⟩
      · rintro ⟨hy, hx, hadj⟩; exact ⟨hx, hy, hadj.symm⟩
    have hcard : (14 : ℕ) ≤ (Finset.range 14).card := by simp
    rcases Ramsey.ramsey_35 hsym hcard with ⟨t, hts, hc3, hmono⟩ | ⟨t, hts, hc5, hmono⟩
    · left
      have hlt : ∀ m ∈ t, m < 14 := fun m hm => Finset.mem_range.mp (hts hm)
      refine ⟨t.attachFin hlt, ?_, ?_⟩
      · intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_attachFin] at ha hb
        have hne : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.ext h)
        have := hmono _ ha _ hb hne
        simp only [hc, decide_eq_true_eq] at this
        obtain ⟨hx, hy, hadj⟩ := this
        simpa using hadj
      · simpa using hc3
    · right
      have hlt : ∀ m ∈ t, m < 14 := fun m hm => Finset.mem_range.mp (hts hm)
      refine ⟨t.attachFin hlt, ?_, ?_⟩
      · intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_attachFin] at ha hb
        have hne : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.ext h)
        have := hmono _ ha _ hb hne
        simp only [hc, decide_eq_false_iff_not, not_exists] at this
        refine ⟨hab, fun hadj => ?_⟩
        exact this a.isLt b.isLt (by simpa using hadj)
      · simpa using hc5
  · -- lower bound: 13 vertices are not enough
    intro N hN
    by_contra hlt
    push_neg at hlt
    have hN13 : N ≤ 13 := by omega
    set G : SimpleGraph (Fin N) :=
      { Adj := fun x y => x ≠ y ∧ Ramsey.cQ (x : ℕ) (y : ℕ) = true
        symm := by
          rintro x y ⟨hne, hadj⟩
          exact ⟨hne.symm, by rw [Ramsey.cQ_symm]; exact hadj⟩
        loopless := ⟨fun x h => h.1 rfl⟩ } with hG
    rcases hN G with ⟨s, hclique, hcard⟩ | ⟨s, hclique, hcard⟩
    · refine Ramsey.cQ_no_red_triangle (s.image (Fin.val)) ?_ ?_
      · rw [Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro x hx
          obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_range.mpr (by omega)
        · rw [Finset.card_image_of_injective _ Fin.val_injective, hcard]
      · intro x hx y hy hxy
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
        have hab : a ≠ b := fun h => hxy (by rw [h])
        exact (hclique (by simpa using ha) (by simpa using hb) hab).2
    · refine Ramsey.cQ_no_blue_five (s.image (Fin.val)) ?_ ?_
      · rw [Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro x hx
          obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_range.mpr (by omega)
        · rw [Finset.card_image_of_injective _ Fin.val_injective, hcard]
      · intro x hx y hy hxy
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
        have hab : a ≠ b := fun h => hxy (by rw [h])
        have := hclique (by simpa using ha) (by simpa using hb) hab
        simp only [SimpleGraph.compl_adj, hG] at this
        have := this.2
        simp only [not_and, ne_eq] at this
        simpa using this hab

end Math

