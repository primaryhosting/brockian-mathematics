import Mathlib
/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math

/-- `MonoClique c b T` says that all pairs of distinct vertices of `T` get colour `b`
under the (edge-)colouring `c`. -/
def MonoClique {n : ℕ} (c : Fin n → Fin n → Bool) (b : Bool) (T : Finset (Fin n)) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x ≠ y → c x y = b

instance {n : ℕ} (c : Fin n → Fin n → Bool) (b : Bool) (T : Finset (Fin n)) :
    Decidable (MonoClique c b T) := by
  unfold MonoClique; infer_instance

/-- `HasRamsey34 n` says: every 2-colouring of the edges of the complete graph on `n`
vertices contains a `true`-coloured triangle or a `false`-coloured `K₄`. -/
def HasRamsey34 (n : ℕ) : Prop :=
  ∀ c : Fin n → Fin n → Bool, (∀ x y, c x y = c y x) →
    (∃ T : Finset (Fin n), T.card = 3 ∧ MonoClique c true T) ∨
    (∃ T : Finset (Fin n), T.card = 4 ∧ MonoClique c false T)

lemma MonoClique.subset {n : ℕ} {c : Fin n → Fin n → Bool} {b : Bool} {S T : Finset (Fin n)}
    (hTS : T ⊆ S) (h : MonoClique c b S) : MonoClique c b T :=
  fun _ hx _ hy hxy => h _ (hTS hx) _ (hTS hy) hxy

lemma MonoClique.insert_vertex {n : ℕ} {c : Fin n → Fin n → Bool} {b : Bool}
    {T : Finset (Fin n)} {v : Fin n} (hsymm : ∀ x y, c x y = c y x)
    (hT : MonoClique c b T) (hv : ∀ x ∈ T, c v x = b) :
    MonoClique c b (insert v T) := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert] at hx hy
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · exact absurd rfl hxy
    · exact hv y hy
  · rcases hy with rfl | hy
    · rw [hsymm]; exact hv x hx
    · exact hT x hx y hy hxy

section Nine

variable {c : Fin 9 → Fin 9 → Bool}

/-- The `true`-neighbourhood of a vertex. -/
def redN (c : Fin 9 → Fin 9 → Bool) (v : Fin 9) : Finset (Fin 9) :=
  (Finset.univ.erase v).filter (fun u => c v u = true)

/-- The `false`-neighbourhood of a vertex. -/
def blueN (c : Fin 9 → Fin 9 → Bool) (v : Fin 9) : Finset (Fin 9) :=
  (Finset.univ.erase v).filter (fun u => c v u = false)

lemma mem_redN {v u : Fin 9} : u ∈ redN c v ↔ u ≠ v ∧ c v u = true := by
  simp [redN]

lemma mem_blueN {v u : Fin 9} : u ∈ blueN c v ↔ u ≠ v ∧ c v u = false := by
  simp [blueN]

lemma card_redN_add_card_blueN (v : Fin 9) : (redN c v).card + (blueN c v).card = 8 := by
  have hb : blueN c v = (Finset.univ.erase v).filter (fun u => ¬ (c v u = true)) := by
    simp [blueN, Bool.not_eq_true]
  rw [hb, redN, Finset.card_filter_add_card_filter_not]
  simp

/-- With no `true` triangle, the `true`-neighbourhood of a vertex is `false`-monochromatic. -/
lemma redN_mono_false (hsymm : ∀ x y, c x y = c y x)
    (hR : ∀ T : Finset (Fin 9), T.card = 3 → ¬ MonoClique c true T) (v : Fin 9) :
    MonoClique c false (redN c v) := by
  intro x hx y hy hxy
  rw [mem_redN] at hx hy
  by_contra hc
  have hxytrue : c x y = true := by simpa using hc
  refine hR {v, x, y} ?_ ?_
  · rw [Finset.card_eq_three]
    exact ⟨v, x, y, (Ne.symm hx.1), (Ne.symm hy.1), hxy, rfl⟩
  · have hT : MonoClique c true {x, y} := by
      intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hxytrue
      · rw [hsymm]; exact hxytrue
      · exact absurd rfl hab
    refine MonoClique.insert_vertex hsymm hT ?_
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hx.2
    · exact hy.2

/-- With no `false` `K₄`, the `false`-neighbourhood of a vertex has no `false` triangle. -/
lemma blueN_no_false_triangle (hsymm : ∀ x y, c x y = c y x)
    (hB : ∀ T : Finset (Fin 9), T.card = 4 → ¬ MonoClique c false T) (v : Fin 9)
    (T : Finset (Fin 9)) (hTsub : T ⊆ blueN c v) (hT3 : T.card = 3) :
    ¬ MonoClique c false T := by
  intro hm
  have hv : v ∉ T := by
    intro hvT
    have := hTsub hvT
    rw [mem_blueN] at this
    exact this.1 rfl
  refine hB (insert v T) ?_ (MonoClique.insert_vertex hsymm hm ?_)
  · rw [Finset.card_insert_of_notMem hv, hT3]
  · intro x hx
    have := hTsub hx
    rw [mem_blueN] at this
    exact this.2

lemma card_redN_le (hsymm : ∀ x y, c x y = c y x)
    (hR : ∀ T : Finset (Fin 9), T.card = 3 → ¬ MonoClique c true T)
    (hB : ∀ T : Finset (Fin 9), T.card = 4 → ¬ MonoClique c false T) (v : Fin 9) :
    (redN c v).card ≤ 3 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨S, hS, hcard⟩ :=
    Finset.exists_subset_card_eq (s := redN c v) (n := 4) (by omega)
  exact hB S hcard ((redN_mono_false hsymm hR v).subset hS)

lemma card_blueN_le (hsymm : ∀ x y, c x y = c y x)
    (hR : ∀ T : Finset (Fin 9), T.card = 3 → ¬ MonoClique c true T)
    (hB : ∀ T : Finset (Fin 9), T.card = 4 → ¬ MonoClique c false T) (v : Fin 9) :
    (blueN c v).card ≤ 5 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨B, hBsub, hB6⟩ :=
    Finset.exists_subset_card_eq (s := blueN c v) (n := 6) (by omega)
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
  have hB'card : (B.erase w).card = 5 := by rw [Finset.card_erase_of_mem hw, hB6]
  have hsum : ((B.erase w).filter (fun u => c w u = true)).card
      + ((B.erase w).filter (fun u => c w u = false)).card = 5 := by
    have h := Finset.card_filter_add_card_filter_not (s := B.erase w)
      (p := fun u => c w u = true)
    have h2 : (B.erase w).filter (fun u => ¬ (c w u = true))
        = (B.erase w).filter (fun u => c w u = false) := by
      simp [Bool.not_eq_true]
    rw [h2] at h
    omega
  by_cases h3 : 3 ≤ ((B.erase w).filter (fun u => c w u = true)).card
  · obtain ⟨T, hTsub, hT3⟩ := Finset.exists_subset_card_eq h3
    refine blueN_no_false_triangle hsymm hB v T ?_ hT3 ?_
    · intro x hx
      exact hBsub (Finset.mem_of_mem_erase (Finset.mem_filter.mp (hTsub hx)).1)
    · refine (redN_mono_false hsymm hR w).subset ?_
      intro x hx
      have hx' := Finset.mem_filter.mp (hTsub hx)
      rw [mem_redN]
      exact ⟨Finset.ne_of_mem_erase hx'.1, hx'.2⟩
  · have h3b : 3 ≤ ((B.erase w).filter (fun u => c w u = false)).card := by omega
    obtain ⟨T, hTsub, hT3⟩ := Finset.exists_subset_card_eq h3b
    by_cases hred : MonoClique c true T
    · exact hR T hT3 hred
    · obtain ⟨x, hx, y, hy, hxy, hne⟩ : ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ c x y = false := by
        unfold MonoClique at hred
        push_neg at hred
        obtain ⟨x, hx, y, hy, hxy, h⟩ := hred
        exact ⟨x, hx, y, hy, hxy, by simpa using h⟩
      have hxm := Finset.mem_filter.mp (hTsub hx)
      have hym := Finset.mem_filter.mp (hTsub hy)
      refine blueN_no_false_triangle hsymm hB v {w, x, y} ?_ ?_ ?_
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hBsub hw
        · exact hBsub (Finset.mem_of_mem_erase hxm.1)
        · exact hBsub (Finset.mem_of_mem_erase hym.1)
      · rw [Finset.card_eq_three]
        exact ⟨w, x, y, (Finset.ne_of_mem_erase hxm.1).symm,
          (Finset.ne_of_mem_erase hym.1).symm, hxy, rfl⟩
      · have hT2 : MonoClique c false {x, y} := by
          intro a ha b hb hab
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact absurd rfl hab
          · exact hne
          · rw [hsymm]; exact hne
          · exact absurd rfl hab
        refine MonoClique.insert_vertex hsymm hT2 ?_
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact hxm.2
        · exact hym.2

lemma card_redN_eq_three (hsymm : ∀ x y, c x y = c y x)
    (hR : ∀ T : Finset (Fin 9), T.card = 3 → ¬ MonoClique c true T)
    (hB : ∀ T : Finset (Fin 9), T.card = 4 → ¬ MonoClique c false T) (v : Fin 9) :
    (redN c v).card = 3 := by
  have h1 := card_redN_add_card_blueN (c := c) v
  have h2 := card_redN_le hsymm hR hB v
  have h3 := card_blueN_le hsymm hR hB v
  omega

/-- The parity obstruction: a graph on 9 vertices cannot be 3-regular. -/
lemma not_three_regular (hsymm : ∀ x y, c x y = c y x)
    (hdeg : ∀ v, (redN c v).card = 3) : False := by
  classical
  let G : SimpleGraph (Fin 9) :=
  { Adj := fun u v => u ≠ v ∧ c u v = true
    symm := by
      rintro u v ⟨h1, h2⟩
      exact ⟨h1.symm, by rw [hsymm]; exact h2⟩
    loopless := by
      constructor
      rintro u ⟨h1, -⟩
      exact h1 rfl }
  have hdG : ∀ v, G.degree v = 3 := by
    intro v
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, ← hdeg v]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_redN, G]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2⟩
  have h := SimpleGraph.sum_degrees_eq_twice_card_edges G
  simp only [hdG, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega

theorem ramsey34_nine : HasRamsey34 9 := by
  intro c hsymm
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h4⟩ := hcon
  exact not_three_regular hsymm (card_redN_eq_three hsymm h3 h4)

end Nine

/-- The Wagner graph (Möbius ladder) on `ℤ/8`: `i ~ j` iff `i - j ∈ {1, 4, 7}`. -/
def wagner (i j : Fin 8) : Bool :=
  ((i.val + 8 - j.val) % 8 == 1) || ((i.val + 8 - j.val) % 8 == 4) ||
    ((i.val + 8 - j.val) % 8 == 7)

lemma wagner_symm : ∀ x y, wagner x y = wagner y x := by decide

lemma wagner_no_triangle : ∀ T : Finset (Fin 8), T.card = 3 → ¬ MonoClique wagner true T := by
  decide

lemma wagner_no_indep_four : ∀ T : Finset (Fin 8), T.card = 4 → ¬ MonoClique wagner false T := by
  decide

theorem not_hasRamsey34_eight : ¬ HasRamsey34 8 := by
  intro h
  rcases h wagner wagner_symm with ⟨T, hT, hm⟩ | ⟨T, hT, hm⟩
  · exact wagner_no_triangle T hT hm
  · exact wagner_no_indep_four T hT hm

lemma HasRamsey34.mono {n m : ℕ} (h : HasRamsey34 n) (hnm : n ≤ m) : HasRamsey34 m := by
  intro c hsymm
  have key : ∀ (b : Bool) (T : Finset (Fin n)),
      MonoClique (fun i j => c (Fin.castLE hnm i) (Fin.castLE hnm j)) b T →
      MonoClique c b (T.map ⟨Fin.castLE hnm, Fin.castLE_injective hnm⟩) := by
    intro b T hT x hx y hy hxy
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨a', ha', rfl⟩ := hy
    exact hT a ha a' ha' (fun hab => hxy (by rw [hab]))
  rcases h (fun i j => c (Fin.castLE hnm i) (Fin.castLE hnm j)) (fun x y => hsymm _ _) with
    ⟨T, hT, hm⟩ | ⟨T, hT, hm⟩
  · exact Or.inl ⟨_, by simpa using hT, key _ _ hm⟩
  · exact Or.inr ⟨_, by simpa using hT, key _ _ hm⟩

/-- **R(3,4) = 9**: nine is the least `n` such that every 2-colouring of the edges of `Kₙ`
contains a triangle in the first colour or a `K₄` in the second colour. -/
theorem ramsey_3_4 : IsLeast {n : ℕ | HasRamsey34 n} 9 := by
  refine ⟨ramsey34_nine, ?_⟩
  intro n hn
  by_contra hlt
  push_neg at hlt
  exact not_hasRamsey34_eight (hn.mono (by omega))

end Math

