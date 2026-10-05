import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

/-! ## Auxiliary counting lemmas -/

/-- Parity translated into `ZMod 2`. -/
lemma odd_iff_cast_zmod_two (m : ℕ) : Odd m ↔ (m : ZMod 2) = 1 := by
  rw [Nat.odd_iff, ← ZMod.natCast_mod m 2]
  constructor
  · intro h; rw [h]; norm_num
  · intro h
    have h2 : m % 2 = 0 ∨ m % 2 = 1 := by omega
    rcases h2 with h0 | h1
    · rw [h0] at h; simp at h
    · exact h1

/-- If `f` maps a finset `σ` onto `J` and `σ` has exactly one element more than `J`, then
exactly one fibre of `f` over `J` has two elements and all the others are singletons. -/
lemma fiber_structure {V α : Type*} [DecidableEq V] [DecidableEq α] (σ : Finset V) (f : V → α)
    (J : Finset α) (himg : σ.image f = J) (hcard : σ.card = J.card + 1) :
    ∃ j₀ ∈ J, (σ.filter (fun v => f v = j₀)).card = 2 ∧
      ∀ j ∈ J, j ≠ j₀ → (σ.filter (fun v => f v = j)).card = 1 := by
  classical
  set g : α → ℕ := fun j => (σ.filter (fun v => f v = j)).card with hg
  have hmem : ∀ v ∈ σ, f v ∈ J := by
    intro v hv; rw [← himg]; exact Finset.mem_image_of_mem f hv
  have hsum : σ.card = ∑ j ∈ J, g j := Finset.card_eq_sum_card_fiberwise hmem
  have hge : ∀ j ∈ J, 1 ≤ g j := by
    intro j hj
    rw [← himg] at hj
    obtain ⟨v, hv, hfv⟩ := Finset.mem_image.mp hj
    exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hfv⟩⟩
  have hsum' : ∑ j ∈ J, (g j - 1) = 1 := by
    have h2 : ∑ j ∈ J, g j = ∑ j ∈ J, ((g j - 1) + 1) := by
      refine Finset.sum_congr rfl ?_
      intro j hj; have := hge j hj; omega
    rw [Finset.sum_add_distrib] at h2
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h2
    omega
  have hex : ∃ j₀ ∈ J, g j₀ - 1 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    rw [Finset.sum_eq_zero hcon] at hsum'
    exact absurd hsum' (by norm_num)
  obtain ⟨j₀, hj₀, hne⟩ := hex
  have hsplit : (g j₀ - 1) + ∑ x ∈ J.erase j₀, (g x - 1) = ∑ j ∈ J, (g j - 1) :=
    Finset.add_sum_erase J (fun j => g j - 1) hj₀
  rw [hsum'] at hsplit
  have hgj₀ : g j₀ = 2 := by have := hge j₀ hj₀; omega
  refine ⟨j₀, hj₀, hgj₀, ?_⟩
  intro j hj hjne
  have hz : ∑ x ∈ J.erase j₀, (g x - 1) = 0 := by omega
  have h0 := (Finset.sum_eq_zero_iff.mp hz) j (Finset.mem_erase.mpr ⟨hjne, hj⟩)
  have := hge j hj
  show g j = 1
  omega

/-- If `f` is a bijection from `σ` onto `J` then exactly one vertex can be deleted from `σ`
so that the remaining colours are `J \ {i₀}`. -/
lemma erase_image_filter_card_of_image_eq {V α : Type*} [DecidableEq V] [DecidableEq α]
    (σ : Finset V) (f : V → α) (J : Finset α) (i₀ : α) (hi₀ : i₀ ∈ J)
    (hcard : σ.card = J.card) (hrb : σ.image f = J) :
    (σ.filter (fun v => (σ.erase v).image f = J.erase i₀)).card = 1 := by
  classical
  have hinj : Set.InjOn f σ := by
    apply Finset.injOn_of_card_image_eq
    rw [hrb, hcard]
  have hset : σ.filter (fun v => (σ.erase v).image f = J.erase i₀)
      = σ.filter (fun v => f v = i₀) := by
    apply Finset.filter_congr
    intro v hv
    constructor
    · intro h
      by_contra hne
      have hi : i₀ ∈ σ.image f := by rw [hrb]; exact hi₀
      obtain ⟨u, hu, hfu⟩ := Finset.mem_image.mp hi
      have huv : u ≠ v := by rintro rfl; exact hne hfu
      have h2 : i₀ ∈ (σ.erase v).image f :=
        Finset.mem_image.mpr ⟨u, Finset.mem_erase.mpr ⟨huv, hu⟩, hfu⟩
      rw [h] at h2
      exact (Finset.notMem_erase i₀ J) h2
    · intro h
      apply Finset.Subset.antisymm
      · intro j hj
        obtain ⟨w, hw, hfw⟩ := Finset.mem_image.mp hj
        obtain ⟨hwv, hwσ⟩ := Finset.mem_erase.mp hw
        subst hfw
        refine Finset.mem_erase.mpr ⟨?_, ?_⟩
        · rw [← h]; intro hc; exact hwv (hinj hwσ hv hc)
        · rw [← hrb]; exact Finset.mem_image_of_mem f hwσ
      · intro j hj
        obtain ⟨hjne, hjJ⟩ := Finset.mem_erase.mp hj
        rw [← hrb] at hjJ
        obtain ⟨u, hu, hfu⟩ := Finset.mem_image.mp hjJ
        refine Finset.mem_image.mpr ⟨u, Finset.mem_erase.mpr ⟨?_, hu⟩, hfu⟩
        rintro rfl
        exact hjne (by rw [← hfu, h])
  rw [hset, Finset.card_eq_one]
  have hi : i₀ ∈ σ.image f := by rw [hrb]; exact hi₀
  obtain ⟨v, hv, hfv⟩ := Finset.mem_image.mp hi
  refine ⟨v, Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hv, hfv⟩, ?_⟩⟩
  intro w hw
  obtain ⟨hwσ, hfw⟩ := Finset.mem_filter.mp hw
  exact hinj hwσ hv (by rw [hfw, hfv])

/-- If `f` does not map `σ` onto `J`, the number of vertices that can be deleted from `σ`
so that the remaining colours are `J \ {i₀}` is even (in fact `0` or `2`). -/
lemma erase_image_filter_card_even {V α : Type*} [DecidableEq V] [DecidableEq α]
    (σ : Finset V) (f : V → α) (J : Finset α) (i₀ : α) (hi₀ : i₀ ∈ J)
    (hcard : σ.card = J.card) (hsub : σ.image f ⊆ J) (hne : σ.image f ≠ J) :
    Even (σ.filter (fun v => (σ.erase v).image f = J.erase i₀)).card := by
  classical
  by_cases hcase : σ.image f = J.erase i₀
  · have hJc : J.card = (J.erase i₀).card + 1 := by
      rw [Finset.card_erase_of_mem hi₀]
      have := Finset.card_pos.mpr ⟨i₀, hi₀⟩
      omega
    obtain ⟨j₀, hj₀J, hj₀card, hother⟩ :=
      fiber_structure σ f (J.erase i₀) hcase (by rw [hcard, hJc])
    have hset : σ.filter (fun v => (σ.erase v).image f = J.erase i₀)
        = σ.filter (fun v => f v = j₀) := by
      apply Finset.filter_congr
      intro v hv
      constructor
      · intro h
        by_contra hvj
        have hfv : f v ∈ J.erase i₀ := by rw [← hcase]; exact Finset.mem_image_of_mem f hv
        have h1 := hother (f v) hfv hvj
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
        have hva : v ∈ σ.filter (fun w => f w = f v) := Finset.mem_filter.mpr ⟨hv, rfl⟩
        rw [ha, Finset.mem_singleton] at hva
        have hfv2 : f v ∈ (σ.erase v).image f := by rw [h]; exact hfv
        obtain ⟨w, hw, hfw⟩ := Finset.mem_image.mp hfv2
        obtain ⟨hwv, hwσ⟩ := Finset.mem_erase.mp hw
        have hwa : w ∈ σ.filter (fun u => f u = f v) := Finset.mem_filter.mpr ⟨hwσ, hfw⟩
        rw [ha, Finset.mem_singleton] at hwa
        exact hwv (hwa.trans hva.symm)
      · intro h
        obtain ⟨w, hwf, hwv⟩ := Finset.exists_mem_ne (s := σ.filter (fun w => f w = j₀))
          (by rw [hj₀card]; norm_num) v
        obtain ⟨hwσ, hfw⟩ := Finset.mem_filter.mp hwf
        apply Finset.Subset.antisymm
        · intro j hj
          obtain ⟨u, hu, hfu⟩ := Finset.mem_image.mp hj
          rw [← hcase]
          exact Finset.mem_image.mpr ⟨u, (Finset.mem_erase.mp hu).2, hfu⟩
        · intro j hj
          rw [← hcase] at hj
          obtain ⟨u, hu, hfu⟩ := Finset.mem_image.mp hj
          by_cases huv : u = v
          · subst huv
            exact Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hwv, hwσ⟩,
              by rw [hfw, ← h, hfu]⟩
          · exact Finset.mem_image.mpr ⟨u, Finset.mem_erase.mpr ⟨huv, hu⟩, hfu⟩
    rw [hset, hj₀card]
    exact even_two
  · have hempty : σ.filter (fun v => (σ.erase v).image f = J.erase i₀) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v hv h
      have h1 : J.erase i₀ ⊆ σ.image f := by
        rw [← h]
        exact Finset.image_subset_image (Finset.erase_subset v σ)
      by_cases hi : i₀ ∈ σ.image f
      · exact hne (Finset.Subset.antisymm hsub (by
          intro j hj
          by_cases hji : j = i₀
          · subst hji; exact hi
          · exact h1 (Finset.mem_erase.mpr ⟨hji, hj⟩)))
      · exact hcase (Finset.Subset.antisymm (by
          intro j hj
          exact Finset.mem_erase.mpr ⟨by rintro rfl; exact hi hj, hsub hj⟩) h1)
    rw [hempty]
    simp

/-! ## The combinatorial setting -/

section Sperner

variable {n : ℕ} {V : Type*} [DecidableEq V]
  (carrier : V → Finset (Fin (n + 1))) (T : Finset (Finset V)) (c : V → Fin (n + 1))

/-- The top-dimensional cells of the sub-triangulation carried by the face `F J` of the
big simplex: faces of the triangulation `T` all of whose vertices are carried inside `J`
and which have the full dimension `|J| - 1` of that face. -/
def spernerCells (J : Finset (Fin (n + 1))) : Finset (Finset V) :=
  T.filter (fun σ => σ.card = J.card ∧ ∀ v ∈ σ, carrier v ⊆ J)

/-- The *rainbow* cells of the face `F J`: cells of `F J` whose vertices receive all the
colours of `J` (equivalently, exactly one vertex of each colour in `J`). -/
def spernerRainbow (J : Finset (Fin (n + 1))) : Finset (Finset V) :=
  (spernerCells carrier T J).filter (fun σ => σ.image c = J)

/-- The *doors* of the face `F J` relative to a distinguished colour `i₀ ∈ J`:
codimension-one faces inside `F J` whose colours are exactly `J \ {i₀}`. -/
def spernerDoors (J : Finset (Fin (n + 1))) (i₀ : Fin (n + 1)) : Finset (Finset V) :=
  T.filter (fun τ => τ.card + 1 = J.card ∧ (∀ v ∈ τ, carrier v ⊆ J) ∧ τ.image c = J.erase i₀)

variable
  (hdown : ∀ σ ∈ T, ∀ τ ⊆ σ, τ ∈ T)
  (hT0 : (∅ : Finset V) ∈ T)
  (hpm : ∀ (J : Finset (Fin (n + 1))) (τ : Finset V), τ ∈ T → τ.card + 1 = J.card →
      (∀ v ∈ τ, carrier v ⊆ J) →
      ((spernerCells carrier T J).filter (fun σ => τ ⊆ σ)).card
        = if τ.biUnion carrier = J then 2 else 1)
  (hc : ∀ v, c v ∈ carrier v)

omit [DecidableEq V] in
include hc in
/-- Colours of a cell of `F J` lie in `J`. -/
lemma spernerCells_image_subset {J : Finset (Fin (n + 1))} {σ : Finset V}
    (hσ : σ ∈ spernerCells carrier T J) : σ.image c ⊆ J := by
  intro j hj
  obtain ⟨v, hv, hfv⟩ := Finset.mem_image.mp hj
  obtain ⟨-, -, hcar⟩ := Finset.mem_filter.mp hσ
  exact hcar v hv (hfv ▸ hc v)

include hdown in
/-- The doors contained in a fixed cell `σ` are exactly the vertex-deletions of `σ` leaving
the colours `J \ {i₀}`. -/
lemma spernerDoors_in_cell_card_eq {J : Finset (Fin (n + 1))} {i₀ : Fin (n + 1)}
    {σ : Finset V} (hσ : σ ∈ spernerCells carrier T J) :
    ((spernerDoors carrier T c J i₀).filter (fun τ => τ ⊆ σ)).card
      = (σ.filter (fun v => (σ.erase v).image c = J.erase i₀)).card := by
  classical
  obtain ⟨hσT, hσcard, hσcar⟩ := Finset.mem_filter.mp hσ
  have hset : (spernerDoors carrier T c J i₀).filter (fun τ => τ ⊆ σ)
      = (σ.filter (fun v => (σ.erase v).image c = J.erase i₀)).image (fun v => σ.erase v) := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_image, spernerDoors]
    constructor
    · rintro ⟨⟨hτT, hτcard, hτcar, hτimg⟩, hτσ⟩
      have hcards : τ.card + 1 = σ.card := by omega
      have hss : τ ⊂ σ := Finset.ssubset_iff_of_subset hτσ |>.mpr (by
        by_contra hcon
        push_neg at hcon
        have : σ ⊆ τ := fun x hx => by
          by_contra hxt
          exact hxt (hcon x hx)
        have := Finset.card_le_card this
        omega)
      obtain ⟨v, hvσ, hvτ⟩ := Finset.exists_of_ssubset hss
      have hτe : τ = σ.erase v := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          exact Finset.mem_erase.mpr ⟨by rintro rfl; exact hvτ hx, hτσ hx⟩
        · rw [Finset.card_erase_of_mem hvσ]; omega
      exact ⟨v, ⟨hvσ, by rw [← hτe]; exact hτimg⟩, hτe.symm⟩
    · rintro ⟨v, ⟨hvσ, hvimg⟩, rfl⟩
      refine ⟨⟨hdown σ hσT _ (Finset.erase_subset v σ), ?_, ?_, hvimg⟩,
        Finset.erase_subset v σ⟩
      · rw [Finset.card_erase_of_mem hvσ, ← hσcard]
        have := Finset.card_pos.mpr ⟨v, hvσ⟩
        omega
      · intro w hw; exact hσcar w (Finset.mem_of_mem_erase hw)
  rw [hset]
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
  by_contra hne
  have hab' : σ.erase a = σ.erase b := hab
  have hmem : a ∈ σ.erase b := Finset.mem_erase.mpr ⟨hne, ha.1⟩
  rw [← hab'] at hmem
  exact (Finset.notMem_erase a σ) hmem

include hdown hc in
/-- For a cell of `F J`, the number of doors it contains is `1` if the cell is rainbow and
even otherwise. -/
lemma spernerDoors_in_cell_card {J : Finset (Fin (n + 1))} {i₀ : Fin (n + 1)} (hi₀ : i₀ ∈ J)
    {σ : Finset V} (hσ : σ ∈ spernerCells carrier T J) :
    (((spernerDoors carrier T c J i₀).filter (fun τ => τ ⊆ σ)).card : ZMod 2)
      = if σ.image c = J then 1 else 0 := by
  classical
  obtain ⟨hσT, hσcard, hσcar⟩ := Finset.mem_filter.mp hσ
  rw [spernerDoors_in_cell_card_eq carrier T c hdown hσ]
  by_cases hrb : σ.image c = J
  · rw [if_pos hrb, erase_image_filter_card_of_image_eq σ c J i₀ hi₀ hσcard hrb]
    norm_num
  · rw [if_neg hrb]
    obtain ⟨m, hm⟩ := erase_image_filter_card_even σ c J i₀ hi₀ hσcard
      (spernerCells_image_subset carrier T c hc hσ) hrb
    rw [hm]
    push_cast
    ring_nf
    rw [show ((2 : ZMod 2)) = 0 by decide]
    ring

include hpm hc in
/-- For a door of `F J`, the number of cells of `F J` containing it is `1` if the door lies
in the sub-face `J \ {i₀}` (i.e. it is a rainbow cell of that sub-face) and `2` otherwise. -/
lemma spernerCells_over_door_card {J : Finset (Fin (n + 1))} {i₀ : Fin (n + 1)} (hi₀ : i₀ ∈ J)
    {τ : Finset V} (hτ : τ ∈ spernerDoors carrier T c J i₀) :
    (((spernerCells carrier T J).filter (fun σ => τ ⊆ σ)).card : ZMod 2)
      = if τ ∈ spernerRainbow carrier T c (J.erase i₀) then 1 else 0 := by
  classical
  obtain ⟨hτT, hτcard, hτcar, hτimg⟩ := Finset.mem_filter.mp hτ
  rw [hpm J τ hτT hτcard hτcar]
  -- `J.erase i₀ ⊆ τ.biUnion carrier ⊆ J`
  have hlow : J.erase i₀ ⊆ τ.biUnion carrier := by
    rw [← hτimg]
    intro j hj
    obtain ⟨v, hv, hfv⟩ := Finset.mem_image.mp hj
    exact Finset.mem_biUnion.mpr ⟨v, hv, hfv ▸ hc v⟩
  have hhigh : τ.biUnion carrier ⊆ J := by
    intro j hj
    obtain ⟨v, hv, hjv⟩ := Finset.mem_biUnion.mp hj
    exact hτcar v hv hjv
  have hmemiff : τ ∈ spernerRainbow carrier T c (J.erase i₀) ↔ τ.biUnion carrier ≠ J := by
    constructor
    · intro hmem hcon
      obtain ⟨hmc, -⟩ := Finset.mem_filter.mp hmem
      obtain ⟨-, -, hcar'⟩ := Finset.mem_filter.mp hmc
      have : i₀ ∈ τ.biUnion carrier := by rw [hcon]; exact hi₀
      obtain ⟨v, hv, hiv⟩ := Finset.mem_biUnion.mp this
      exact (Finset.notMem_erase i₀ J) (hcar' v hv hiv)
    · intro hne
      have hi₀not : i₀ ∉ τ.biUnion carrier := by
        intro hcon
        apply hne
        apply Finset.Subset.antisymm hhigh
        intro j hj
        by_cases hji : j = i₀
        · subst hji; exact hcon
        · exact hlow (Finset.mem_erase.mpr ⟨hji, hj⟩)
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hτT, ?_, ?_⟩, hτimg⟩
      · rw [Finset.card_erase_of_mem hi₀]; omega
      · intro v hv j hj
        refine Finset.mem_erase.mpr ⟨?_, hτcar v hv hj⟩
        rintro rfl
        exact hi₀not (Finset.mem_biUnion.mpr ⟨v, hv, hj⟩)
  by_cases hb : τ.biUnion carrier = J
  · rw [if_pos hb, if_neg (by rw [hmemiff]; simpa using hb)]
    decide
  · rw [if_neg hb, if_pos (hmemiff.mpr hb)]
    norm_num

include hdown hT0 hpm hc in
/-- **Key induction.** Every nonempty face of the big simplex carries an odd number of
rainbow cells. -/
theorem spernerRainbow_card_odd (k : ℕ) :
    ∀ J : Finset (Fin (n + 1)), J.card = k + 1 → Odd (spernerRainbow carrier T c J).card := by
  classical
  induction k with
  | zero =>
    intro J hJ
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hJ
    have hcount := hpm {i} ∅ hT0 (by simp) (by simp)
    rw [Finset.filter_true_of_mem (fun σ _ => Finset.empty_subset σ)] at hcount
    rw [if_neg (by simp)] at hcount
    have hrb : spernerRainbow carrier T c {i} = spernerCells carrier T {i} := by
      apply Finset.filter_true_of_mem
      intro σ hσ
      obtain ⟨-, hcard, hcar⟩ := Finset.mem_filter.mp hσ
      simp only [Finset.card_singleton] at hcard
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
      have : c v = i := by
        have := hcar v (Finset.mem_singleton_self v) (hc v)
        simpa using this
      simp [this]
    rw [hrb, hcount]
    exact odd_one
  | succ k ih =>
    intro J hJ
    have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i₀, hi₀⟩ := hJne
    set Cells := spernerCells carrier T J with hCells
    set Doors := spernerDoors carrier T c J i₀ with hDoors
    -- double counting of incident (cell, door) pairs
    have hdc : ∑ σ ∈ Cells, (Doors.filter (fun τ => τ ⊆ σ)).card
        = ∑ τ ∈ Doors, (Cells.filter (fun σ => τ ⊆ σ)).card := by
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    have hcast := congrArg (fun m : ℕ => (m : ZMod 2)) hdc
    simp only [Nat.cast_sum] at hcast
    -- left-hand side counts rainbow cells of `J`
    have hL : ∑ σ ∈ Cells, ((Doors.filter (fun τ => τ ⊆ σ)).card : ZMod 2)
        = ((spernerRainbow carrier T c J).card : ZMod 2) := by
      rw [Finset.sum_congr rfl (fun σ hσ =>
        spernerDoors_in_cell_card carrier T c hdown hc hi₀ hσ)]
      rw [spernerRainbow, Finset.card_filter, Nat.cast_sum]
      exact Finset.sum_congr rfl (fun σ _ => by split <;> simp)
    -- right-hand side counts rainbow cells of `J \ {i₀}`
    have hsub : spernerRainbow carrier T c (J.erase i₀) ⊆ Doors := by
      intro τ hτ
      obtain ⟨hmc, himg⟩ := Finset.mem_filter.mp hτ
      obtain ⟨hτT, hcard, hcar⟩ := Finset.mem_filter.mp hmc
      refine Finset.mem_filter.mpr ⟨hτT, ?_, ?_, himg⟩
      · rw [hcard, Finset.card_erase_of_mem hi₀]
        have := Finset.card_pos.mpr ⟨i₀, hi₀⟩
        omega
      · intro v hv
        exact (hcar v hv).trans (Finset.erase_subset i₀ J)
    have hR : ∑ τ ∈ Doors, ((Cells.filter (fun σ => τ ⊆ σ)).card : ZMod 2)
        = ((spernerRainbow carrier T c (J.erase i₀)).card : ZMod 2) := by
      rw [Finset.sum_congr rfl (fun τ hτ =>
        spernerCells_over_door_card carrier T c hpm hc hi₀ hτ)]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.mpr hsub]
      simp
    rw [odd_iff_cast_zmod_two]
    rw [← hL, hcast, hR, ← odd_iff_cast_zmod_two]
    exact ih (J.erase i₀) (by rw [Finset.card_erase_of_mem hi₀]; omega)

include hdown hT0 hpm hc in
/-- **Sperner's lemma.** Let `T` be a triangulation of the `n`-simplex, described
combinatorially: `T` is a finite simplicial complex on a vertex set `V` (closed under
passing to subfaces, and containing the empty face), each vertex `v` carries a nonempty
*carrier* `carrier v ⊆ Fin (n+1)` — the minimal face of the big simplex containing it —
and `T` satisfies the pseudomanifold condition `hpm`: inside each face `F J` of the big
simplex, every codimension-one face `τ` of the induced triangulation is contained in
exactly two full-dimensional cells of `F J` if it is interior to `F J` (that is, the
carriers of its vertices jointly cover `J`), and in exactly one otherwise.

Then for every *Sperner colouring* `c` — a colouring of the vertices with `c v ∈ carrier v`
— the number of rainbow cells, i.e. full-dimensional cells of the triangulation receiving
all `n + 1` colours, is odd. -/
theorem sperner_lemma : Odd (spernerRainbow carrier T c Finset.univ).card :=
  spernerRainbow_card_odd carrier T c hdown hT0 hpm hc n Finset.univ (by simp)

end Sperner

/-! ## Non-vacuity: the hypotheses of `sperner_lemma` are satisfiable

Two instances are provided: the trivial (unsubdivided) triangulation of the `n`-simplex in
every dimension, and a genuinely subdivided one-dimensional triangulation, in which the
`2` branch of the pseudomanifold condition really occurs. -/

namespace TrivialTriangulation

variable (n : ℕ)

/-- The vertices of the unsubdivided `n`-simplex, each carried by its own vertex face. -/
def carrier : Fin (n + 1) → Finset (Fin (n + 1)) := fun i => {i}

/-- The full simplex: all subsets of `Fin (n+1)` are faces. -/
def cplx : Finset (Finset (Fin (n + 1))) := Finset.univ

lemma cells_eq (J : Finset (Fin (n + 1))) :
    spernerCells (carrier n) (cplx n) J = {J} := by
  ext σ
  simp only [spernerCells, cplx, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, carrier, Finset.singleton_subset_iff]
  constructor
  · rintro ⟨hcard, hsub⟩
    exact Finset.eq_of_subset_of_card_le hsub hcard.ge
  · rintro rfl
    exact ⟨rfl, fun v hv => hv⟩

lemma down : ∀ σ ∈ cplx n, ∀ τ ⊆ σ, τ ∈ cplx n := by
  intro σ _ τ _; exact Finset.mem_univ τ

lemma empty_mem : (∅ : Finset (Fin (n + 1))) ∈ cplx n := Finset.mem_univ _

lemma pseudomanifold : ∀ (J : Finset (Fin (n + 1))) (τ : Finset (Fin (n + 1))),
    τ ∈ cplx n → τ.card + 1 = J.card → (∀ v ∈ τ, carrier n v ⊆ J) →
    ((spernerCells (carrier n) (cplx n) J).filter (fun σ => τ ⊆ σ)).card
      = if τ.biUnion (carrier n) = J then 2 else 1 := by
  intro J τ _ hcard hcar
  simp only [carrier, Finset.singleton_subset_iff] at hcar
  have hτJ : τ ⊆ J := fun v hv => hcar v hv
  have hbi : τ.biUnion (carrier n) = τ := by
    ext j; simp [carrier]
  rw [cells_eq, hbi, if_neg (by rintro rfl; omega)]
  rw [Finset.filter_singleton, if_pos hτJ, Finset.card_singleton]

/-- The colouring of the unsubdivided simplex is forced, and there is exactly one rainbow
cell, in agreement with `Math.sperner_lemma`. -/
lemma rainbow_card (c : Fin (n + 1) → Fin (n + 1)) (hc : ∀ v, c v ∈ carrier n v) :
    (spernerRainbow (carrier n) (cplx n) c Finset.univ).card = 1 := by
  have hcid : ∀ v, c v = v := by
    intro v; simpa [carrier] using hc v
  rw [spernerRainbow, cells_eq, Finset.filter_singleton, if_pos]
  · exact Finset.card_singleton _
  · ext j; simp [Finset.mem_image, hcid]

example : Odd (spernerRainbow (carrier n) (cplx n) id Finset.univ).card :=
  sperner_lemma (carrier n) (cplx n) id (down n) (empty_mem n) (pseudomanifold n)
    (fun v => Finset.mem_singleton_self v)

end TrivialTriangulation

namespace SubdividedInterval

/-- A subdivided segment: three vertices `0 < 1 < 2`, the middle one being interior. -/
def carrier : Fin 3 → Finset (Fin 2) := ![{0}, {0, 1}, {1}]

/-- The two edges of the subdivided segment together with all their subfaces. -/
def cplx : Finset (Finset (Fin 3)) := {∅, {0}, {1}, {2}, {0, 1}, {1, 2}}

/-- A Sperner colouring of the subdivided segment. -/
def col : Fin 3 → Fin 2 := ![0, 1, 1]

lemma down : ∀ σ ∈ cplx, ∀ τ ⊆ σ, τ ∈ cplx := by decide

lemma empty_mem : (∅ : Finset (Fin 3)) ∈ cplx := by decide

lemma sperner_col : ∀ v, col v ∈ carrier v := by decide

lemma pseudomanifold : ∀ (J : Finset (Fin 2)) (τ : Finset (Fin 3)),
    τ ∈ cplx → τ.card + 1 = J.card → (∀ v ∈ τ, carrier v ⊆ J) →
    ((spernerCells carrier cplx J).filter (fun σ => τ ⊆ σ)).card
      = if τ.biUnion carrier = J then 2 else 1 := by decide

/-- Here the `2` branch of the pseudomanifold condition really occurs: the interior
vertex `1` is a face of both edges. -/
lemma two_branch_occurs :
    ((spernerCells carrier cplx {0, 1}).filter (fun σ => ({1} : Finset (Fin 3)) ⊆ σ)).card
      = 2 := by decide

example : Odd (spernerRainbow carrier cplx col Finset.univ).card :=
  sperner_lemma carrier cplx col down empty_mem pseudomanifold sperner_col

/-- Exactly one of the two edges is rainbow. -/
lemma rainbow_card : (spernerRainbow carrier cplx col Finset.univ).card = 1 := by decide

end SubdividedInterval

end Math

