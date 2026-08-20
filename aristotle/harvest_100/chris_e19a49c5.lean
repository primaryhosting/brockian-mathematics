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

open Finset

/-!
## Combinatorial data of a triangulated simplex with a Sperner colouring

We formalise a triangulated `n`-simplex combinatorially.  The vertices of the big simplex are
indexed by `Fin (n+1)`; a face of the big simplex is a nonempty `S : Finset (Fin (n+1))`.
The triangulation assigns to each such face `S` the finite set `cells S` of top-dimensional
simplices of the induced triangulation of the face `S`; a cell is a set of `|S|` vertices taken
from an ambient vertex set `V`.

`label : V → Fin (n+1)` is the colouring, and the Sperner condition is `label_mem`: a vertex
used in the triangulation of the face `S` receives a colour belonging to `S`.

`pseudomanifold` is the standard combinatorial property of a triangulation of a simplex: a
codimension-one face `F` of a cell of `S` lies in exactly two cells of `S`, unless it lies on the
boundary of `S` (that is, it is itself a cell of a proper face `T` of `S`), in which case it lies
in exactly one cell of `S`.
-/

/-- A combinatorial triangulated `n`-simplex, with a Sperner colouring, on the vertex set `V`. -/
structure SpernerTriangulation (n : ℕ) (V : Type*) [DecidableEq V] where
  /-- `cells S` are the top-dimensional simplices of the triangulation of the face `S`. -/
  cells : Finset (Fin (n + 1)) → Finset (Finset V)
  /-- The Sperner colouring of the vertices used by the triangulation. -/
  label : V → Fin (n + 1)
  /-- A cell of the triangulation of the face `S` has exactly `|S|` vertices. -/
  card_cell : ∀ S : Finset (Fin (n + 1)), ∀ C ∈ cells S, C.card = S.card
  /-- Sperner's condition: a vertex lying in the face `S` is coloured by a colour of `S`. -/
  label_mem : ∀ S : Finset (Fin (n + 1)), ∀ C ∈ cells S, ∀ v ∈ C, label v ∈ S
  /-- A vertex of the big simplex is triangulated by exactly one `0`-cell. -/
  vertex_cell : ∀ i : Fin (n + 1), (cells {i}).card = 1
  /-- The pseudomanifold property: an interior codimension-one face lies in exactly two cells,
  a boundary one in exactly one cell. -/
  pseudomanifold : ∀ S : Finset (Fin (n + 1)), 1 < S.card → ∀ F : Finset V,
      F.card + 1 = S.card → (∃ C ∈ cells S, F ⊆ C) →
      ((cells S).filter (fun C => F ⊆ C)).card = if ∃ T ⊂ S, F ∈ cells T then 1 else 2
  /-- A cell of a proper face of `S` is contained in some cell of `S`. -/
  face_subset : ∀ S T : Finset (Fin (n + 1)), T ⊂ S → ∀ F ∈ cells T, ∃ C ∈ cells S, F ⊆ C

namespace SpernerTriangulation

variable {n : ℕ} {V : Type*} [DecidableEq V]

/-- The rainbow ("fully coloured") cells of the triangulation of the face `S`: those cells whose
vertices realise all the colours of `S`. -/
def rainbow (t : SpernerTriangulation n V) (S : Finset (Fin (n + 1))) : Finset (Finset V) :=
  (t.cells S).filter (fun C => C.image t.label = S)

end SpernerTriangulation

/-! ## Counting the doors of a single cell

Fix a face `S` and a colour `i₀ ∈ S`.  A *door* of a cell `C` is a codimension-one face of `C`
whose set of colours is exactly `S.erase i₀`.  We show that a cell has one door if it is rainbow,
two doors if its colour set is exactly `S.erase i₀`, and no door otherwise.
-/

section Doors

variable {n : ℕ} {V : Type*} [DecidableEq V]

/-- The codimension-one faces of a cell `C` are exactly the sets `C.erase v` for `v ∈ C`. -/
lemma card_doors_eq (label : V → Fin (n + 1)) (C : Finset V) (k : ℕ) (hC : C.card = k + 1)
    (S' : Finset (Fin (n + 1))) :
    ((C.powersetCard k).filter (fun F => F.image label = S')).card
      = (C.filter (fun v => (C.erase v).image label = S')).card := by
  refine (Finset.card_bij (fun v _ => C.erase v) ?_ ?_ ?_).symm
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hv ⊢
    refine ⟨⟨Finset.erase_subset _ _, ?_⟩, hv.2⟩
    rw [Finset.card_erase_of_mem hv.1, hC]
    omega
  · intro v hv w hw h
    have h' : C.erase v = C.erase w := h
    simp only [Finset.mem_filter] at hv hw
    by_contra hne
    have hmem : v ∈ C.erase w := Finset.mem_erase.2 ⟨hne, hv.1⟩
    rw [← h'] at hmem
    exact (Finset.notMem_erase v C) hmem
  · intro F hF
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hF
    obtain ⟨⟨hFC, hFcard⟩, hFimg⟩ := hF
    have hss : F ⊂ C :=
      Finset.ssubset_iff_subset_ne.2 ⟨hFC, by intro h; rw [h, hC] at hFcard; omega⟩
    obtain ⟨v, hvC, hvF⟩ := Finset.exists_of_ssubset hss
    have hFe : F = C.erase v := by
      refine Finset.eq_of_subset_of_card_le (fun x hx => Finset.mem_erase.2 ⟨?_, hFC hx⟩) ?_
      · rintro rfl; exact hvF hx
      · rw [Finset.card_erase_of_mem hvC, hC, hFcard]
        omega
    refine ⟨v, ?_, hFe.symm⟩
    simp only [Finset.mem_filter]
    exact ⟨hvC, by rw [← hFe]; exact hFimg⟩

/-- A rainbow cell has exactly one door. -/
lemma card_erase_doors_of_image_eq (label : V → Fin (n + 1)) (C : Finset V)
    (S : Finset (Fin (n + 1))) (i₀ : Fin (n + 1)) (hi₀ : i₀ ∈ S) (hcard : C.card = S.card)
    (himg : C.image label = S) :
    (C.filter (fun v => (C.erase v).image label = S.erase i₀)).card = 1 := by
  have hinj : Set.InjOn label (C : Set V) := by
    apply Finset.injOn_of_card_image_eq
    rw [himg, hcard]
  obtain ⟨u, huC, hu⟩ : ∃ u ∈ C, label u = i₀ := by
    have : i₀ ∈ C.image label := by rw [himg]; exact hi₀
    simpa [Finset.mem_image] using this
  have hset : C.filter (fun v => (C.erase v).image label = S.erase i₀) = {u} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hvC, hv⟩
      by_contra hne
      have hne' : u ≠ v := fun h => hne h.symm
      have hmem : i₀ ∈ (C.erase v).image label :=
        Finset.mem_image.2 ⟨u, Finset.mem_erase.2 ⟨hne', huC⟩, hu⟩
      rw [hv] at hmem
      exact (Finset.notMem_erase i₀ S) hmem
    · rintro rfl
      refine ⟨huC, ?_⟩
      ext j
      simp only [Finset.mem_image, Finset.mem_erase]
      constructor
      · rintro ⟨w, ⟨hwu, hwC⟩, rfl⟩
        refine ⟨fun hcon => hwu (hinj hwC huC (by rw [hcon, hu])), ?_⟩
        rw [← himg]; exact Finset.mem_image.2 ⟨w, hwC, rfl⟩
      · rintro ⟨hj, hjS⟩
        rw [← himg] at hjS
        obtain ⟨w, hwC, rfl⟩ := Finset.mem_image.1 hjS
        exact ⟨w, ⟨fun h => hj (by rw [h, hu]), hwC⟩, rfl⟩
  rw [hset, Finset.card_singleton]

/-- A cell whose colour set is exactly `S.erase i₀` has exactly two doors. -/
lemma card_erase_doors_of_image_eq_erase (label : V → Fin (n + 1)) (C : Finset V)
    (S : Finset (Fin (n + 1))) (i₀ : Fin (n + 1)) (hi₀ : i₀ ∈ S) (hcard : C.card = S.card)
    (himg : C.image label = S.erase i₀) :
    (C.filter (fun v => (C.erase v).image label = S.erase i₀)).card = 2 := by
  set S' := S.erase i₀ with hS'
  have hS'card : S'.card + 1 = C.card := by
    rw [hS', Finset.card_erase_of_mem hi₀, hcard]
    have : 1 ≤ S.card := Finset.card_pos.2 ⟨i₀, hi₀⟩
    omega
  set fib : Fin (n + 1) → Finset V := fun j => C.filter (fun w => label w = j) with hfib
  have hmaps : Set.MapsTo label (C : Set V) (S' : Set (Fin (n + 1))) := by
    intro v hv
    rw [← himg]
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨v, hv, rfl⟩)
  have hsum : C.card = ∑ j ∈ S', (fib j).card := Finset.card_eq_sum_card_fiberwise hmaps
  have hone : ∀ j ∈ S', 1 ≤ (fib j).card := by
    intro j hj
    rw [← himg] at hj
    obtain ⟨w, hwC, hw⟩ := Finset.mem_image.1 hj
    exact Finset.card_pos.2 ⟨w, Finset.mem_filter.2 ⟨hwC, hw⟩⟩
  obtain ⟨j₀, hj₀S, hj₀⟩ : ∃ j ∈ S', 2 ≤ (fib j).card := by
    by_contra hcon
    push_neg at hcon
    have hall : ∑ j ∈ S', (fib j).card = ∑ j ∈ S', 1 := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have := hone j hj
      have := hcon j hj
      omega
    rw [hall, Finset.sum_const, smul_eq_mul, mul_one] at hsum
    omega
  have hg : ∀ j ∈ S', (if j = j₀ then 2 else 1) = (fib j).card := by
    refine (Finset.sum_eq_sum_iff_of_le ?_).1 ?_
    · intro j hj
      by_cases h : j = j₀
      · subst h; rw [if_pos rfl]; exact hj₀
      · rw [if_neg h]; exact hone j hj
    · rw [← hsum, ← hS'card]
      have hsplit : ∑ j ∈ S', (if j = j₀ then 2 else 1)
          = ∑ j ∈ S', (1 + if j = j₀ then 1 else 0) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        by_cases h : j = j₀ <;> simp [h]
      rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.sum_ite_eq' S' j₀ (fun _ => 1), if_pos hj₀S]
  have hfibj₀ : (fib j₀).card = 2 := by
    have := hg j₀ hj₀S
    rw [if_pos rfl] at this
    exact this.symm
  have hset : C.filter (fun v => (C.erase v).image label = S') = fib j₀ := by
    ext v
    simp only [hfib, Finset.mem_filter]
    constructor
    · rintro ⟨hvC, hv⟩
      refine ⟨hvC, ?_⟩
      by_contra hne
      have hlv : label v ∈ S' := hmaps hvC
      have h1 : (fib (label v)).card = 1 := by
        have := hg (label v) hlv
        rw [if_neg hne] at this
        exact this.symm
      have hmem : label v ∈ (C.erase v).image label := by rw [hv]; exact hlv
      obtain ⟨w, hwe, hw⟩ := Finset.mem_image.1 hmem
      obtain ⟨hwv, hwC⟩ := Finset.mem_erase.1 hwe
      have h2 : ({v, w} : Finset V) ⊆ fib (label v) := by
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact Finset.mem_filter.2 ⟨hvC, rfl⟩
        · rw [Finset.mem_singleton] at hx
          subst hx
          exact Finset.mem_filter.2 ⟨hwC, hw⟩
      have h3 := Finset.card_le_card h2
      rw [h1, Finset.card_insert_of_notMem (by simp [Ne.symm hwv]), Finset.card_singleton] at h3
      omega
    · rintro ⟨hvC, hvlab⟩
      refine ⟨hvC, ?_⟩
      obtain ⟨w, hwfib, hwv⟩ :=
        Finset.exists_mem_ne (by rw [hfibj₀]; norm_num : 1 < (fib j₀).card) v
      obtain ⟨hwC, hw⟩ := Finset.mem_filter.1 hwfib
      apply Finset.Subset.antisymm
      · intro j hj
        obtain ⟨x, hxe, rfl⟩ := Finset.mem_image.1 hj
        exact hmaps (Finset.mem_erase.1 hxe).2
      · intro j hj
        rw [← himg] at hj
        obtain ⟨x, hxC, rfl⟩ := Finset.mem_image.1 hj
        by_cases hxv : x = v
        · subst hxv
          exact Finset.mem_image.2 ⟨w, Finset.mem_erase.2 ⟨hwv, hwC⟩, by rw [hw, hvlab]⟩
        · exact Finset.mem_image.2 ⟨x, Finset.mem_erase.2 ⟨hxv, hxC⟩, rfl⟩
  rw [hset, hfibj₀]

/-- Any other cell has no door. -/
lemma card_erase_doors_of_other (label : V → Fin (n + 1)) (C : Finset V)
    (S : Finset (Fin (n + 1))) (i₀ : Fin (n + 1)) (hi₀ : i₀ ∈ S)
    (hsub : C.image label ⊆ S) (h₁ : C.image label ≠ S) (h₂ : C.image label ≠ S.erase i₀) :
    (C.filter (fun v => (C.erase v).image label = S.erase i₀)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v _ hcon
  apply h₂
  have h3 : S.erase i₀ ⊆ C.image label := by
    rw [← hcon]; exact Finset.image_subset_image (Finset.erase_subset _ _)
  refine (Finset.eq_of_subset_of_card_le h3 ?_).symm
  have h4 : (C.image label).card < S.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, h₁⟩)
  have h5 : (S.erase i₀).card = S.card - 1 := Finset.card_erase_of_mem hi₀
  omega

/-- The door count of a single cell, in the three possible cases. -/
lemma card_doors_cell (label : V → Fin (n + 1)) (C : Finset V) (S : Finset (Fin (n + 1)))
    (i₀ : Fin (n + 1)) (hi₀ : i₀ ∈ S) (k : ℕ) (hk : S.card = k + 1) (hcard : C.card = S.card)
    (hsub : C.image label ⊆ S) :
    ((C.powersetCard k).filter (fun F => F.image label = S.erase i₀)).card
      = (if C.image label = S then 1 else 0)
        + 2 * (if C.image label = S.erase i₀ then 1 else 0) := by
  rw [card_doors_eq label C k (by rw [hcard, hk]) (S.erase i₀)]
  by_cases h₁ : C.image label = S
  · rw [if_pos h₁, if_neg (by rw [h₁]; exact fun h => (Finset.notMem_erase i₀ S) (h ▸ hi₀))]
    rw [card_erase_doors_of_image_eq label C S i₀ hi₀ hcard h₁]
  · by_cases h₂ : C.image label = S.erase i₀
    · rw [if_neg h₁, if_pos h₂]
      rw [card_erase_doors_of_image_eq_erase label C S i₀ hi₀ hcard h₂]
    · rw [if_neg h₁, if_neg h₂]
      rw [card_erase_doors_of_other label C S i₀ hi₀ hsub h₁ h₂]

end Doors

namespace SpernerTriangulation

variable {n : ℕ} {V : Type*} [DecidableEq V] (t : SpernerTriangulation n V)

/-- The colours occurring on a cell of the face `S` all belong to `S`. -/
lemma image_label_subset {S : Finset (Fin (n + 1))} {C : Finset V} (hC : C ∈ t.cells S) :
    C.image t.label ⊆ S := by
  intro j hj
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hj
  exact t.label_mem S C hC v hv

/-- Membership in the set of rainbow cells. -/
lemma mem_rainbow {S : Finset (Fin (n + 1))} {F : Finset V} :
    F ∈ t.rainbow S ↔ F ∈ t.cells S ∧ F.image t.label = S := Finset.mem_filter

/-- The parity step: passing from a face `S` to the facet `S.erase i₀` preserves the parity of
the number of rainbow cells.  This is the classical "door and room" double count. -/
lemma rainbow_parity_step (S : Finset (Fin (n + 1))) (i₀ : Fin (n + 1)) (hi₀ : i₀ ∈ S)
    (hcard : 1 < S.card) :
    (t.rainbow S).card % 2 = (t.rainbow (S.erase i₀)).card % 2 := by
  obtain ⟨k, hk⟩ : ∃ k, S.card = k + 1 := ⟨S.card - 1, by omega⟩
  set S' := S.erase i₀ with hS'def
  have hS'card : S'.card = k := by
    rw [hS'def, Finset.card_erase_of_mem hi₀, hk]
    omega
  have hS'ss : S' ⊂ S := Finset.erase_ssubset hi₀
  -- `D` is the set of all doors: codimension-one faces of cells of `S` coloured by `S'`.
  set D : Finset (Finset V) :=
    (t.cells S).biUnion (fun C => (C.powersetCard k).filter (fun F => F.image t.label = S'))
    with hDdef
  have hmemD : ∀ F : Finset V,
      F ∈ D ↔ ((∃ C ∈ t.cells S, F ⊆ C) ∧ F.card = k ∧ F.image t.label = S') := by
    intro F
    simp only [hDdef, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨C, hC, ⟨hFC, hFcard⟩, himg⟩; exact ⟨⟨C, hC, hFC⟩, hFcard, himg⟩
    · rintro ⟨⟨C, hC, hFC⟩, hFcard, himg⟩; exact ⟨C, hC, ⟨hFC, hFcard⟩, himg⟩
  -- Double counting of the incidences (cell, door).
  have key : ∑ C ∈ t.cells S, (D.filter (fun F => F ⊆ C)).card
      = ∑ F ∈ D, ((t.cells S).filter (fun C => F ⊆ C)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  -- Left-hand side: count the doors of each cell.
  have hL : ∀ C ∈ t.cells S, (D.filter (fun F => F ⊆ C)).card
      = (if C.image t.label = S then 1 else 0)
        + 2 * (if C.image t.label = S' then 1 else 0) := by
    intro C hC
    have hDC : D.filter (fun F => F ⊆ C)
        = (C.powersetCard k).filter (fun F => F.image t.label = S') := by
      ext F
      simp only [Finset.mem_filter, hmemD, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨_, hFcard, himg⟩, hFC⟩; exact ⟨⟨hFC, hFcard⟩, himg⟩
      · rintro ⟨⟨hFC, hFcard⟩, himg⟩; exact ⟨⟨⟨C, hC, hFC⟩, hFcard, himg⟩, hFC⟩
    rw [hDC, hS'def]
    exact card_doors_cell t.label C S i₀ hi₀ k hk (t.card_cell S C hC) (t.image_label_subset hC)
  -- Right-hand side: a door lies in one or two cells according to whether it is on the boundary.
  have hbd : ∀ F ∈ D, ((∃ T ⊂ S, F ∈ t.cells T) ↔ F ∈ t.rainbow S') := by
    intro F hF
    rw [hmemD] at hF
    obtain ⟨_, hFcard, himg⟩ := hF
    constructor
    · rintro ⟨T, hTS, hFT⟩
      have hTcard : F.card = T.card := t.card_cell T F hFT
      have hsub : S' ⊆ T := by
        rw [← himg]
        intro j hj
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hj
        exact t.label_mem T F hFT v hv
      have hTeq : S' = T := Finset.eq_of_subset_of_card_le hsub (by omega)
      exact t.mem_rainbow.2 ⟨hTeq ▸ hFT, himg⟩
    · intro hF'
      exact ⟨S', hS'ss, (t.mem_rainbow.1 hF').1⟩
  have hR : ∀ F ∈ D, ((t.cells S).filter (fun C => F ⊆ C)).card
      = (if F ∈ t.rainbow S' then 1 else 0) + 2 * (if F ∈ t.rainbow S' then 0 else 1) := by
    intro F hF
    have hF' := hF
    rw [hmemD] at hF'
    obtain ⟨hex, hFcard, _⟩ := hF'
    rw [t.pseudomanifold S hcard F (by omega) hex]
    by_cases h : F ∈ t.rainbow S'
    · rw [if_pos ((hbd F hF).2 h)]; simp [h]
    · rw [if_neg (fun hc => h ((hbd F hF).1 hc))]; simp [h]
  -- Assemble the two counts.
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR] at key
  have hLsum : ∑ C ∈ t.cells S, ((if C.image t.label = S then 1 else 0)
        + 2 * (if C.image t.label = S' then 1 else 0))
      = (t.rainbow S).card + 2 * ((t.cells S).filter (fun C => C.image t.label = S')).card := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter, ← Finset.card_filter]
    rfl
  have hDsub : t.rainbow S' ⊆ D := by
    intro F hF
    rw [t.mem_rainbow] at hF
    rw [hmemD]
    refine ⟨t.face_subset S S' hS'ss F hF.1, ?_, hF.2⟩
    rw [t.card_cell S' F hF.1, hS'card]
  have e1 : ∑ F ∈ D, (if F ∈ t.rainbow S' then 1 else 0) = (t.rainbow S').card := by
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hDsub]
  have e2 : ∑ F ∈ D, (if F ∈ t.rainbow S' then 0 else 1)
      = (D.filter (fun F => F ∉ t.rainbow S')).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun F _ => ?_
    by_cases h : F ∈ t.rainbow S' <;> simp [h]
  have hRsum : ∑ F ∈ D, ((if F ∈ t.rainbow S' then 1 else 0)
        + 2 * (if F ∈ t.rainbow S' then 0 else 1))
      = (t.rainbow S').card + 2 * (D.filter (fun F => F ∉ t.rainbow S')).card := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, e1, e2]
  rw [hLsum, hRsum] at key
  omega

/-- The base case: a vertex of the big simplex carries exactly one rainbow cell. -/
lemma rainbow_vertex (i : Fin (n + 1)) : (t.rainbow {i}).card = 1 := by
  obtain ⟨C, hC⟩ := Finset.card_eq_one.1 (t.vertex_cell i)
  have hCmem : C ∈ t.cells {i} := by rw [hC]; exact Finset.mem_singleton_self C
  have hCcard : C.card = 1 := by rw [t.card_cell {i} C hCmem, Finset.card_singleton]
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 hCcard
  have hlab : t.label v = i :=
    Finset.mem_singleton.1 (t.label_mem {i} {v} hCmem v (Finset.mem_singleton_self v))
  have : t.rainbow {i} = {({v} : Finset V)} := by
    rw [rainbow, hC, Finset.filter_singleton, if_pos]
    simp [hlab]
  rw [this, Finset.card_singleton]

/-- **Sperner's lemma** for an arbitrary nonempty face `S` of the big simplex: the number of
rainbow cells of the induced triangulation of `S` is odd. -/
theorem rainbow_card_odd (S : Finset (Fin (n + 1))) (hS : S.Nonempty) :
    Odd (t.rainbow S).card := by
  rw [Nat.odd_iff]
  induction hm : S.card using Nat.strong_induction_on generalizing S with
  | _ m ih =>
    match m, hm with
    | 0, hm => exact absurd (Finset.card_eq_zero.1 hm) (Finset.nonempty_iff_ne_empty.1 hS)
    | 1, hm =>
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hm
      rw [t.rainbow_vertex i]
    | (m + 2), hm =>
      obtain ⟨i₀, hi₀⟩ := hS
      rw [t.rainbow_parity_step S i₀ hi₀ (by omega)]
      refine ih (m + 1) (by omega) (S.erase i₀) ?_ ?_
      · rw [← Finset.card_pos, Finset.card_erase_of_mem hi₀, hm]
        omega
      · rw [Finset.card_erase_of_mem hi₀, hm]
        omega

end SpernerTriangulation

/-- **Sperner's lemma**: every Sperner colouring of a triangulated simplex has an odd number of
rainbow (fully coloured) cells. -/
theorem sperner_lemma {n : ℕ} {V : Type*} [DecidableEq V] (t : SpernerTriangulation n V) :
    Odd (t.rainbow Finset.univ).card :=
  t.rainbow_card_odd Finset.univ Finset.univ_nonempty

/-! ## Non-vacuity

The hypotheses gathered in `SpernerTriangulation` are satisfiable: we exhibit the trivial
triangulation of the `n`-simplex (every face is a single cell), and a genuinely subdivided
triangulation of the `1`-simplex (an interval cut into two segments). -/

/-- The trivial triangulation of the `n`-simplex: every face `S` is triangulated by the single
cell `S`, and the colouring is the identity. -/
def trivialTriangulation (n : ℕ) : SpernerTriangulation n (Fin (n + 1)) where
  cells S := {S}
  label := id
  card_cell := by
    intro S C hC
    rw [Finset.mem_singleton.1 hC]
  label_mem := by
    intro S C hC v hv
    rw [Finset.mem_singleton.1 hC] at hv
    exact hv
  vertex_cell := by
    intro i
    exact Finset.card_singleton _
  pseudomanifold := by
    intro S _ F hF hex
    obtain ⟨C, hC, hFC⟩ := hex
    rw [Finset.mem_singleton] at hC
    subst hC
    have hne : F ≠ C := by
      intro h
      rw [h] at hF
      omega
    rw [if_pos ⟨F, Finset.ssubset_iff_subset_ne.2 ⟨hFC, hne⟩, Finset.mem_singleton_self F⟩,
      Finset.filter_singleton, if_pos hFC, Finset.card_singleton]
  face_subset := by
    intro S T hTS F hF
    rw [Finset.mem_singleton] at hF
    exact ⟨S, Finset.mem_singleton_self S, hF ▸ hTS.1⟩

/-- The trivial triangulation has exactly one rainbow cell. -/
example (n : ℕ) : ((trivialTriangulation n).rainbow Finset.univ).card = 1 := by
  have h : (trivialTriangulation n).rainbow Finset.univ = {(Finset.univ : Finset (Fin (n + 1)))} := by
    rw [SpernerTriangulation.rainbow]
    show Finset.filter _ ({(Finset.univ : Finset (Fin (n + 1)))}) = _
    rw [Finset.filter_singleton, if_pos]
    exact Finset.image_id
  rw [h, Finset.card_singleton]

/-- The cells of the interval `[0,1]` cut into the two segments `[0,1/2]` and `[1/2,1]`:
the three vertices `0, 1, 2` stand for `0, 1/2, 1`. -/
def subdividedIntervalCells : Finset (Fin 2) → Finset (Finset (Fin 3)) := fun S =>
  if S = {0} then {{0}} else if S = {1} then {{2}} else
  if S = {0, 1} then {{0, 1}, {1, 2}} else ∅

/-- A Sperner colouring of the subdivided interval: the midpoint receives the colour `0`. -/
def subdividedIntervalLabel : Fin 3 → Fin 2 := ![0, 0, 1]

/-- A genuinely subdivided triangulation: the `1`-simplex cut into two segments. -/
def subdividedInterval : SpernerTriangulation 1 (Fin 3) where
  cells := subdividedIntervalCells
  label := subdividedIntervalLabel
  card_cell := by decide
  label_mem := by decide
  vertex_cell := by decide
  pseudomanifold := by decide
  face_subset := by decide

/-- The subdivided interval has exactly one rainbow cell, namely `{1, 2}`. -/
example : subdividedInterval.rainbow Finset.univ = {{1, 2}} := by decide

end Math

