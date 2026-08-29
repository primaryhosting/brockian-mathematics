import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Mathlib (as of this commit) contains *Sperner's theorem* on antichains
(`IsAntichain.sperner`) but **no** Sperner *lemma* about triangulated simplices;
`exact?`/`apply?`/`rw?` therefore have nothing to close this with, and the whole
development below is built from scratch.

## Formalisation

We work with the **barycentric subdivision** of a simplex.  Let `A : Finset α` be the
vertex set of a simplex `Δ(A)` (so `Δ(A)` has dimension `A.card - 1`).  The vertices of
the barycentric subdivision of `Δ(A)` are the barycentres of the faces of `Δ(A)`, i.e.
the nonempty subsets `S ⊆ A`, and the top-dimensional cells are the maximal flags
`S₁ ⊊ S₂ ⊊ ⋯ ⊊ S_k = A` (with `|S_i| = i`).  Such a flag is the same thing as an
ordering `a₁, a₂, …, a_k` of `A` (take `S_i = {a₁, …, a_i}`), so we encode a cell as a
list `l` whose underlying multiset is `A.val` (see `Math.cells`).

A **Sperner colouring** assigns to each vertex `S` of the subdivision a colour
`c S ∈ S` (the barycentre of a face must get a colour of one of the vertices of that
face).  A cell is **rainbow** (or "completely labelled") when its `k` vertices carry
`k` pairwise distinct colours.  `Math.colorSeq c ∅ l` is the list of colours of the
vertices of the cell `l`, listed along the flag.

The main result, `Math.sperner_lemma`, states that the number of rainbow cells is odd.
The section "The flag of faces of a cell" at the end records the dictionary between a
cell `l` and the corresponding maximal flag `Math.flagOf l 0 ⊊ ⋯ ⊊ Math.flagOf l (k-1) = A`
of faces of `Δ(A)`, and checks that the colours of the cell are exactly the colours of
the barycentres of that flag.
-/

open Finset List

namespace Math

variable {α : Type*} [DecidableEq α]

/-! ### The colours along a flag -/

/-- `colorSeq c acc l` is the list of colours `c (acc ∪ {a₁,…,a_i})`, `i = 1 … |l|`,
of the vertices of the flag determined by the ordering `l = [a₁, …, a_n]`
(started from the face `acc`). -/
def colorSeq (c : Finset α → α) : Finset α → List α → List α
  | _, [] => []
  | acc, a :: t => c (insert a acc) :: colorSeq c (insert a acc) t

@[simp] lemma colorSeq_nil (c : Finset α → α) (acc : Finset α) : colorSeq c acc [] = [] := rfl

@[simp] lemma colorSeq_cons (c : Finset α → α) (acc : Finset α) (a : α) (t : List α) :
    colorSeq c acc (a :: t) = c (insert a acc) :: colorSeq c (insert a acc) t := rfl

@[simp] lemma colorSeq_length (c : Finset α → α) (acc : Finset α) (l : List α) :
    (colorSeq c acc l).length = l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih => simp [ih]

/-- Every colour occurring along a flag is a colour of a vertex of the corresponding face. -/
lemma colorSeq_mem_union {c : Finset α → α} {B : Finset α}
    (hc : ∀ S : Finset α, S.Nonempty → S ⊆ B → c S ∈ S) :
    ∀ (l : List α) (acc : Finset α), acc ⊆ B → l.toFinset ⊆ B →
      ∀ x ∈ colorSeq c acc l, x ∈ acc ∪ l.toFinset := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    intro acc hacc hl x hx
    simp only [colorSeq_cons, List.mem_cons] at hx
    have haB : a ∈ B := hl (by simp)
    have htB : t.toFinset ⊆ B := fun y hy => hl (by simp only [List.toFinset_cons]; exact Finset.mem_insert_of_mem hy)
    have hins : insert a acc ⊆ B := Finset.insert_subset haB hacc
    rcases hx with rfl | hx
    · have := hc (insert a acc) ⟨a, Finset.mem_insert_self _ _⟩ hins
      simp only [Finset.mem_insert] at this
      rcases this with h | h
      · simp [h]
      · simp [h]
    · have := ih (insert a acc) hins htB x hx
      simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons] at this ⊢
      tauto

lemma colorSeq_dropLast (c : Finset α → α) (acc : Finset α) (l : List α) :
    colorSeq c acc l.dropLast = (colorSeq c acc l).dropLast := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b s => simp [ih]

/-! ### Cells -/

/-- The top-dimensional cells of the barycentric subdivision of the simplex on the
vertex set `A`, encoded as orderings of `A`. -/
noncomputable def cells (A : Finset α) : Finset (List α) := A.toList.permutations.toFinset

lemma mem_cells {A : Finset α} {l : List α} : l ∈ cells A ↔ (l : Multiset α) = A.val := by
  rw [cells, List.mem_toFinset, List.mem_permutations, ← Multiset.coe_eq_coe, Finset.coe_toList]

/-- A cell is *rainbow* if the colours of its vertices are pairwise distinct. -/
def IsRainbow (c : Finset α → α) (l : List α) : Prop := (colorSeq c ∅ l).Nodup

instance (c : Finset α → α) (l : List α) : Decidable (IsRainbow c l) := by
  unfold IsRainbow; infer_instance

/-- The rainbow cells of the barycentric subdivision of the simplex on vertex set `A`. -/
noncomputable def rainbowCells (c : Finset α → α) (A : Finset α) : Finset (List α) :=
  (cells A).filter (fun l => IsRainbow c l)

/-! ### Adjacent transpositions of a cell -/

/-- Swap the entries at positions `i` and `i+1`. -/
def swapAt : List α → ℕ → List α
  | a :: b :: t, 0 => b :: a :: t
  | a :: t, (n + 1) => a :: swapAt t n
  | l, _ => l

omit [DecidableEq α] in
lemma swapAt_perm : ∀ (l : List α) (i : ℕ), swapAt l i ~ l
  | [], _ => by simp [swapAt]
  | [a], 0 => by simp [swapAt]
  | a :: b :: t, 0 => by simpa [swapAt] using List.Perm.swap _ _ _
  | a :: t, (n + 1) => by simpa [swapAt] using (swapAt_perm t n).cons a

omit [DecidableEq α] in
lemma swapAt_length (l : List α) (i : ℕ) : (swapAt l i).length = l.length :=
  (swapAt_perm l i).length_eq

omit [DecidableEq α] in
lemma swapAt_swapAt : ∀ (l : List α) (i : ℕ), i + 1 < l.length → swapAt (swapAt l i) i = l
  | a :: b :: t, 0 => by intro _; simp [swapAt]
  | a :: t, (n + 1) => by
      intro h
      simp only [List.length_cons] at h
      simp [swapAt, swapAt_swapAt t n (by omega)]
  | [], _ => by simp
  | [a], 0 => by simp

omit [DecidableEq α] in
lemma swapAt_ne : ∀ (l : List α) (i : ℕ), l.Nodup → i + 1 < l.length → swapAt l i ≠ l
  | a :: b :: t, 0 => by
      intro hnd _
      simp only [List.nodup_cons, List.mem_cons] at hnd
      have hab : a ≠ b := fun h => hnd.1 (Or.inl h)
      simp only [swapAt, ne_eq, List.cons.injEq, not_and]
      intro h; exact absurd h hab.symm
  | a :: t, (n + 1) => by
      intro hnd h
      simp only [List.length_cons] at h
      simp only [swapAt, ne_eq, List.cons.injEq, true_and]
      exact swapAt_ne t n hnd.of_cons (by omega)
  | [], _ => by simp
  | [a], 0 => by simp

lemma colorSeq_swapAt_eraseIdx (c : Finset α → α) :
    ∀ (l : List α) (i : ℕ) (acc : Finset α), i + 1 < l.length →
      (colorSeq c acc (swapAt l i)).eraseIdx i = (colorSeq c acc l).eraseIdx i
  | a :: b :: t, 0, acc, _ => by
      simp only [swapAt, colorSeq_cons, List.eraseIdx_zero, List.tail_cons]
      rw [Finset.insert_comm]
  | a :: t, (n + 1), acc, h => by
      simp only [List.length_cons] at h
      simp only [swapAt, colorSeq_cons, List.eraseIdx_cons_succ, List.cons.injEq, true_and]
      exact colorSeq_swapAt_eraseIdx c t n (insert a acc) (by omega)
  | [], _, _, h => by simp at h
  | [a], 0, _, h => by simp at h

/-! ### Two counting lemmas -/

lemma coe_eraseIdx : ∀ (l : List α) (i : ℕ) (h : i < l.length),
    ((l.eraseIdx i : List α) : Multiset α) = (l : Multiset α).erase l[i]
  | a :: t, 0, _ => by simp
  | a :: t, (n + 1), h => by
      simp only [List.length_cons] at h
      have hn : n < t.length := by omega
      have ht := coe_eraseIdx t n hn
      have hmem : t[n] ∈ (t : Multiset α) := by exact_mod_cast List.getElem_mem hn
      simp only [List.eraseIdx_cons_succ, List.getElem_cons_succ, ← Multiset.cons_coe, ht]
      by_cases hat : t[n] = a
      · rw [hat] at hmem ⊢
        rw [Multiset.erase_cons_head, Multiset.cons_erase hmem]
      · rw [Multiset.erase_cons_tail _ (fun h => hat h.symm)]

lemma card_filter_getElem?_eq (l : List α) (v : α) :
    ((Finset.range l.length).filter (fun i => l[i]? = some v)).card = l.count v := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [Finset.card_filter, List.length_cons, Finset.sum_range_succ']
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some_inj]
    rw [← Finset.card_filter, ih, List.count_cons]
    by_cases h : a = v <;> simp [h]

/-! ### The doors of a cell -/

/-- The indices `i` such that deleting the `i`-th vertex of the cell `l` leaves a
"door": a face whose colours are exactly the elements of the multiset `D`. -/
def goodIdx (c : Finset α → α) (D : Multiset α) (l : List α) : Finset ℕ :=
  (Finset.range l.length).filter
    (fun i => (((colorSeq c ∅ l).eraseIdx i : List α) : Multiset α) = D)

/-- A cell has an odd number of doors avoiding the colour `z` exactly when it is rainbow. -/
lemma odd_card_goodIdx_iff {A : Finset α} {c : Finset α → α} {z : α} (hz : z ∈ A)
    (hc : ∀ S : Finset α, S.Nonempty → S ⊆ A → c S ∈ S)
    {l : List α} (hl : (l : Multiset α) = A.val) :
    Odd (goodIdx c (A.erase z).val l).card ↔ IsRainbow c l := by
  set C := colorSeq c ∅ l with hCdef
  set D := (A.erase z).val with hDdef
  have hllen : l.length = A.card := by
    have := congrArg Multiset.card hl
    simpa using this
  have hlenEq : l.length = C.length := by rw [hCdef, colorSeq_length]
  have hlA : l.toFinset ⊆ A := by
    intro x hx
    rw [List.mem_toFinset] at hx
    have hx' : x ∈ (l : Multiset α) := by exact_mod_cast hx
    rw [hl] at hx'; exact hx'
  have hCA : ∀ x ∈ C, x ∈ A := by
    intro x hx
    have := colorSeq_mem_union hc l ∅ (Finset.empty_subset _) hlA x hx
    simp only [Finset.empty_union] at this
    exact hlA this
  have hDnodup : D.Nodup := (A.erase z).nodup
  have hzD : z ∉ D := by
    simp only [hDdef, Finset.mem_val]
    exact Finset.notMem_erase z A
  have key : ∀ i (hi : i < C.length),
      (((C.eraseIdx i : List α) : Multiset α) = D ↔ (C : Multiset α) = C[i] ::ₘ D) := by
    intro i hi
    rw [coe_eraseIdx C i hi]
    constructor
    · intro h
      rw [← h]
      exact (Multiset.cons_erase (by exact_mod_cast List.getElem_mem hi)).symm
    · intro h
      rw [h, Multiset.erase_cons_head]
  by_cases hex : ∃ v, (C : Multiset α) = v ::ₘ D
  · obtain ⟨v, hv⟩ := hex
    have hvC : v ∈ C := by
      have : v ∈ (C : Multiset α) := by rw [hv]; exact Multiset.mem_cons_self _ _
      exact_mod_cast this
    have hfilter : goodIdx c D l = (Finset.range C.length).filter (fun i => C[i]? = some v) := by
      rw [goodIdx, ← hCdef, hlenEq]
      refine Finset.filter_congr ?_
      intro i hi
      rw [Finset.mem_range] at hi
      rw [key i hi, hv, List.getElem?_eq_getElem hi]
      simp only [Option.some_inj]
      constructor
      · intro h; exact ((Multiset.cons_inj_left D).mp h).symm
      · intro h; rw [h]
    have hcard : (goodIdx c D l).card = Multiset.count v (C : Multiset α) := by
      rw [hfilter, card_filter_getElem?_eq, Multiset.coe_count]
    rw [hv, Multiset.count_cons_self] at hcard
    by_cases hvz : v = z
    · subst hvz
      have hcount : Multiset.count v D = 0 := Multiset.count_eq_zero.mpr hzD
      rw [hcount] at hcard
      have hCA' : (C : Multiset α) = A.val := by
        rw [hv, hDdef]; exact Multiset.cons_erase hz
      have : IsRainbow c l := by
        show C.Nodup
        rw [← Multiset.coe_nodup, hCA']
        exact A.nodup
      simp [hcard, this]
    · have hvA : v ∈ A := hCA v hvC
      have hvD : v ∈ D := by
        rw [hDdef]
        exact Multiset.mem_erase_of_ne hvz |>.mpr (by exact_mod_cast hvA)
      have hcount : Multiset.count v D = 1 := Multiset.count_eq_one_of_mem hDnodup hvD
      rw [hcount] at hcard
      have hnr : ¬ IsRainbow c l := by
        show ¬ C.Nodup
        rw [← Multiset.coe_nodup, hv]
        intro hnd
        have := Multiset.nodup_iff_count_le_one.mp hnd v
        rw [Multiset.count_cons_self, hcount] at this
        omega
      simp only [hcard, hnr, iff_false]
      decide
  · have hempty : goodIdx c D l = ∅ := by
      rw [goodIdx, ← hCdef, hlenEq]
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro i hi
      rw [Finset.mem_range] at hi
      rw [key i hi]
      exact fun h => hex ⟨C[i], h⟩
    have hnr : ¬ IsRainbow c l := by
      intro hnd
      apply hex
      refine ⟨z, ?_⟩
      have hCnd : (C : Multiset α).Nodup := Multiset.coe_nodup.mpr hnd
      have hsub : C.toFinset ⊆ A := fun x hx => hCA x (List.mem_toFinset.mp hx)
      have hcardC : C.toFinset.card = A.card := by
        rw [List.toFinset_card_of_nodup hnd, ← hlenEq, hllen]
      have : C.toFinset = A := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcardC.symm)
      have hCval : (C : Multiset α) = A.val := by
        rw [← this, List.toFinset_val, List.Nodup.dedup (hnd : C.Nodup)]
      rw [hCval, hDdef]
      exact (Multiset.cons_erase hz).symm
    simp [hempty, hnr]

/-! ### Cells, colours and the top face -/

lemma length_of_mem_cells {A : Finset α} {l : List α} (h : l ∈ cells A) : l.length = A.card := by
  have := congrArg Multiset.card (mem_cells.mp h); simpa using this

lemma nodup_of_mem_cells {A : Finset α} {l : List α} (h : l ∈ cells A) : l.Nodup := by
  rw [← Multiset.coe_nodup, mem_cells.mp h]; exact A.nodup

lemma toFinset_of_mem_cells {A : Finset α} {l : List α} (h : l ∈ cells A) : l.toFinset = A := by
  have : ((l : Multiset α)).toFinset = A.val.toFinset := by rw [mem_cells.mp h]
  simpa using this

lemma cells_empty : cells (∅ : Finset α) = {[]} := by
  ext l
  simp [mem_cells]

lemma coe_eq_val_of_nodup {m : List α} {B : Finset α} (h1 : m.Nodup) (h3 : m.length = B.card)
    (h2 : m.toFinset ⊆ B ∨ B ⊆ m.toFinset) : (m : Multiset α) = B.val := by
  have hcard : m.toFinset.card = B.card := by rw [List.toFinset_card_of_nodup h1, h3]
  have hEq : m.toFinset = B := by
    rcases h2 with h | h
    · exact Finset.eq_of_subset_of_card_le h (le_of_eq hcard.symm)
    · exact (Finset.eq_of_subset_of_card_le h (le_of_eq hcard)).symm
  rw [← hEq, List.toFinset_val, List.Nodup.dedup h1]

/-- The colours occurring along a cell of `Δ(B)` are colours of vertices of `Δ(B)`. -/
lemma colorSeq_mem_of_mem_cells {B : Finset α} {c : Finset α → α}
    (hc : ∀ S : Finset α, S.Nonempty → S ⊆ B → c S ∈ S) {l : List α} (hl : l.toFinset ⊆ B)
    {x : α} (hx : x ∈ colorSeq c ∅ l) : x ∈ l.toFinset := by
  have := colorSeq_mem_union hc l ∅ (Finset.empty_subset _) hl x hx
  simpa using this

/-- A rainbow cell of `Δ(B)` carries each colour of `B` exactly once. -/
lemma coe_colorSeq_of_rainbow {B : Finset α} {c : Finset α → α}
    (hc : ∀ S : Finset α, S.Nonempty → S ⊆ B → c S ∈ S) {l : List α} (hl : l ∈ cells B)
    (hr : IsRainbow c l) : ((colorSeq c ∅ l : List α) : Multiset α) = B.val := by
  refine coe_eq_val_of_nodup hr ?_ (Or.inl ?_)
  · rw [colorSeq_length, length_of_mem_cells hl]
  · intro x hx
    rw [List.mem_toFinset] at hx
    have hsub : l.toFinset ⊆ B := by rw [toFinset_of_mem_cells hl]
    have := colorSeq_mem_of_mem_cells hc hsub hx
    rwa [toFinset_of_mem_cells hl] at this

/-- If deleting the last vertex of a cell `l` of `Δ(A)` leaves a face whose colours are
exactly `A \ {z}`, then that face is a rainbow cell of the facet `Δ(A \ {z})`, and `l` is
obtained from it by appending the vertex `A` (whose colour must then be `z`). -/
lemma dropLast_mem_rainbowCells {A : Finset α} {c : Finset α → α} {z : α} (hz : z ∈ A)
    (hc : ∀ S : Finset α, S.Nonempty → S ⊆ A → c S ∈ S) {l : List α} (hl : l ∈ cells A)
    (hd : ((colorSeq c ∅ l.dropLast : List α) : Multiset α) = (A.erase z).val) :
    l.dropLast ∈ rainbowCells c (A.erase z) ∧ l = l.dropLast ++ [z] := by
  have hlen : l.length = A.card := length_of_mem_cells hl
  have hlne : l ≠ [] := by
    intro h
    rw [h] at hlen
    simp only [List.length_nil] at hlen
    exact absurd (Finset.card_pos.mpr ⟨z, hz⟩) (by omega)
  have hmnd : l.dropLast.Nodup := (List.dropLast_sublist l).nodup (nodup_of_mem_cells hl)
  have hmlen : l.dropLast.length = (A.erase z).card := by
    rw [List.length_dropLast, hlen, Finset.card_erase_of_mem hz]
  have hmA : l.dropLast.toFinset ⊆ A := by
    intro x hx
    rw [List.mem_toFinset] at hx
    have : x ∈ l := (List.dropLast_sublist l).mem hx
    rw [← toFinset_of_mem_cells hl, List.mem_toFinset]
    exact this
  have hsub : A.erase z ⊆ l.dropLast.toFinset := by
    intro x hx
    have hx1 : x ∈ ((colorSeq c ∅ l.dropLast : List α) : Multiset α) := by
      rw [hd]; exact hx
    have hx2 : x ∈ colorSeq c ∅ l.dropLast := by exact_mod_cast hx1
    exact colorSeq_mem_of_mem_cells hc hmA hx2
  have hmval : (l.dropLast : Multiset α) = (A.erase z).val :=
    coe_eq_val_of_nodup hmnd hmlen (Or.inr hsub)
  refine ⟨?_, ?_⟩
  · rw [rainbowCells, Finset.mem_filter]
    refine ⟨mem_cells.mpr hmval, ?_⟩
    show (colorSeq c ∅ l.dropLast).Nodup
    rw [← Multiset.coe_nodup, hd]
    exact (A.erase z).nodup
  · have hlast := List.dropLast_append_getLast hlne
    set x := l.getLast hlne with hxdef
    have h1 : (l : Multiset α) = x ::ₘ (l.dropLast : Multiset α) := by
      conv_lhs => rw [← hlast]
      exact Multiset.coe_eq_coe.mpr (List.perm_append_singleton _ _)
    have h2 : x ::ₘ (A.erase z).val = z ::ₘ (A.erase z).val := by
      have hA : (l : Multiset α) = A.val := mem_cells.mp hl
      rw [h1, hmval] at hA
      rw [hA]
      exact (Multiset.cons_erase hz).symm
    have hxz : x = z := (Multiset.cons_inj_left _).mp h2
    conv_lhs => rw [← hlast]
    rw [hxz]

/-- Conversely, appending the top face to a rainbow cell of the facet `Δ(A \ {z})`
produces a cell of `Δ(A)` whose last door has colours `A \ {z}`. -/
lemma concat_mem_cells {A : Finset α} {c : Finset α → α} {z : α} (hz : z ∈ A)
    (hc : ∀ S : Finset α, S.Nonempty → S ⊆ A → c S ∈ S) {m : List α}
    (hm : m ∈ rainbowCells c (A.erase z)) :
    (m ++ [z]) ∈ cells A ∧
      ((colorSeq c ∅ (m ++ [z]).dropLast : List α) : Multiset α) = (A.erase z).val := by
  rw [rainbowCells, Finset.mem_filter] at hm
  obtain ⟨hm1, hm2⟩ := hm
  have hval : ((m ++ [z] : List α) : Multiset α) = A.val := by
    have h : ((m ++ [z] : List α) : Multiset α) = z ::ₘ (m : Multiset α) :=
      Multiset.coe_eq_coe.mpr (List.perm_append_singleton _ _)
    rw [h, mem_cells.mp hm1]
    exact Multiset.cons_erase hz
  refine ⟨mem_cells.mpr hval, ?_⟩
  rw [List.dropLast_concat]
  exact coe_colorSeq_of_rainbow
    (fun S hS hSA => hc S hS (hSA.trans (Finset.erase_subset _ _))) hm1 hm2

/-! ### The main theorem -/

/-- **Sperner's lemma.**  Let `Δ(A)` be the simplex with vertex set `A`, barycentrically
subdivided; its cells are the maximal flags of faces of `Δ(A)`, encoded as orderings of
`A`.  For any Sperner colouring `c` (each barycentre `S` receives a colour `c S ∈ S`),
the number of rainbow cells is odd. -/
private lemma sperner_aux : ∀ (n : ℕ) (A : Finset α) (c : Finset α → α), A.card = n →
    (∀ S : Finset α, S.Nonempty → S ⊆ A → c S ∈ S) → Odd (rainbowCells c A).card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A c hcard hc
    rcases Finset.eq_empty_or_nonempty A with rfl | hA
    · have h1 : rainbowCells c (∅ : Finset α) = {[]} := by
        rw [rainbowCells, cells_empty, Finset.filter_eq_self.mpr]
        intro l hl
        rw [Finset.mem_singleton] at hl
        subst hl
        exact List.nodup_nil
      rw [h1]
      simp
    · obtain ⟨z, hz⟩ := hA
      have hk : 1 ≤ A.card := Finset.card_pos.mpr ⟨z, hz⟩
      set k := A.card with hkdef
      set D := (A.erase z).val with hDdef
      set S := ((cells A) ×ˢ Finset.range k).filter
        (fun p => (((colorSeq c ∅ p.1).eraseIdx p.2 : List α) : Multiset α) = D) with hSdef
      -- Facts about membership in `S`.
      have hmemS : ∀ p : List α × ℕ, p ∈ S →
          p.1 ∈ cells A ∧ p.2 < k ∧
            (((colorSeq c ∅ p.1).eraseIdx p.2 : List α) : Multiset α) = D := by
        intro p hp
        rw [hSdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
        exact ⟨hp.1.1, hp.1.2, hp.2⟩
      -- Step 1: counting the doors cell by cell.
      have hScard : S.card = ∑ l ∈ cells A, (goodIdx c D l).card := by
        rw [hSdef, Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [goodIdx, Finset.card_filter, length_of_mem_cells hl]
      have hstep1 : ((S.card : ℕ) : ZMod 2) = ((rainbowCells c A).card : ZMod 2) := by
        rw [hScard, rainbowCells, Finset.card_filter]
        push_cast
        refine Finset.sum_congr rfl fun l hl => ?_
        by_cases hr : IsRainbow c l
        · have hodd : Odd (goodIdx c D l).card :=
            (odd_card_goodIdx_iff hz hc (mem_cells.mp hl)).mpr hr
          rw [ZMod.natCast_eq_one_iff_odd.mpr hodd]
          simp [hr]
        · have hev : Even (goodIdx c D l).card := by
            rw [← Nat.not_odd_iff_even]
            exact fun h => hr ((odd_card_goodIdx_iff hz hc (mem_cells.mp hl)).mp h)
          rw [ZMod.natCast_eq_zero_iff_even.mpr hev]
          simp [hr]
      -- Step 2: the interior doors cancel in pairs.
      have hmid : (((S.filter (fun p => ¬ p.2 = k - 1)).card : ℕ) : ZMod 2) = 0 := by
        have hfacts : ∀ p : List α × ℕ, p ∈ S.filter (fun p => ¬ p.2 = k - 1) →
            p.1 ∈ cells A ∧ p.2 + 1 < p.1.length ∧
              (((colorSeq c ∅ p.1).eraseIdx p.2 : List α) : Multiset α) = D ∧ ¬ p.2 = k - 1 := by
          intro p hp
          rw [Finset.mem_filter] at hp
          obtain ⟨h1, h2, h3⟩ := hmemS p hp.1
          refine ⟨h1, ?_, h3, hp.2⟩
          rw [length_of_mem_cells h1]
          omega
        have h0 : ∑ _p ∈ S.filter (fun p => ¬ p.2 = k - 1), (1 : ZMod 2) = 0 := by
          refine Finset.sum_involution (fun p _ => (swapAt p.1 p.2, p.2)) (fun a ha => by decide)
            ?_ ?_ ?_
          · intro a ha _
            obtain ⟨h1, h2, _, _⟩ := hfacts a ha
            intro hcon
            exact swapAt_ne a.1 a.2 (nodup_of_mem_cells h1) h2 (congrArg Prod.fst hcon)
          · intro a ha
            obtain ⟨h1, h2, h3, h4⟩ := hfacts a ha
            show (swapAt a.1 a.2, a.2) ∈ S.filter (fun p => ¬ p.2 = k - 1)
            refine Finset.mem_filter.mpr ⟨?_, h4⟩
            rw [hSdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · exact mem_cells.mpr
                ((Multiset.coe_eq_coe.mpr (swapAt_perm a.1 a.2)).trans (mem_cells.mp h1))
            · show a.2 < k
              have hlen : a.1.length = k := (length_of_mem_cells h1).trans hkdef.symm
              omega
            · show (((colorSeq c ∅ (swapAt a.1 a.2)).eraseIdx a.2 : List α) : Multiset α) = D
              rw [colorSeq_swapAt_eraseIdx c a.1 a.2 ∅ h2]; exact h3
          · intro a ha
            obtain ⟨h1, h2, _, _⟩ := hfacts a ha
            show (swapAt (swapAt a.1 a.2) a.2, a.2) = a
            rw [swapAt_swapAt a.1 a.2 h2]
        simpa using h0
      -- Step 3: the boundary doors are the rainbow cells of the facet.
      have htop : (S.filter (fun p => p.2 = k - 1)).card = (rainbowCells c (A.erase z)).card := by
        have hkey : ∀ p : List α × ℕ, p ∈ S.filter (fun p => p.2 = k - 1) →
            p.1.dropLast ∈ rainbowCells c (A.erase z) ∧ p.1 = p.1.dropLast ++ [z] := by
          intro p hp
          rw [Finset.mem_filter] at hp
          obtain ⟨h1, _, h3⟩ := hmemS p hp.1
          have hlen : (colorSeq c ∅ p.1).length = k := by
            rw [colorSeq_length, length_of_mem_cells h1]
          rw [hp.2, ← hlen, List.eraseIdx_length_sub_one, ← colorSeq_dropLast] at h3
          exact dropLast_mem_rainbowCells hz hc h1 h3
        refine Finset.card_bij (fun p _ => p.1.dropLast) (fun p hp => (hkey p hp).1) ?_ ?_
        · intro p hp q hq hpq
          rw [Finset.mem_filter] at hp hq
          have h1 := (hkey p (Finset.mem_filter.mpr hp)).2
          have h2 := (hkey q (Finset.mem_filter.mpr hq)).2
          have hpq' : p.1.dropLast = q.1.dropLast := hpq
          have hfst : p.1 = q.1 := by rw [h1, h2, hpq']
          exact Prod.ext hfst (by rw [hp.2, hq.2])
        · intro m hm
          obtain ⟨h1, h2⟩ := concat_mem_cells hz hc hm
          refine ⟨(m ++ [z], k - 1), ?_, by show (m ++ [z]).dropLast = m; simp⟩
          rw [Finset.mem_filter, hSdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          have hlen : (colorSeq c ∅ (m ++ [z])).length = k := by
            rw [colorSeq_length, length_of_mem_cells h1]
          refine ⟨⟨⟨h1, by omega⟩, ?_⟩, rfl⟩
          rw [show (m ++ [z], k - 1).2 = k - 1 from rfl, show (m ++ [z], k - 1).1 = m ++ [z] from rfl,
            ← hlen, List.eraseIdx_length_sub_one, ← colorSeq_dropLast]
          exact h2
      -- Step 4: induction on the dimension.
      have hIH : Odd (rainbowCells c (A.erase z)).card := by
        refine ih (A.erase z).card ?_ (A.erase z) c rfl
          (fun S hS hSA => hc S hS (hSA.trans (Finset.erase_subset _ _)))
        rw [← hcard]
        exact Finset.card_erase_lt_of_mem hz
      rw [← ZMod.natCast_eq_one_iff_odd, ← hstep1,
        ← Finset.card_filter_add_card_filter_not (s := S) (fun p => p.2 = k - 1)]
      push_cast
      rw [hmid, add_zero, htop, ZMod.natCast_eq_one_iff_odd]
      exact hIH

/-- **Sperner's lemma.**  Let `Δ(A)` be the simplex with vertex set `A`, barycentrically
subdivided; its cells are the maximal flags of faces of `Δ(A)`, encoded as orderings of
`A`.  For any Sperner colouring `c` (each barycentre `S` receives a colour `c S ∈ S`),
the number of rainbow cells is odd. -/
theorem sperner_lemma (A : Finset α) (c : Finset α → α)
    (hc : ∀ S : Finset α, S.Nonempty → S ⊆ A → c S ∈ S) :
    Odd (rainbowCells c A).card :=
  sperner_aux A.card A c rfl hc

/-! ### The flag of faces of a cell

The lemmas in this section spell out the geometric meaning of the encoding: a cell `l`
of the barycentric subdivision of `Δ(A)` really is a maximal flag
`flagOf l 0 ⊊ flagOf l 1 ⊊ ⋯ ⊊ flagOf l (|A| - 1) = A` of faces of `Δ(A)`, with
`(flagOf l i).card = i + 1`, and `colorSeq c ∅ l` really is the list of colours of the
barycentres of the faces of that flag. -/

/-- The `i`-th face of the flag of faces determined by the ordering `l`, namely the face
spanned by the first `i + 1` vertices of `l`. -/
def flagOf (l : List α) (i : ℕ) : Finset α := (l.take (i + 1)).toFinset

lemma colorSeq_eq_map_aux (c : Finset α → α) :
    ∀ (l : List α) (acc : Finset α),
      colorSeq c acc l = (List.range l.length).map (fun i => c (acc ∪ (l.take (i + 1)).toFinset))
  | [], acc => by simp
  | a :: t, acc => by
      rw [List.length_cons, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, colorSeq_cons]
      congr 1
      · simp
      · rw [colorSeq_eq_map_aux c t (insert a acc)]
        refine List.map_congr_left ?_
        intro i _
        simp only [Function.comp_apply, List.take_succ_cons, List.toFinset_cons]
        rw [Finset.union_insert, Finset.insert_union]

/-- The colours of a cell are the colours of the barycentres of the faces of its flag. -/
lemma colorSeq_eq_map (c : Finset α → α) (l : List α) :
    colorSeq c ∅ l = (List.range l.length).map (fun i => c (flagOf l i)) := by
  rw [colorSeq_eq_map_aux]
  simp [flagOf]

/-- The `i`-th face of the flag of a cell has exactly `i + 1` vertices. -/
lemma flagOf_card {l : List α} (h : l.Nodup) {i : ℕ} (hi : i < l.length) :
    (flagOf l i).card = i + 1 := by
  rw [flagOf, List.toFinset_card_of_nodup (h.sublist (List.take_sublist _ _)), List.length_take]
  omega

lemma flagOf_subset_succ (l : List α) (i : ℕ) : flagOf l i ⊆ flagOf l (i + 1) := by
  intro x hx
  rw [flagOf, List.mem_toFinset] at hx ⊢
  exact List.IsPrefix.mem hx (List.take_prefix_take_left (by omega))

/-- The flag of a cell is a strictly increasing chain of faces. -/
lemma flagOf_ssubset {l : List α} (h : l.Nodup) {i : ℕ} (hi : i + 1 < l.length) :
    flagOf l i ⊂ flagOf l (i + 1) := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨flagOf_subset_succ l i, ?_⟩
  intro hEq
  have h1 := flagOf_card h (i := i) (by omega)
  have h2 := flagOf_card h (i := i + 1) hi
  rw [hEq, h2] at h1
  omega

/-- The flag of a cell of `Δ(A)` ends at the top face `A`. -/
lemma flagOf_top {A : Finset α} {l : List α} (h : l ∈ cells A) (hA : A.Nonempty) :
    flagOf l (A.card - 1) = A := by
  have hlen := length_of_mem_cells h
  have hpos : 0 < A.card := Finset.card_pos.mpr hA
  rw [flagOf, show A.card - 1 + 1 = l.length by omega, List.take_length,
    toFinset_of_mem_cells h]

/-- Every face of the flag of a cell of `Δ(A)` is a face of `Δ(A)`. -/
lemma flagOf_subset {A : Finset α} {l : List α} (h : l ∈ cells A) (i : ℕ) : flagOf l i ⊆ A := by
  rw [← toFinset_of_mem_cells h, flagOf]
  intro x hx
  rw [List.mem_toFinset] at hx ⊢
  exact List.IsPrefix.mem hx (List.take_prefix _ _)

/-! ### A worked example

The subdivided `1`-simplex `Δ({0,1})` (a segment with vertices `0`, `1` and its midpoint
`{0,1}`) has two cells, `[0,1]` and `[1,0]`, i.e. the two little segments.  For the
Sperner colouring giving the midpoint the colour `0`, exactly one of them is rainbow. -/

lemma cells_zero_one : cells ({0, 1} : Finset ℕ) = {[0, 1], [1, 0]} := by
  ext l
  rw [mem_cells, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have hlen : l.length = 2 := by
      have := congrArg Multiset.card h; simpa using this
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
    have hnd : ([a, b] : List ℕ).Nodup := by
      rw [← Multiset.coe_nodup, h]; exact ({0, 1} : Finset ℕ).nodup
    have hab : a ≠ b := by simpa using hnd
    have ha : a ∈ ({0, 1} : Finset ℕ).val := by rw [← h]; simp
    have hb : b ∈ ({0, 1} : Finset ℕ).val := by rw [← h]; simp
    simp only [Finset.mem_val, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
  · rintro (rfl | rfl) <;> decide

/-- The colouring used below really is a Sperner colouring of `Δ({0,1})`. -/
lemma isSpernerColouring_zero_one : ∀ S : Finset ℕ, S.Nonempty → S ⊆ ({0, 1} : Finset ℕ) →
    (if S = ({1} : Finset ℕ) then 1 else 0) ∈ S := by
  intro S hS hSA
  have h : S ∈ ({0, 1} : Finset ℕ).powerset := Finset.mem_powerset.mpr hSA
  fin_cases h <;> simp_all <;> decide

/-- The exact count in the worked example: one rainbow cell (which is odd, as
`Math.sperner_lemma` predicts). -/
example :
    (rainbowCells (fun S => if S = ({1} : Finset ℕ) then 1 else 0)
      ({0, 1} : Finset ℕ)).card = 1 := by
  rw [rainbowCells, cells_zero_one]
  decide

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

