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

/-!
# Sperner's lemma

Every Sperner colouring of a triangulated simplex has an odd number of rainbow cells.
-/

namespace Math

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of cells of `T` containing the face `F`. -/
def cellMult (T : Finset (Finset V)) (F : Finset V) : ℕ :=
  (T.filter (fun σ => F ⊆ σ)).card

/-- The rainbow cells of `T`: those whose vertices carry all the colours `0, …, n`. -/
def rainbowCells (c : V → ℕ) (n : ℕ) (T : Finset (Finset V)) : Finset (Finset V) :=
  T.filter (fun σ => σ.image c = Finset.range (n + 1))

/-- The induced triangulation on the face spanned by the colours `0, …, n`. -/
def bdry (car : V → Finset ℕ) (n : ℕ) (T : Finset (Finset V)) : Finset (Finset V) :=
  Finset.univ.filter (fun F =>
    F.card = n + 1 ∧ (∀ v ∈ F, car v ⊆ Finset.range (n + 1)) ∧ Odd (cellMult T F))

/-- `IsSpernerTriangulation c car n T` is the combinatorial model of an `n`-simplex,
triangulated with cell set `T`, carrying a Sperner colouring `c`.

A vertex `v` has a colour `c v` and a *carrier* `car v`, the set of colours spanning the
smallest face of the big simplex containing `v`.  The conditions are:

* every cell has `n+1` vertices;
* (Sperner condition) `c v ∈ car v`, and `car v` is a set of colours of the big simplex;
* a face of a cell of size `n` lying in an odd number of cells is a boundary face, hence is
  contained in a proper face of the big simplex, i.e. misses some colour `i`;
* the induced triangulation of the face spanned by the colours `0, …, n-1` is again a Sperner
  triangulation, of dimension `n-1`;
* in dimension `0`, the triangulation is a single vertex, coloured `0`.

See `Math.isSpernerTriangulation_std`, `Math.segment_isSpernerTriangulation` and
`Math.triangle_isSpernerTriangulation` for instances of this notion. -/
def IsSpernerTriangulation (c : V → ℕ) (car : V → Finset ℕ) : ℕ → Finset (Finset V) → Prop
  | 0, T => ∃ v : V, T = {{v}} ∧ c v = 0
  | (n + 1), T =>
      (∀ σ ∈ T, σ.card = n + 2) ∧
      (∀ σ ∈ T, ∀ v ∈ σ, c v ∈ car v ∧ car v ⊆ Finset.range (n + 2)) ∧
      (∀ F : Finset V, (∃ σ ∈ T, F ⊆ σ) → F.card = n + 1 → Odd (cellMult T F) →
        ∃ i < n + 2, ∀ v ∈ F, i ∉ car v) ∧
      IsSpernerTriangulation c car n (bdry car n T)

/-- The potential "doors": faces of size `n+1` carrying exactly the colours `0, …, n`. -/
def doors (c : V → ℕ) (n : ℕ) : Finset (Finset V) :=
  Finset.univ.filter (fun F => F.card = n + 1 ∧ F.image c = Finset.range (n + 1))

/-- Doors lying in an odd number of cells. -/
def oddDoors (c : V → ℕ) (n : ℕ) (T : Finset (Finset V)) : Finset (Finset V) :=
  (doors c n).filter (fun F => Odd (cellMult T F))

/-- Reduction of a natural number mod 2, expressed through parity. -/
lemma cast_zmod_two (m : ℕ) : (m : ZMod 2) = if Odd m then 1 else 0 := by
  have h2 : ((m % 2 : ℕ) : ZMod 2) = (m : ZMod 2) := ZMod.natCast_mod m 2
  rw [← h2]
  rcases Nat.even_or_odd m with h | h
  · rw [Nat.even_iff] at h; rw [h]; simp [Nat.odd_iff, h]
  · rw [Nat.odd_iff] at h; rw [h]; simp [Nat.odd_iff, h]

/-- The faces of size `n+1` of a cell `σ` of size `n+2` are exactly the sets `σ.erase v`. -/
theorem doors_in_cell_card (c : V → ℕ) (n : ℕ) (σ : Finset V) (hσ : σ.card = n + 2) :
    ((doors c n).filter (fun F => F ⊆ σ)).card
      = (σ.filter (fun v => (σ.erase v).image c = Finset.range (n + 1))).card := by
  symm
  apply Finset.card_bij (fun v _ => σ.erase v)
  · intro v hv
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨?_, Finset.erase_subset _ _⟩
    rw [doors, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, hv.2⟩
    rw [Finset.card_erase_of_mem hv.1, hσ]
    omega
  · intro v hv w hw h
    rw [Finset.mem_filter] at hv hw
    by_contra hne
    have hmem : v ∈ σ.erase w := Finset.mem_erase.2 ⟨hne, hv.1⟩
    rw [← h] at hmem
    exact (Finset.notMem_erase v σ) hmem
  · intro F hF
    rw [Finset.mem_filter, doors, Finset.mem_filter] at hF
    obtain ⟨⟨-, hcard, himg⟩, hsub⟩ := hF
    have hnsub : ¬ σ ⊆ F := by
      intro h
      have := Finset.card_le_card h
      omega
    obtain ⟨v, hvσ, hvF⟩ := Finset.not_subset.1 hnsub
    have hFe : F = σ.erase v := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        exact Finset.mem_erase.2 ⟨fun h => hvF (h ▸ hx), hsub hx⟩
      · rw [Finset.card_erase_of_mem hvσ, hσ, hcard]
        omega
    exact ⟨v, Finset.mem_filter.2 ⟨hvσ, by rw [← hFe, himg]⟩, hFe.symm⟩

omit [Fintype V] in
/-- A rainbow cell has exactly one door. -/
theorem rainbow_case (c : V → ℕ) (n : ℕ) (σ : Finset V) (hσ : σ.card = n + 2)
    (himg : σ.image c = Finset.range (n + 2)) :
    (σ.filter (fun v => (σ.erase v).image c = Finset.range (n + 1))).card = 1 := by
  have hinj : Set.InjOn c σ := by
    apply Finset.injOn_of_card_image_eq
    rw [himg, hσ, Finset.card_range]
  have herase : ∀ v ∈ σ, (σ.erase v).image c = (Finset.range (n + 2)).erase (c v) := by
    intro v hv
    ext j
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_range]
    constructor
    · rintro ⟨w, ⟨hwv, hwσ⟩, rfl⟩
      refine ⟨fun h => hwv (hinj hwσ hv h), ?_⟩
      have hc : c w ∈ σ.image c := Finset.mem_image_of_mem c hwσ
      rw [himg, Finset.mem_range] at hc
      exact hc
    · rintro ⟨hj, hjlt⟩
      have hj' : j ∈ σ.image c := by rw [himg, Finset.mem_range]; exact hjlt
      rw [Finset.mem_image] at hj'
      obtain ⟨w, hw, rfl⟩ := hj'
      exact ⟨w, ⟨fun h => hj (by rw [h]), hw⟩, rfl⟩
  have hfilter : σ.filter (fun v => (σ.erase v).image c = Finset.range (n + 1))
      = σ.filter (fun v => c v = n + 1) := by
    apply Finset.filter_congr
    intro v hv
    rw [herase v hv]
    constructor
    · intro h
      by_contra hne
      have h1 : n + 1 ∈ (Finset.range (n + 2)).erase (c v) :=
        Finset.mem_erase.2 ⟨fun hh => hne hh.symm, Finset.mem_range.2 (by omega)⟩
      rw [h, Finset.mem_range] at h1
      omega
    · intro h
      rw [h]
      ext j
      simp only [Finset.mem_erase, Finset.mem_range]
      omega
  rw [hfilter]
  have hn : (n + 1) ∈ σ.image c := by rw [himg, Finset.mem_range]; omega
  rw [Finset.mem_image] at hn
  obtain ⟨v₀, hv₀, hcv₀⟩ := hn
  rw [Finset.card_eq_one]
  refine ⟨v₀, ?_⟩
  ext w
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hw, hcw⟩
    exact hinj hw hv₀ (by rw [hcw, hcv₀])
  · rintro rfl
    exact ⟨hv₀, hcv₀⟩

omit [Fintype V] in
/-- A non-rainbow cell has either no door or exactly two doors. -/
theorem nonrainbow_case (c : V → ℕ) (n : ℕ) (σ : Finset V) (hσ : σ.card = n + 2)
    (hcol : ∀ v ∈ σ, c v < n + 2) (hne : σ.image c ≠ Finset.range (n + 2)) :
    (σ.filter (fun v => (σ.erase v).image c = Finset.range (n + 1))).card = 0 ∨
      (σ.filter (fun v => (σ.erase v).image c = Finset.range (n + 1))).card = 2 := by
  by_cases hsub : Finset.range (n + 1) ⊆ σ.image c
  · right
    have hnotmem : (n + 1) ∉ σ.image c := by
      intro hmem
      apply hne
      apply Finset.Subset.antisymm
      · intro j hj
        rw [Finset.mem_image] at hj
        obtain ⟨w, hw, rfl⟩ := hj
        exact Finset.mem_range.2 (hcol w hw)
      · intro j hj
        rw [Finset.mem_range] at hj
        rcases Nat.lt_or_ge j (n + 1) with h | h
        · exact hsub (Finset.mem_range.2 h)
        · have hj' : j = n + 1 := by omega
          rw [hj']; exact hmem
    have himg : σ.image c = Finset.range (n + 1) := by
      apply Finset.Subset.antisymm _ hsub
      intro j hj
      have hj2 : j < n + 2 := by
        rw [Finset.mem_image] at hj
        obtain ⟨w, hw, rfl⟩ := hj
        exact hcol w hw
      have : j ≠ n + 1 := fun h => hnotmem (h ▸ hj)
      exact Finset.mem_range.2 (by omega)
    have hkey : ∀ v ∈ σ, ((σ.erase v).image c = Finset.range (n + 1) ↔
        ∃ w ∈ σ, w ≠ v ∧ c w = c v) := by
      intro v hv
      constructor
      · intro h
        have hcv : c v ∈ Finset.range (n + 1) := by
          rw [← himg]; exact Finset.mem_image_of_mem c hv
        rw [← h, Finset.mem_image] at hcv
        obtain ⟨w, hw, hcw⟩ := hcv
        rw [Finset.mem_erase] at hw
        exact ⟨w, hw.2, hw.1, hcw⟩
      · rintro ⟨w, hwσ, hwv, hcw⟩
        apply Finset.Subset.antisymm
        · intro j hj
          rw [Finset.mem_image] at hj
          obtain ⟨u, hu, rfl⟩ := hj
          rw [← himg]
          exact Finset.mem_image_of_mem c (Finset.mem_of_mem_erase hu)
        · intro j hj
          rw [← himg, Finset.mem_image] at hj
          obtain ⟨u, hu, rfl⟩ := hj
          by_cases huv : u = v
          · subst huv
            exact Finset.mem_image.2 ⟨w, Finset.mem_erase.2 ⟨hwv, hwσ⟩, hcw⟩
          · exact Finset.mem_image.2 ⟨u, Finset.mem_erase.2 ⟨huv, hu⟩, rfl⟩
    obtain ⟨v₁, hv₁, v₂, hv₂, hv₁₂, hc₁₂⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to
        (t := Finset.range (n + 1)) (by rw [hσ, Finset.card_range]; omega)
        (fun a ha => by rw [← himg]; exact Finset.mem_image_of_mem c ha)
    have himg1 : (σ.erase v₁).image c = Finset.range (n + 1) :=
      (hkey v₁ hv₁).2 ⟨v₂, hv₂, hv₁₂.symm, hc₁₂.symm⟩
    have hinj1 : Set.InjOn c (σ.erase v₁) := by
      apply Finset.injOn_of_card_image_eq
      rw [himg1, Finset.card_erase_of_mem hv₁, hσ, Finset.card_range]
      omega
    have hfil : σ.filter (fun v => (σ.erase v).image c = Finset.range (n + 1)) = {v₁, v₂} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hv, hvi⟩
        obtain ⟨w, hwσ, hwv, hcw⟩ := (hkey v hv).1 hvi
        by_contra hcon
        push_neg at hcon
        obtain ⟨hvv₁, hvv₂⟩ := hcon
        by_cases hwv₁ : w = v₁
        · subst hwv₁
          exact hvv₂ (hinj1 (Finset.mem_erase.2 ⟨hvv₁, hv⟩)
            (Finset.mem_erase.2 ⟨hv₁₂.symm, hv₂⟩) (by rw [← hcw, hc₁₂]))
        · exact hwv (hinj1 (Finset.mem_erase.2 ⟨hwv₁, hwσ⟩)
            (Finset.mem_erase.2 ⟨hvv₁, hv⟩) hcw)
      · intro h
        rcases h with h | h
        · rw [h]; exact ⟨hv₁, himg1⟩
        · rw [h]; exact ⟨hv₂, (hkey v₂ hv₂).2 ⟨v₁, hv₁, hv₁₂, hc₁₂⟩⟩
    rw [hfil, Finset.card_insert_of_notMem (by simpa using hv₁₂), Finset.card_singleton]
  · left
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v hv h
    exact hsub (h ▸ Finset.image_subset_image (Finset.erase_subset v σ))

/-- A cell of dimension `n+1` contains an odd number of doors iff it is rainbow. -/
theorem odd_doors_in_cell (c : V → ℕ) (n : ℕ) (σ : Finset V) (hσ : σ.card = n + 2)
    (hcol : ∀ v ∈ σ, c v < n + 2) :
    (Odd ((doors c n).filter (fun F => F ⊆ σ)).card ↔ σ.image c = Finset.range (n + 2)) := by
  rw [doors_in_cell_card c n σ hσ]
  constructor
  · intro h
    by_contra hne
    rw [Nat.odd_iff] at h
    rcases nonrainbow_case c n σ hσ hcol hne with h0 | h2 <;> omega
  · intro h
    rw [rainbow_case c n σ hσ h]
    exact odd_one

/-- Double counting: mod 2, the number of rainbow cells equals the number of odd doors. -/
theorem rainbow_card_eq_oddDoors_card (c : V → ℕ) (n : ℕ) (T : Finset (Finset V))
    (hσ : ∀ σ ∈ T, σ.card = n + 2) (hcol : ∀ σ ∈ T, ∀ v ∈ σ, c v < n + 2) :
    ((rainbowCells c (n + 1) T).card : ZMod 2) = ((oddDoors c n T).card : ZMod 2) := by
  -- double counting the incidences between cells and the doors they contain
  have key : ∑ σ ∈ T, (((doors c n).filter (fun F => F ⊆ σ)).card)
      = ∑ F ∈ doors c n, ((T.filter (fun σ => F ⊆ σ)).card) := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hL : ((∑ σ ∈ T, (((doors c n).filter (fun F => F ⊆ σ)).card) : ℕ) : ZMod 2)
      = ((rainbowCells c (n + 1) T).card : ZMod 2) := by
    rw [Nat.cast_sum]
    have hterm : ∀ σ ∈ T, (((((doors c n).filter (fun F => F ⊆ σ)).card) : ℕ) : ZMod 2)
        = if σ.image c = Finset.range (n + 2) then 1 else 0 := by
      intro τ hτ
      rw [cast_zmod_two]
      by_cases h : τ.image c = Finset.range (n + 2)
      · rw [if_pos ((odd_doors_in_cell c n τ (hσ τ hτ) (hcol τ hτ)).2 h), if_pos h]
      · rw [if_neg (fun hh => h ((odd_doors_in_cell c n τ (hσ τ hτ) (hcol τ hτ)).1 hh)), if_neg h]
    rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
    simp [rainbowCells]
  have hR : ((∑ F ∈ doors c n, ((T.filter (fun σ => F ⊆ σ)).card) : ℕ) : ZMod 2)
      = ((oddDoors c n T).card : ZMod 2) := by
    rw [Nat.cast_sum]
    have hterm : ∀ F ∈ doors c n, ((((T.filter (fun σ => F ⊆ σ)).card) : ℕ) : ZMod 2)
        = if Odd (cellMult T F) then 1 else 0 := fun F _ => cast_zmod_two _
    rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
    simp [oddDoors]
  rw [← hL, key, hR]

/-- The rainbow cells of the induced boundary triangulation are exactly the odd doors. -/
theorem rainbowCells_bdry (c : V → ℕ) (car : V → Finset ℕ) (n : ℕ) (T : Finset (Finset V))
    (hcol : ∀ σ ∈ T, ∀ v ∈ σ, c v ∈ car v ∧ car v ⊆ Finset.range (n + 2))
    (hbd : ∀ F : Finset V, (∃ σ ∈ T, F ⊆ σ) → F.card = n + 1 → Odd (cellMult T F) →
        ∃ i < n + 2, ∀ v ∈ F, i ∉ car v) :
    rainbowCells c n (bdry car n T) = oddDoors c n T := by
  ext F
  simp only [rainbowCells, bdry, oddDoors, doors, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hcard, _, hodd⟩, himg⟩
    exact ⟨⟨hcard, himg⟩, hodd⟩
  · rintro ⟨⟨hcard, himg⟩, hodd⟩
    -- `F` lies in some cell
    have hne : (T.filter (fun σ => F ⊆ σ)).Nonempty := by
      rw [← Finset.card_pos]
      have : cellMult T F ≠ 0 := by
        intro h
        rw [Nat.odd_iff, h] at hodd
        exact absurd hodd (by norm_num)
      exact Nat.pos_of_ne_zero this
    obtain ⟨σ, hσ⟩ := hne
    rw [Finset.mem_filter] at hσ
    obtain ⟨i, hi, hcar⟩ := hbd F ⟨σ, hσ.1, hσ.2⟩ hcard hodd
    -- the missing colour must be `n+1`
    have hin : i = n + 1 := by
      by_contra hne'
      have hi' : i ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
      rw [← himg, Finset.mem_image] at hi'
      obtain ⟨v, hv, hcv⟩ := hi'
      exact hcar v hv (hcv ▸ (hcol σ hσ.1 v (hσ.2 hv)).1)
    refine ⟨⟨hcard, ?_, hodd⟩, himg⟩
    intro v hv j hj
    have h1 : j ∈ Finset.range (n + 2) := (hcol σ hσ.1 v (hσ.2 hv)).2 hj
    have h2 : j ≠ n + 1 := by
      rintro rfl
      exact hcar v hv (hin ▸ hj)
    rw [Finset.mem_range] at h1 ⊢
    omega

/-- **Sperner's lemma**: every Sperner colouring of a triangulated `n`-simplex has an odd
number of rainbow cells. -/
theorem sperner_lemma (c : V → ℕ) (car : V → Finset ℕ) (n : ℕ) (T : Finset (Finset V))
    (h : IsSpernerTriangulation c car n T) : Odd (rainbowCells c n T).card := by
  induction n generalizing T with
  | zero =>
      obtain ⟨v, rfl, hv⟩ := h
      have : rainbowCells c 0 ({{v}} : Finset (Finset V)) = {{v}} := by
        unfold rainbowCells
        rw [Finset.filter_eq_self]
        intro σ hσ
        rw [Finset.mem_singleton] at hσ
        subst hσ
        simp [hv, Finset.range_one]
      rw [this]
      simp
  | succ n ih =>
      obtain ⟨hcard, hcol, hbd, hrec⟩ := h
      have hIH : Odd (rainbowCells c n (bdry car n T)).card := ih _ hrec
      rw [rainbowCells_bdry c car n T hcol hbd] at hIH
      have hcol' : ∀ σ ∈ T, ∀ v ∈ σ, c v < n + 2 := by
        intro σ hσ v hv
        have := (hcol σ hσ v hv).2 (hcol σ hσ v hv).1
        simpa using this
      have hpar := rainbow_card_eq_oddDoors_card c n T hcard hcol'
      have hmod : (rainbowCells c (n + 1) T).card ≡ (oddDoors c n T).card [MOD 2] :=
        (ZMod.natCast_eq_natCast_iff _ _ _).1 hpar
      rw [Nat.odd_iff] at hIH ⊢
      rw [Nat.ModEq] at hmod
      omega

/-!
### Sanity checks

The notion of a Sperner triangulation used above is not vacuous: it is satisfied both by
genuinely subdivided triangulations and, in every dimension, by the undivided simplex.
-/

/-- The `k`-dimensional face of the standard simplex, inside `Fin (N+1)`. -/
def stdFace (N k : ℕ) : Finset (Fin (N + 1)) := Finset.univ.filter (fun i => (i : ℕ) < k + 1)

lemma mem_stdFace {N k : ℕ} {i : Fin (N + 1)} : i ∈ stdFace N k ↔ (i : ℕ) < k + 1 := by
  simp [stdFace]

lemma card_stdFace (N k : ℕ) (h : k ≤ N) : (stdFace N k).card = k + 1 := by
  rw [← Finset.card_range (k + 1)]
  apply Finset.card_bij (fun (i : Fin (N + 1)) _ => (i : ℕ))
  · intro a ha; exact Finset.mem_range.2 (mem_stdFace.1 ha)
  · intro a _ b _ hab; exact Fin.ext hab
  · intro b hb
    rw [Finset.mem_range] at hb
    exact ⟨⟨b, by omega⟩, mem_stdFace.2 (by simpa using hb), rfl⟩

lemma stdFace_mono (N k : ℕ) : stdFace N k ⊆ stdFace N (k + 1) := by
  intro v hv
  rw [mem_stdFace] at hv ⊢
  omega

/-- Non-vacuity: for every `k ≤ N` the undivided `k`-simplex, with vertices coloured by their
index, is a Sperner triangulation. -/
theorem isSpernerTriangulation_std (N : ℕ) (k : ℕ) (hk : k ≤ N) :
    IsSpernerTriangulation (V := Fin (N + 1)) (fun i => (i : ℕ)) (fun i => {(i : ℕ)}) k
      {stdFace N k} := by
  induction k with
  | zero =>
      refine ⟨0, ?_, rfl⟩
      congr 1
      ext i
      simp only [stdFace, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        Fin.ext_iff, Fin.val_zero]
      omega
  | succ k ih =>
      have hk' : k ≤ N := by omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro σ hσ
        rw [Finset.mem_singleton] at hσ
        subst hσ
        exact card_stdFace N (k + 1) hk
      · intro σ hσ v hv
        rw [Finset.mem_singleton] at hσ
        subst hσ
        rw [mem_stdFace] at hv
        refine ⟨Finset.mem_singleton_self _, ?_⟩
        rw [Finset.singleton_subset_iff, Finset.mem_range]
        omega
      · intro F hF hcard _
        obtain ⟨σ, hσ, hFσ⟩ := hF
        rw [Finset.mem_singleton] at hσ
        subst hσ
        have hns : ¬ stdFace N (k + 1) ⊆ F := by
          intro hsub
          have h1 := Finset.card_le_card hsub
          rw [card_stdFace N (k + 1) hk, hcard] at h1
          omega
        obtain ⟨j, hj, hjF⟩ := Finset.not_subset.1 hns
        refine ⟨(j : ℕ), mem_stdFace.1 hj, ?_⟩
        intro v hv hmem
        rw [Finset.mem_singleton] at hmem
        exact hjF (by rwa [Fin.ext hmem.symm] at hv)
      · have hbd : bdry (fun i : Fin (N + 1) => ({(i : ℕ)} : Finset ℕ)) k {stdFace N (k + 1)}
            = {stdFace N k} := by
          ext F
          simp only [bdry, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro ⟨hcard, hcar, -⟩
            have hsub : F ⊆ stdFace N k := by
              intro v hv
              have h1 := hcar v hv
              rw [Finset.singleton_subset_iff, Finset.mem_range] at h1
              exact mem_stdFace.2 h1
            exact Finset.eq_of_subset_of_card_le hsub (by rw [card_stdFace N k hk', hcard])
          · rintro rfl
            refine ⟨card_stdFace N k hk', ?_, ?_⟩
            · intro v hv
              rw [mem_stdFace] at hv
              rw [Finset.singleton_subset_iff, Finset.mem_range]
              omega
            · have h1 : cellMult {stdFace N (k + 1)} (stdFace N k) = 1 := by
                unfold cellMult
                rw [Finset.filter_singleton, if_pos (stdFace_mono N k)]
                simp
              rw [h1]
              exact odd_one
        rw [hbd]
        exact ih hk'

/-- A segment `A B` coloured `0, 1`, subdivided by a midpoint coloured `0`. -/
def segColour : Fin 3 → ℕ := ![0, 0, 1]

/-- Carriers for `segColour`: the two endpoints, and the interior midpoint. -/
def segCarrier : Fin 3 → Finset ℕ := ![{0}, {0, 1}, {1}]

/-- The two cells of the subdivided segment. -/
def segCells : Finset (Finset (Fin 3)) := {{0, 1}, {1, 2}}

theorem segment_isSpernerTriangulation :
    IsSpernerTriangulation segColour segCarrier 1 segCells := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  exact ⟨0, by decide, by decide⟩

theorem segment_rainbow_card : (rainbowCells segColour 1 segCells).card = 1 := by decide

/-- A triangle `A B C` coloured `0, 1, 2`, subdivided by a point `M` on the edge `A B`
coloured `1`. -/
def triColour : Fin 4 → ℕ := ![0, 1, 2, 1]

/-- Carriers for `triColour`: three corners and a point in the interior of the edge `A B`. -/
def triCarrier : Fin 4 → Finset ℕ := ![{0}, {1}, {2}, {0, 1}]

/-- The two cells of the subdivided triangle. -/
def triCells : Finset (Finset (Fin 4)) := {{0, 2, 3}, {1, 2, 3}}

theorem triangle_isSpernerTriangulation :
    IsSpernerTriangulation triColour triCarrier 2 triCells := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  refine ⟨by decide, by decide, by decide, ?_⟩
  exact ⟨0, by decide, by decide⟩

theorem triangle_rainbow_card : (rainbowCells triColour 2 triCells).card = 1 := by decide

end Math

