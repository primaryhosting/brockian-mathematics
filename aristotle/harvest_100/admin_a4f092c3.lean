/-
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open Finset

variable {V : Type*} [DecidableEq V]

/-- The number of cells of `K` that contain the face `τ`. -/
def deg (K : Finset (Finset V)) (τ : Finset V) : ℕ :=
  (K.filter (fun σ => τ ⊆ σ)).card

/-- All `k`-element faces of the cells of `K`. -/
def faces (K : Finset (Finset V)) (k : ℕ) : Finset (Finset V) :=
  K.biUnion (fun σ => Finset.powersetCard k σ)

/-- The sub-complex of `K` consisting of the boundary faces lying in the facet
opposite to the vertex `n + 1`: the `(n+1)`-element faces contained in a unique cell
and all of whose vertices have carrier avoiding the index `n + 1`. -/
def bdry (s : V → Finset ℕ) (K : Finset (Finset V)) (n : ℕ) : Finset (Finset V) :=
  (faces K (n + 1)).filter (fun τ => deg K τ = 1 ∧ ∀ v ∈ τ, (n + 1) ∉ s v)

/-- `IsTri s n K` says that `K` is (the set of top-dimensional cells of) a triangulation of the
`n`-dimensional simplex, where each vertex `v` carries the set `s v ⊆ {0, …, n}` of barycentric
coordinates in which it is supported (its *carrier face*).

The axioms are the standard combinatorial (pseudo-manifold) properties of a triangulation
of a simplex:
* every cell has `n + 1` vertices;
* every vertex is supported inside `{0, …, n}`;
* every `n`-element face lies in one or two cells;
* a face lying in exactly one cell is a boundary face, hence lies in some facet `{x_i = 0}`;
* the boundary faces lying in the last facet form a triangulation of the `(n-1)`-simplex.

A triangulation of the `0`-simplex is a single vertex. -/
def IsTri (s : V → Finset ℕ) : ℕ → Finset (Finset V) → Prop
  | 0, K => ∃ v : V, K = {({v} : Finset V)} ∧ s v ⊆ range 1
  | (n + 1), K =>
      (∀ σ ∈ K, σ.card = n + 2) ∧
      (∀ σ ∈ K, ∀ v ∈ σ, s v ⊆ range (n + 2)) ∧
      (∀ τ ∈ faces K (n + 1), deg K τ = 1 ∨ deg K τ = 2) ∧
      (∀ τ ∈ faces K (n + 1), deg K τ = 1 → ∃ i ∈ range (n + 2), ∀ v ∈ τ, i ∉ s v) ∧
      IsTri s n (bdry s K n)

/-- The cells of `K` that are *rainbow*: their vertices carry all of the `n + 1` colours. -/
def rainbowCells (c : V → ℕ) (n : ℕ) (K : Finset (Finset V)) : Finset (Finset V) :=
  K.filter (fun σ => σ.image c = range (n + 1))

/-! ### Counting the doors of a single cell -/

/-- The "doors" of a cell `σ`: the `(n+1)`-element faces carrying exactly the colours
`{0, …, n}`. -/
def doorsOf (c : V → ℕ) (n : ℕ) (σ : Finset V) : Finset (Finset V) :=
  (Finset.powersetCard (n + 1) σ).filter (fun τ => τ.image c = range (n + 1))

/-- Faces of codimension one inside `σ` are exactly the sets `σ.erase x` for `x ∈ σ`. -/
theorem card_filter_powersetCard_pred (σ : Finset V) (P : Finset V → Prop) [DecidablePred P]
    (k : ℕ) (hcard : σ.card = k + 1) :
    ((Finset.powersetCard k σ).filter P).card = (σ.filter (fun x => P (σ.erase x))).card := by
  refine (Finset.card_bij (fun x _ => σ.erase x) ?_ ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hx ⊢
    refine ⟨⟨Finset.erase_subset _ _, ?_⟩, hx.2⟩
    rw [Finset.card_erase_of_mem hx.1, hcard]
    omega
  · intro x hx y hy hxy
    simp only [Finset.mem_filter] at hx hy
    dsimp only at hxy
    by_contra hne
    have hmem : x ∈ σ.erase y := Finset.mem_erase.2 ⟨hne, hx.1⟩
    rw [← hxy] at hmem
    exact (Finset.notMem_erase x σ) hmem
  · intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hτ
    obtain ⟨⟨hsub, hc⟩, hP⟩ := hτ
    have h1 : (σ \ τ).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.2 hsub, hcard, hc]
      omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 h1
    have hxmem : x ∈ σ \ τ := by rw [hx]; exact Finset.mem_singleton_self x
    have hxσ : x ∈ σ := (Finset.mem_sdiff.1 hxmem).1
    have hxτ : x ∉ τ := (Finset.mem_sdiff.1 hxmem).2
    have hτe : τ = σ.erase x := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        exact Finset.mem_erase.2 ⟨by rintro rfl; exact hxτ hy, hsub hy⟩
      · rw [Finset.card_erase_of_mem hxσ, hcard, hc]
        omega
    refine ⟨x, ?_, hτe.symm⟩
    simp only [Finset.mem_filter]
    exact ⟨hxσ, hτe ▸ hP⟩

/-- A rainbow cell has exactly one door. -/
theorem doors_of_rainbow (c : V → ℕ) (n : ℕ) (σ : Finset V) (hcard : σ.card = n + 2)
    (himg : σ.image c = range (n + 2)) : (doorsOf c n σ).card = 1 := by
  rw [doorsOf, card_filter_powersetCard_pred σ _ (n + 1) hcard]
  have hinj : Set.InjOn c σ := by
    apply Finset.injOn_of_card_image_eq
    rw [himg, hcard, Finset.card_range]
  have hkey : ∀ x ∈ σ, ((σ.erase x).image c = range (n + 1) ↔ c x = n + 1) := by
    intro x hx
    constructor
    · intro he
      by_contra hne
      have hmem : (n + 1) ∈ σ.image c := by rw [himg]; simp
      obtain ⟨y, hy, hcy⟩ := Finset.mem_image.1 hmem
      have hyx : y ≠ x := by rintro rfl; exact hne hcy
      have hmem' : (n + 1) ∈ (σ.erase x).image c :=
        Finset.mem_image.2 ⟨y, Finset.mem_erase.2 ⟨hyx, hy⟩, hcy⟩
      rw [he] at hmem'
      simp at hmem'
    · intro hcx
      ext k
      simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_range]
      constructor
      · rintro ⟨y, ⟨hyx, hy⟩, rfl⟩
        have h1 : c y ∈ range (n + 2) := by rw [← himg]; exact Finset.mem_image_of_mem c hy
        rw [Finset.mem_range] at h1
        have h2 : c y ≠ n + 1 := by
          rw [← hcx]; intro h; exact hyx (hinj hy hx h)
        omega
      · intro hk
        have hmem : k ∈ σ.image c := by rw [himg, Finset.mem_range]; omega
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hmem
        refine ⟨y, ⟨?_, hy⟩, rfl⟩
        rintro rfl
        omega
  rw [Finset.card_eq_one]
  have hmem : (n + 1) ∈ σ.image c := by rw [himg]; simp
  obtain ⟨x0, hx0, hcx0⟩ := Finset.mem_image.1 hmem
  refine ⟨x0, ?_⟩
  ext y
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hy, hey⟩
    exact hinj hy hx0 (((hkey y hy).1 hey).trans hcx0.symm)
  · rintro rfl
    exact ⟨hx0, (hkey _ hx0).2 hcx0⟩

/-- A cell carrying exactly the colours `{0, …, n}` has exactly two doors. -/
theorem doors_of_almost (c : V → ℕ) (n : ℕ) (σ : Finset V) (hcard : σ.card = n + 2)
    (himg : σ.image c = range (n + 1)) : (doorsOf c n σ).card = 2 := by
  rw [doorsOf, card_filter_powersetCard_pred σ _ (n + 1) hcard]
  have hlt : (σ.image c).card < σ.card := by
    rw [himg, hcard, Finset.card_range]; omega
  obtain ⟨x, hx, y, hy, hne, hcxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt (fun a ha => Finset.mem_image_of_mem c ha)
  have hdup : ∀ z ∈ σ, ∀ w ∈ σ, w ≠ z → c w = c z → (σ.erase z).image c = σ.image c := by
    intro z _ w hw hwz hcw
    apply Finset.Subset.antisymm
    · exact Finset.image_subset_image (Finset.erase_subset _ _)
    · intro k hk
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hk
      by_cases huz : u = z
      · subst huz
        exact Finset.mem_image.2 ⟨w, Finset.mem_erase.2 ⟨hwz, hw⟩, hcw⟩
      · exact Finset.mem_image.2 ⟨u, Finset.mem_erase.2 ⟨huz, hu⟩, rfl⟩
  have hfilter : σ.filter (fun z => (σ.erase z).image c = range (n + 1)) = {x, y} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hez⟩
      by_contra hcon
      push_neg at hcon
      obtain ⟨hzx, hzy⟩ := hcon
      have hxe : x ∈ σ.erase z := Finset.mem_erase.2 ⟨fun h => hzx h.symm, hx⟩
      have hye : y ∈ σ.erase z := Finset.mem_erase.2 ⟨fun h => hzy h.symm, hy⟩
      have hcard' : (σ.erase z).card = n + 1 := by
        rw [Finset.card_erase_of_mem hz, hcard]
        omega
      have hinj : Set.InjOn c (σ.erase z) := by
        apply Finset.injOn_of_card_image_eq
        rw [hez, hcard', Finset.card_range]
      exact hne (hinj hxe hye hcxy)
    · rintro (rfl | rfl)
      · exact ⟨hx, (hdup z hx y hy (fun h => hne h.symm) hcxy.symm).trans himg⟩
      · exact ⟨hy, (hdup z hy x hx hne hcxy).trans himg⟩
  rw [hfilter, Finset.card_pair hne]

omit [DecidableEq V] in
/-- A cell missing one of the colours `{0, …, n}` has no door. -/
theorem doors_of_other (c : V → ℕ) (n : ℕ) (σ : Finset V)
    (himg : ¬ range (n + 1) ⊆ σ.image c) : (doorsOf c n σ).card = 0 := by
  rw [Finset.card_eq_zero, doorsOf, Finset.filter_eq_empty_iff]
  intro τ hτ hcon
  apply himg
  rw [← hcon]
  exact Finset.image_subset_image (Finset.mem_powersetCard.1 hτ).1

/-- A cell has an odd number of doors exactly when it is rainbow. -/
theorem doors_parity (c : V → ℕ) (n : ℕ) (σ : Finset V) (hcard : σ.card = n + 2)
    (hsub : σ.image c ⊆ range (n + 2)) :
    (doorsOf c n σ).card % 2 = if σ.image c = range (n + 2) then 1 else 0 := by
  by_cases hcov : range (n + 1) ⊆ σ.image c
  · by_cases hn : (n + 1) ∈ σ.image c
    · have himg : σ.image c = range (n + 2) := by
        refine Finset.Subset.antisymm hsub ?_
        intro k hk
        rw [Finset.mem_range] at hk
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
        · exact hcov (Finset.mem_range.2 h)
        · rw [h]; exact hn
      rw [doors_of_rainbow c n σ hcard himg, if_pos himg]
    · have himg : σ.image c = range (n + 1) := by
        refine Finset.Subset.antisymm ?_ hcov
        intro k hk
        have hk' : k ∈ range (n + 2) := hsub hk
        rw [Finset.mem_range] at hk' ⊢
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with h | h
        · exact h
        · exact absurd (h ▸ hk) hn
      have hne : σ.image c ≠ range (n + 2) := by
        rw [himg]
        intro hcon
        apply hn
        rw [himg, hcon]
        simp
      rw [doors_of_almost c n σ hcard himg, if_neg hne]
  · have hne : σ.image c ≠ range (n + 2) := by
      intro hcon
      apply hcov
      rw [hcon]
      intro k hk
      rw [Finset.mem_range] at hk ⊢
      omega
    rw [doors_of_other c n σ hcov, if_neg hne]

/-! ### The main theorem -/

/-- **Sperner's lemma.** For any triangulation `K` of the `n`-simplex and any Sperner colouring
`c` (each vertex `v` receives a colour `c v` belonging to its carrier face `s v`), the number of
rainbow cells — cells whose vertices carry all `n + 1` colours — is odd. -/
theorem sperner_lemma (s : V → Finset ℕ) (c : V → ℕ) (hc : ∀ v, c v ∈ s v)
    (n : ℕ) (K : Finset (Finset V)) (h : IsTri s n K) :
    Odd (rainbowCells c n K).card := by
  induction n generalizing K with
  | zero =>
    obtain ⟨v, rfl, hsv⟩ := h
    have hcv : c v = 0 := by
      have hmem := hsv (hc v)
      simpa using hmem
    have hrc : rainbowCells c 0 {({v} : Finset V)} = {({v} : Finset V)} := by
      rw [rainbowCells, Finset.filter_true_of_mem]
      intro σ hσ
      rw [Finset.mem_singleton] at hσ
      subst hσ
      simp [hcv, Finset.range_one]
    rw [hrc]
    simp
  | succ n ih =>
    obtain ⟨hcards, hsupp, hdeg, hbd, hind⟩ := h
    set D := (faces K (n + 1)).filter (fun τ => τ.image c = range (n + 1)) with hD
    have hdoors : ∀ σ ∈ K, doorsOf c n σ = D.filter (fun τ => τ ⊆ σ) := by
      intro σ hσ
      ext τ
      simp only [doorsOf, hD, faces, Finset.mem_filter, Finset.mem_powersetCard,
        Finset.mem_biUnion]
      constructor
      · rintro ⟨⟨hts, htc⟩, hti⟩
        exact ⟨⟨⟨σ, hσ, hts, htc⟩, hti⟩, hts⟩
      · rintro ⟨⟨⟨σ', hσ', hmem⟩, hti⟩, hts⟩
        exact ⟨⟨hts, hmem.2⟩, hti⟩
    have hsum : ∑ σ ∈ K, (doorsOf c n σ).card = ∑ τ ∈ D, deg K τ := by
      calc ∑ σ ∈ K, (doorsOf c n σ).card
          = ∑ σ ∈ K, ∑ τ ∈ D, (if τ ⊆ σ then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro σ hσ
            rw [hdoors σ hσ, Finset.card_filter]
        _ = ∑ τ ∈ D, ∑ σ ∈ K, (if τ ⊆ σ then 1 else 0) := Finset.sum_comm
        _ = ∑ τ ∈ D, deg K τ := by
            refine Finset.sum_congr rfl ?_
            intro τ _
            rw [deg, Finset.card_filter]
    have hL : (∑ σ ∈ K, (doorsOf c n σ).card) % 2 = (rainbowCells c (n + 1) K).card % 2 := by
      rw [Finset.sum_nat_mod]
      have hpar : ∀ σ ∈ K, (doorsOf c n σ).card % 2 =
          if σ.image c = range (n + 2) then 1 else 0 := by
        intro σ hσ
        refine doors_parity c n σ (hcards σ hσ) ?_
        intro k hk
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hk
        exact hsupp σ hσ v hv (hc v)
      rw [Finset.sum_congr rfl hpar, Finset.sum_boole]
      simp [rainbowCells]
    have hR : (∑ τ ∈ D, deg K τ) % 2 = (D.filter (fun τ => deg K τ = 1)).card % 2 := by
      rw [Finset.sum_nat_mod]
      have hpar : ∀ τ ∈ D, deg K τ % 2 = if deg K τ = 1 then 1 else 0 := by
        intro τ hτ
        have hf : τ ∈ faces K (n + 1) := (Finset.mem_filter.1 hτ).1
        rcases hdeg τ hf with h1 | h2
        · simp [h1]
        · simp [h2]
      rw [Finset.sum_congr rfl hpar, Finset.sum_boole]
      simp
    have hEq : D.filter (fun τ => deg K τ = 1) = rainbowCells c n (bdry s K n) := by
      ext τ
      simp only [hD, rainbowCells, bdry, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hf, hi⟩, h1⟩
        refine ⟨⟨hf, h1, ?_⟩, hi⟩
        obtain ⟨i, hi', hfac⟩ := hbd τ hf h1
        have hin : i = n + 1 := by
          rw [Finset.mem_range] at hi'
          by_contra hnei
          have hmem : i ∈ range (n + 1) := Finset.mem_range.2 (by omega)
          rw [← hi] at hmem
          obtain ⟨v, hv, hcv⟩ := Finset.mem_image.1 hmem
          exact hfac v hv (hcv ▸ hc v)
        rw [← hin]
        exact hfac
      · rintro ⟨⟨hf, h1, _⟩, hi⟩
        exact ⟨⟨hf, hi⟩, h1⟩
    have hodd := ih (bdry s K n) hind
    rw [← hEq, Nat.odd_iff] at hodd
    rw [Nat.odd_iff]
    omega

/-! ### A nondegenerate instance

To see that the hypotheses of `sperner_lemma` are satisfiable, here is the subdivision of the
`1`-simplex into the two segments `{0,1}` and `{1,2}`, with carriers `s 0 = {0}`,
`s 1 = {0,1}`, `s 2 = {1}`, coloured by `c 0 = c 1 = 0`, `c 2 = 1`.  It has exactly one
rainbow cell. -/
namespace Example

/-- Carrier faces of the three vertices of the subdivided `1`-simplex. -/
def carrier : ℕ → Finset ℕ
  | 0 => {0}
  | 1 => {0, 1}
  | _ => {1}

/-- A Sperner colouring of the subdivided `1`-simplex. -/
def colour : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | _ => 1

theorem isTri_example : IsTri carrier 1 ({{0, 1}, {1, 2}} : Finset (Finset ℕ)) :=
  ⟨by decide, by decide, by decide, by decide, ⟨0, by decide, by decide⟩⟩

theorem colour_mem_carrier : ∀ v, colour v ∈ carrier v := by
  intro v
  match v with
  | 0 => decide
  | 1 => decide
  | (_ + 2) => simp [colour, carrier]

theorem rainbow_example :
    (rainbowCells colour 1 ({{0, 1}, {1, 2}} : Finset (Finset ℕ))).card = 1 := by
  decide

example : Odd (rainbowCells colour 1 ({{0, 1}, {1, 2}} : Finset (Finset ℕ))).card :=
  sperner_lemma carrier colour colour_mem_carrier 1 _ isTri_example

/-! A two-dimensional instance: the triangle `{0,1,2}` subdivided by its barycentre `3` into the
three cells `{0,1,3}`, `{0,2,3}`, `{1,2,3}`, coloured by `c i = i` for `i < 3` and `c 3 = 0`. -/

/-- Carrier faces of the four vertices of the barycentrically subdivided triangle. -/
def carrier2 : ℕ → Finset ℕ
  | 0 => {0}
  | 1 => {1}
  | 2 => {2}
  | _ => {0, 1, 2}

/-- A Sperner colouring of the barycentrically subdivided triangle. -/
def colour2 : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

theorem isTri_example2 :
    IsTri carrier2 2 ({{0, 1, 3}, {0, 2, 3}, {1, 2, 3}} : Finset (Finset ℕ)) :=
  ⟨by decide, by decide, by decide, by decide,
    ⟨by decide, by decide, by decide, by decide, ⟨0, by decide, by decide⟩⟩⟩

theorem colour2_mem_carrier2 : ∀ v, colour2 v ∈ carrier2 v := by
  intro v
  match v with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | (_ + 3) => simp [colour2, carrier2]

theorem rainbow_example2 :
    (rainbowCells colour2 2 ({{0, 1, 3}, {0, 2, 3}, {1, 2, 3}} : Finset (Finset ℕ))).card = 1 := by
  decide

example : Odd (rainbowCells colour2 2 ({{0, 1, 3}, {0, 2, 3}, {1, 2, 3}} : Finset (Finset ℕ))).card :=
  sperner_lemma carrier2 colour2 colour2_mem_carrier2 2 _ isTri_example2

end Example

end Math

