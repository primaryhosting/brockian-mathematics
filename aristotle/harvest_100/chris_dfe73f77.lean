import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` lines to come first in a module, so the
required header block is placed immediately after the single `import Mathlib` line.
-/

namespace Math

open Finset

variable {V : Type*} [DecidableEq V]

/-! ### Codimension-one subsets -/

/-- Subsets of `S` of cardinality `S.card - 1` are exactly the sets `S.erase x` for `x ∈ S`;
hence counting them amounts to counting the vertices `x ∈ S` with the corresponding property. -/
lemma card_filter_powerset_erase (S : Finset V) (m : ℕ) (hS : S.card = m + 1)
    (P : Finset V → Prop) [DecidablePred P] :
    (S.powerset.filter (fun G => G.card = m ∧ P G)).card
      = (S.filter (fun x => P (S.erase x))).card := by
  have herase : ∀ x ∈ S, (S.erase x).card = m := by
    intro x hx
    rw [Finset.card_erase_of_mem hx, hS]
    omega
  have hinj : Set.InjOn (fun x => S.erase x) S := by
    intro x hx y hy h
    by_contra hne
    have hx' : x ∈ S.erase y := Finset.mem_erase.2 ⟨hne, hx⟩
    rw [← show S.erase x = S.erase y from h] at hx'
    exact Finset.notMem_erase x S hx'
  have hset : S.powerset.filter (fun G => G.card = m ∧ P G)
      = (S.filter (fun x => P (S.erase x))).image (fun x => S.erase x) := by
    ext G
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hGS, hGc, hGP⟩
      obtain ⟨x, hxS, hxG⟩ : ∃ x ∈ S, x ∉ G := by
        by_contra hcon
        push_neg at hcon
        have hsub : S ⊆ G := fun y hy => hcon y hy
        have := Finset.card_le_card hsub
        omega
      have hGe : G = S.erase x := by
        refine Finset.eq_of_subset_of_card_le ?_ ?_
        · intro y hy
          exact Finset.mem_erase.2 ⟨by rintro rfl; exact hxG hy, hGS hy⟩
        · rw [herase x hxS, hGc]
      exact ⟨x, ⟨hxS, hGe ▸ hGP⟩, hGe.symm⟩
    · rintro ⟨x, ⟨hxS, hxP⟩, rfl⟩
      exact ⟨Finset.erase_subset _ _, herase x hxS, hxP⟩
  rw [hset]
  refine Finset.card_image_of_injOn ?_
  intro x hx y hy h
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
  exact hinj hx.1 hy.1 h

/-! ### Images after deleting one vertex -/

lemma image_erase_of_injOn {color : V → ℕ} {S : Finset V} (hinj : Set.InjOn color S)
    {x : V} (hx : x ∈ S) :
    (S.erase x).image color = (S.image color).erase (color x) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨z, ⟨hzx, hzS⟩, rfl⟩
    exact ⟨fun h => hzx (hinj hzS hx h), z, hzS, rfl⟩
  · rintro ⟨hne, z, hzS, rfl⟩
    exact ⟨z, ⟨fun h => hne (by rw [h]), hzS⟩, rfl⟩

lemma image_erase_eq_iff_exists {color : V → ℕ} {S : Finset V} {x : V} (hx : x ∈ S) :
    (S.erase x).image color = S.image color ↔ ∃ y ∈ S, y ≠ x ∧ color y = color x := by
  constructor
  · intro h
    have hmem : color x ∈ (S.erase x).image color := by
      rw [h]; exact Finset.mem_image_of_mem _ hx
    obtain ⟨y, hy, hyc⟩ := Finset.mem_image.1 hmem
    rw [Finset.mem_erase] at hy
    exact ⟨y, hy.2, hy.1, hyc⟩
  · rintro ⟨y, hyS, hyx, hyc⟩
    refine Finset.Subset.antisymm (Finset.image_subset_image (Finset.erase_subset _ _)) ?_
    intro c hc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hc
    by_cases hzx : z = x
    · subst hzx
      exact Finset.mem_image.2 ⟨y, Finset.mem_erase.2 ⟨hyx, hyS⟩, hyc⟩
    · exact Finset.mem_image.2 ⟨z, Finset.mem_erase.2 ⟨hzx, hz⟩, rfl⟩

/-! ### The door-counting lemma -/

/-- **Door counting.**  Let `S` be a cell with `k+2` vertices whose colours lie in
`{0, …, k+1}`.  The number of codimension-one faces of `S` whose colour set is exactly
`{0, …, k}` (the "doors" of `S`) is odd precisely when `S` is rainbow. -/
lemma door_count (color : V → ℕ) (k : ℕ) (S : Finset V)
    (hcard : S.card = k + 2) (hsub : S.image color ⊆ Finset.range (k + 2)) :
    (S.filter (fun x => (S.erase x).image color = Finset.range (k + 1))).card % 2
      = if S.image color = Finset.range (k + 2) then 1 else 0 := by
  by_cases hrange : Finset.range (k + 1) ⊆ S.image color
  · by_cases hk1 : (k + 1) ∈ S.image color
    · -- `S` is rainbow: exactly one door
      have himg : S.image color = Finset.range (k + 2) := by
        refine Finset.Subset.antisymm hsub ?_
        intro y hy
        rw [Finset.mem_range] at hy
        rcases Nat.lt_succ_iff_lt_or_eq.1 hy with h | h
        · exact hrange (Finset.mem_range.2 h)
        · rw [h]; exact hk1
      have hcardimg : (S.image color).card = S.card := by
        rw [himg, hcard, Finset.card_range]
      have hinj : Set.InjOn color S := Finset.injOn_of_card_image_eq hcardimg
      have hfe : ∀ x ∈ S, ((S.erase x).image color = Finset.range (k + 1) ↔ color x = k + 1) := by
        intro x hx
        rw [image_erase_of_injOn hinj hx, himg]
        constructor
        · intro h
          by_contra hne
          have hmem : (k + 1) ∈ (Finset.range (k + 2)).erase (color x) :=
            Finset.mem_erase.2 ⟨fun hh => hne hh.symm, Finset.mem_range.2 (by omega)⟩
          rw [h, Finset.mem_range] at hmem
          omega
        · intro h
          rw [h]
          ext y
          simp only [Finset.mem_erase, Finset.mem_range]
          omega
      have hfilter : S.filter (fun x => (S.erase x).image color = Finset.range (k + 1))
          = S.filter (fun x => color x = k + 1) := Finset.filter_congr hfe
      obtain ⟨x0, hx0, hx0c⟩ : ∃ x0 ∈ S, color x0 = k + 1 := Finset.mem_image.1 hk1
      have hsingle : S.filter (fun x => color x = k + 1) = {x0} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hy, hyc⟩
          exact hinj hy hx0 (by rw [hyc, hx0c])
        · rintro rfl
          exact ⟨hx0, hx0c⟩
      rw [hfilter, hsingle, if_pos himg, Finset.card_singleton]
    · -- `S` misses the colour `k+1`: exactly two doors
      have himg : S.image color = Finset.range (k + 1) := by
        refine Finset.Subset.antisymm ?_ hrange
        intro y hy
        have hy2 := hsub hy
        rw [Finset.mem_range] at hy2 ⊢
        rcases Nat.lt_succ_iff_lt_or_eq.1 hy2 with h | h
        · exact h
        · exact absurd (h ▸ hy) hk1
      have hne : S.image color ≠ Finset.range (k + 2) := by
        rw [himg]
        intro h
        have hc := congrArg Finset.card h
        simp only [Finset.card_range] at hc
        omega
      have hcardlt : (S.image color).card < S.card := by
        rw [himg, hcard, Finset.card_range]
        omega
      obtain ⟨u, hu, v, hv, huv, hcuv⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcardlt
          (f := color) (fun a ha => Finset.mem_image_of_mem color ha)
      have himgeu : (S.erase u).image color = S.image color :=
        (image_erase_eq_iff_exists hu).2 ⟨v, hv, huv.symm, hcuv.symm⟩
      have hinj' : Set.InjOn color (S.erase u) := by
        apply Finset.injOn_of_card_image_eq
        rw [himgeu, himg, Finset.card_erase_of_mem hu, hcard, Finset.card_range]
        omega
      have hve : v ∈ S.erase u := Finset.mem_erase.2 ⟨huv.symm, hv⟩
      have hfilter : S.filter (fun x => (S.erase x).image color = Finset.range (k + 1))
          = {u, v} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hx, hxi⟩
          rw [← himg] at hxi
          obtain ⟨y, hyS, hyx, hyc⟩ := (image_erase_eq_iff_exists hx).1 hxi
          by_cases hxu : x = u
          · exact Or.inl hxu
          · refine Or.inr ?_
            have hxe : x ∈ S.erase u := Finset.mem_erase.2 ⟨hxu, hx⟩
            by_cases hyu : y = u
            · subst hyu
              exact hinj' hxe hve (by rw [← hyc]; exact hcuv)
            · exact absurd (hinj' (Finset.mem_erase.2 ⟨hyu, hyS⟩) hxe hyc) hyx
        · intro h
          rcases h with h | h
          · subst h
            exact ⟨hu, by rw [himgeu, himg]⟩
          · subst h
            refine ⟨hv, ?_⟩
            rw [← himg]
            exact (image_erase_eq_iff_exists hv).2 ⟨u, hu, huv, hcuv⟩
      rw [hfilter, if_neg hne, Finset.card_insert_of_notMem (by simpa using huv),
        Finset.card_singleton]
  · -- some colour in `{0, …, k}` does not occur on `S`: no doors at all
    have hne : S.image color ≠ Finset.range (k + 2) := by
      intro h
      apply hrange
      rw [h]
      intro y hy
      rw [Finset.mem_range] at hy ⊢
      omega
    have hempty : S.filter (fun x => (S.erase x).image color = Finset.range (k + 1)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x _ hxi
      apply hrange
      rw [← hxi]
      exact Finset.image_subset_image (Finset.erase_subset _ _)
    rw [hempty, if_neg hne, Finset.card_empty]

/-! ### Sperner's lemma -/

/--
**Sperner's Lemma** (combinatorial form), stated for all skeleta at once.

`T k` is the set of `k`-dimensional cells of the induced triangulation of the `k`-th face
`⟨v₀, …, v_k⟩` of a triangulated `n`-simplex, and `color` is a Sperner colouring:

* `hcard`  : a `k`-cell has `k+1` vertices;
* `hcolor` : all colours occurring on the `k`-th face lie in `{0, …, k}`
  (this is the Sperner boundary condition);
* `hbase`  : the `0`-th face is the single vertex `v₀`, coloured `0`;
* `hdoor`  : the pseudomanifold / door condition — a *rainbow* `k`-cell `G`
  (colour set exactly `{0, …, k}`) is contained in an odd number of `(k+1)`-cells
  exactly when `G` itself lies in the `k`-th face, i.e. `G ∈ T k`.
  (Geometrically: a codimension-one face interior to the `(k+1)`-st face lies in two cells,
  one on its boundary lies in one; and a rainbow boundary face must lie in the `k`-th face.)

Conclusion: for every `k ≤ n` the number of *rainbow* `k`-cells — cells whose vertices
carry all of the colours `0, …, k` — is odd.
-/
theorem sperner_lemma_all {V : Type*} [DecidableEq V] [Fintype V]
    (n : ℕ) (color : V → ℕ) (T : ℕ → Finset (Finset V))
    (hcard : ∀ k ≤ n, ∀ S ∈ T k, S.card = k + 1)
    (hcolor : ∀ k ≤ n, ∀ S ∈ T k, S.image color ⊆ Finset.range (k + 1))
    (hbase : ∃ v, T 0 = {{v}} ∧ color v = 0)
    (hdoor : ∀ k, k + 1 ≤ n → ∀ G : Finset V, G.card = k + 1 →
      G.image color = Finset.range (k + 1) →
      ((T (k + 1)).filter (fun S => G ⊆ S)).card % 2 = if G ∈ T k then 1 else 0) :
    ∀ k ≤ n, ((T k).filter (fun S => S.image color = Finset.range (k + 1))).card % 2 = 1 := by
  intro k
  induction k with
  | zero =>
    intro _
    obtain ⟨v, hTv, hcv⟩ := hbase
    rw [hTv]
    have hfe : ({{v}} : Finset (Finset V)).filter
        (fun S => S.image color = Finset.range 1) = {{v}} := by
      rw [Finset.filter_eq_self]
      intro S hS
      rw [Finset.mem_singleton] at hS
      subst hS
      ext y
      simp [hcv]
    rw [hfe, Finset.card_singleton]
  | succ k ih =>
    intro hkn
    have hk : k ≤ n := by omega
    -- `D` is the set of all rainbow `k`-faces ("doors")
    set D : Finset (Finset V) :=
      (Finset.univ : Finset (Finset V)).filter
        (fun G => G.card = k + 1 ∧ G.image color = Finset.range (k + 1)) with hD
    -- double counting of incidences between doors and `(k+1)`-cells
    have key : ∑ S ∈ T (k + 1), (D.filter (fun G => G ⊆ S)).card
        = ∑ G ∈ D, ((T (k + 1)).filter (fun S => G ⊆ S)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    -- each cell has an odd number of doors iff it is rainbow
    have step1 : ∀ S ∈ T (k + 1), (D.filter (fun G => G ⊆ S)).card % 2
        = if S.image color = Finset.range (k + 2) then 1 else 0 := by
      intro S hS
      have hDS : D.filter (fun G => G ⊆ S)
          = S.powerset.filter (fun G => G.card = k + 1 ∧
              G.image color = Finset.range (k + 1)) := by
        ext G
        simp only [hD, Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ, true_and]
        tauto
      rw [hDS, card_filter_powerset_erase S (k + 1) (hcard (k + 1) hkn S hS),
        door_count color k S (hcard (k + 1) hkn S hS) (hcolor (k + 1) hkn S hS)]
    -- each door lies in an odd number of cells iff it is a `k`-cell of the `k`-th face
    have step2 : ∀ G ∈ D, ((T (k + 1)).filter (fun S => G ⊆ S)).card % 2
        = if G ∈ T k then 1 else 0 := by
      intro G hG
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hG
      exact hdoor k hkn G hG.1 hG.2
    have hDT : D.filter (fun G => G ∈ T k)
        = (T k).filter (fun S => S.image color = Finset.range (k + 1)) := by
      ext G
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨hcard k hk G h1, h2⟩, h1⟩
    have hleft : (∑ S ∈ T (k + 1), (D.filter (fun G => G ⊆ S)).card) % 2
        = ((T (k + 1)).filter (fun S => S.image color = Finset.range (k + 2))).card % 2 := by
      rw [Finset.sum_nat_mod, Finset.sum_congr rfl step1, ← Finset.card_filter]
    have hright : (∑ G ∈ D, ((T (k + 1)).filter (fun S => G ⊆ S)).card) % 2
        = ((T k).filter (fun S => S.image color = Finset.range (k + 1))).card % 2 := by
      rw [Finset.sum_nat_mod, Finset.sum_congr rfl step2, ← Finset.card_filter, hDT]
    rw [← hleft, key, hright]
    exact ih hk

/--
**Sperner's Lemma**: every Sperner colouring of a triangulated `n`-simplex has an odd
number of rainbow cells.  See `Math.sperner_lemma_all` for the meaning of the hypotheses.
-/
theorem sperner_lemma {V : Type*} [DecidableEq V] [Fintype V]
    (n : ℕ) (color : V → ℕ) (T : ℕ → Finset (Finset V))
    (hcard : ∀ k ≤ n, ∀ S ∈ T k, S.card = k + 1)
    (hcolor : ∀ k ≤ n, ∀ S ∈ T k, S.image color ⊆ Finset.range (k + 1))
    (hbase : ∃ v, T 0 = {{v}} ∧ color v = 0)
    (hdoor : ∀ k, k + 1 ≤ n → ∀ G : Finset V, G.card = k + 1 →
      G.image color = Finset.range (k + 1) →
      ((T (k + 1)).filter (fun S => G ⊆ S)).card % 2 = if G ∈ T k then 1 else 0) :
    Odd ((T n).filter (fun S => S.image color = Finset.range (n + 1))).card :=
  Nat.odd_iff.2 (sperner_lemma_all n color T hcard hcolor hbase hdoor n le_rfl)


/-! ### A concrete instance

To see that the hypotheses of `Math.sperner_lemma` are satisfiable in a non-degenerate
way, we exhibit the segment `[v₀, v₁]` subdivided at a midpoint: the vertices are
`0, 1, 2` with `0` and `2` the endpoints, coloured `0, 1, 1`.  The `1`-cells are
`{0,1}` and `{1,2}`, and exactly one of them (namely `{0,1}`) is rainbow. -/

namespace Example

def color : Fin 3 → ℕ := fun i => if i = 0 then 0 else 1

def T : ℕ → Finset (Finset (Fin 3)) :=
  fun k => if k = 0 then {{0}} else if k = 1 then {{0, 1}, {1, 2}} else ∅

theorem rainbow_cells_odd :
    Odd ((T 1).filter (fun S => S.image color = Finset.range 2)).card := by
  refine Math.sperner_lemma 1 color T ?_ ?_ ?_ ?_
  · intro k hk
    interval_cases k <;> decide
  · intro k hk
    interval_cases k <;> decide
  · exact ⟨0, by decide, by decide⟩
  · intro k hk
    obtain rfl : k = 0 := by omega
    intro G
    revert G
    decide

/-- There is exactly one rainbow cell in this triangulation. -/
theorem rainbow_cells_card :
    ((T 1).filter (fun S => S.image color = Finset.range 2)).card = 1 := by decide

end Example

/-! ### A two-dimensional instance

The triangle `[v₀, v₁, v₂]` subdivided by a single interior vertex `3`, coloured
`0, 1, 2, 0`.  The `2`-cells are `{0,1,3}`, `{1,2,3}`, `{0,2,3}`, the edge `[v₀,v₁]`
carries the single `1`-cell `{0,1}`, and exactly one `2`-cell is rainbow. -/

namespace Example2

def color : Fin 4 → ℕ := fun i => if i = 3 then 0 else (i : ℕ)

def T : ℕ → Finset (Finset (Fin 4)) :=
  fun k => if k = 0 then {{0}} else if k = 1 then {{0, 1}}
    else if k = 2 then {{0, 1, 3}, {1, 2, 3}, {0, 2, 3}} else ∅

theorem rainbow_cells_odd :
    Odd ((T 2).filter (fun S => S.image color = Finset.range 3)).card := by
  refine Math.sperner_lemma 2 color T ?_ ?_ ?_ ?_
  · intro k hk
    interval_cases k <;> decide
  · intro k hk
    interval_cases k <;> decide
  · exact ⟨0, by decide, by decide⟩
  · intro k hk
    have hk' : k ≤ 1 := by omega
    interval_cases k <;> (intro G; revert G; decide)

/-- There is exactly one rainbow `2`-cell in this triangulation. -/
theorem rainbow_cells_card :
    ((T 2).filter (fun S => S.image color = Finset.range 3)).card = 1 := by decide

end Example2

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

