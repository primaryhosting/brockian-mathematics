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
