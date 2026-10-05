import RequestProject.CapExpand

/-!
# The Ellenberg–Gijswijt bound

Combining the slice-rank bound with the polynomial expansion gives
`|A| ≤ 3 · #{exponent vectors of degree ≤ 2n/3}` for every 3AP-free `A ⊆ 𝔽₃ⁿ`.
-/

open scoped BigOperators
open Finset

namespace CapSetAux

/-- In `𝔽₃ⁿ`, a 3AP-free set contains no nontrivial triple summing to zero. -/

theorem exists_large_support (W : Submodule F (X → F)) :
    ∃ (S : Finset X) (u : X → F), u ∈ W ∧ (∀ x ∈ S, u x ≠ 0) ∧
      Module.finrank F W ≤ S.card := by
  classical
  set P : Finset X → Prop := fun S => ∀ c : X → F, ∃ u ∈ W, ∀ x ∈ S, u x = c x with hP
  have hne : ((univ : Finset (Finset X)).filter P).Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [mem_filter, mem_univ, true_and, hP]
    exact fun c => ⟨0, W.zero_mem, by simp⟩
  obtain ⟨S, hSmem, hSmax⟩ :=
    Finset.exists_max_image ((univ : Finset (Finset X)).filter P) Finset.card hne
  have hPS : P S := (mem_filter.mp hSmem).2
  obtain ⟨u, huW, hu⟩ := hPS (fun _ => 1)
  refine ⟨S, u, huW, ?_, ?_⟩
  · intro x hx
    rw [hu x hx]
    exact one_ne_zero
  · -- maximality forces `finrank W ≤ S.card`
    by_contra hlt
    push_neg at hlt
    -- the restriction map to `S` is surjective, so its kernel is nontrivial
    have hsurj : Function.Surjective (restrictMap W S) := by
      intro c
      obtain ⟨v, hvW, hv⟩ := hPS (fun x => if hx : x ∈ S then c ⟨x, hx⟩ else 0)
      refine ⟨⟨v, hvW⟩, ?_⟩
      funext x
      simpa [restrictMap, x.2] using hv x x.2
    have hrange : LinearMap.range (restrictMap W S) = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    have hfr : Module.finrank F (LinearMap.range (restrictMap W S))
        + Module.finrank F (LinearMap.ker (restrictMap W S)) = Module.finrank F W :=
      LinearMap.finrank_range_add_finrank_ker _
    have hrk : Module.finrank F (LinearMap.range (restrictMap W S)) = S.card := by
      rw [hrange, finrank_top]
      simp
    have hkerpos : Module.finrank F (LinearMap.ker (restrictMap W S)) ≠ 0 := by omega
    have hkerne : LinearMap.ker (restrictMap W S) ≠ ⊥ := fun hb => hkerpos (by
      rw [hb]; simp)
    obtain ⟨w, hwker, hw0⟩ := (Submodule.ne_bot_iff _).mp hkerne
    obtain ⟨w, hwmem⟩ := w
    -- `w` vanishes on `S` but is nonzero somewhere
    have hwS : ∀ x ∈ S, (w : X → F) x = 0 := by
      intro x hx
      have := congrFun (LinearMap.mem_ker.mp hwker) ⟨x, hx⟩
      simpa [restrictMap] using this
    have hwne : (w : X → F) ≠ 0 := by
      intro h
      apply hw0
      ext
      simpa using congrFun h _
    obtain ⟨x0, hx0⟩ := Function.ne_iff.mp hwne
    have hx0S : x0 ∉ S := fun hmem => hx0 (by simpa using hwS x0 hmem)
    -- so we can enlarge `S`, contradicting maximality
    have hPins : P (insert x0 S) := by
      intro c
      obtain ⟨v, hvW, hv⟩ := hPS c
      refine ⟨v + ((c x0 - v x0) / (w : X → F) x0) • (w : X → F),
        W.add_mem hvW (W.smul_mem _ hwmem), ?_⟩
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · have hwx : w x ≠ 0 := by simpa using hx0
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
        ring
      · simp [hv x hx, hwS x hx]
    have : (insert x0 S).card ≤ S.card :=
      hSmax _ (mem_filter.mpr ⟨mem_univ _, hPins⟩)
    rw [Finset.card_insert_of_notMem hx0S] at this
    omega

/-- **Slice rank of the diagonal tensor.** If the diagonal tensor on a finite type `X`
decomposes as a sum of `card I₁ + card I₂ + card I₃` slices, then
`card X ≤ card I₁ + card I₂ + card I₃`. -/
