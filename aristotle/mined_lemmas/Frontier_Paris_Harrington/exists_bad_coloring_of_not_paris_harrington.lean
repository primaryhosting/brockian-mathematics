import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset Set

/-- `Homog n c T i` says: every `n`-element subset of the set `T` gets colour `i` under `c`. -/

theorem exists_bad_coloring_of_not_paris_harrington {n k m : ℕ}
    (h : ¬ ParisHarringtonAt n k m) :
    ∃ c : Finset ℕ → Fin k, ∀ H : Finset ℕ, ↑H ⊆ Set.Ici 1 → m ≤ H.card →
      RelativelyLarge H → ∀ i, ¬ Homog n c ↑H i := by
  rw [ParisHarringtonAt] at h
  push_neg at h
  choose cbad hcbad using h
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le (Filter.cofinite : Filter ℕ)
  have key : ∀ s : Finset ℕ, ∃ i : Fin k, {N : ℕ | cbad N s = i} ∈ U := by
    intro s
    have huniv : (Set.univ : Set ℕ) =
        ⋃ i ∈ (Set.univ : Set (Fin k)), {N : ℕ | cbad N s = i} := by
      ext N; simp
    have hmem : (⋃ i ∈ (Set.univ : Set (Fin k)), {N : ℕ | cbad N s = i}) ∈ U :=
      huniv ▸ U.univ_mem
    rw [Ultrafilter.finite_biUnion_mem_iff (Set.finite_univ)] at hmem
    obtain ⟨i, -, hi⟩ := hmem
    exact ⟨i, hi⟩
  refine ⟨fun s => (key s).choose, ?_⟩
  intro H hH1 hHm hHL i hHom
  have hmem : ∀ s ∈ H.powersetCard n, {N : ℕ | cbad N s = i} ∈ U := by
    intro s hs
    rw [Finset.mem_powersetCard] at hs
    have hci : (key s).choose = i := hHom s (by exact_mod_cast hs.1) hs.2
    have hkey := (key s).choose_spec
    rwa [hci] at hkey
  have hA : (⋂ s ∈ H.powersetCard n, {N : ℕ | cbad N s = i}) ∈ U :=
    (Filter.biInter_finset_mem _).2 hmem
  have hinf : (⋂ s ∈ H.powersetCard n, {N : ℕ | cbad N s = i}).Infinite := by
    intro hfin
    have h1 : (⋂ s ∈ H.powersetCard n, {N : ℕ | cbad N s = i})ᶜ ∈ U :=
      hU hfin.compl_mem_cofinite
    exact (U.compl_notMem_iff.2 hA) h1
  obtain ⟨N, hNmem, hNgt⟩ := hinf.exists_gt (H.sup id)
  refine hcbad N H ?_ hHm hHL i ?_
  · intro x hx
    rw [Finset.mem_Icc]
    refine ⟨hH1 hx, ?_⟩
    have : id x ≤ H.sup id := Finset.le_sup hx
    simp only [id] at this
    omega
  · intro s hs hcard
    have hs' : s ∈ H.powersetCard n := Finset.mem_powersetCard.2 ⟨by exact_mod_cast hs, hcard⟩
    simpa using Set.mem_iInter₂.1 hNmem s hs'

/-- **Paris–Harrington theorem** (the "true" half): the strengthened finite Ramsey theorem
holds.  Its unprovability in Peano Arithmetic is a metamathematical statement about the
formal system PA, and is not formalised here. -/
