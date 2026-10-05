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
def Homog (n : ℕ) {k : ℕ} (c : Finset ℕ → Fin k) (T : Set ℕ) (i : Fin k) : Prop :=
  ∀ s : Finset ℕ, ↑s ⊆ T → s.card = n → c s = i

/-- A finite set of naturals is *relatively large* when its cardinality is at least its
least element. -/
def RelativelyLarge (H : Finset ℕ) : Prop :=
  ∃ h : H.Nonempty, H.min' h ≤ H.card

/-- The Paris–Harrington statement for exponent `n`, `k` colours and size bound `m`:
there is an `N` such that every `k`-colouring of the `n`-element subsets of `{1, …, N}`
admits a relatively large homogeneous subset with at least `m` elements. -/
def ParisHarringtonAt (n k m : ℕ) : Prop :=
  ∃ N : ℕ, ∀ c : Finset ℕ → Fin k, ∃ H : Finset ℕ, H ⊆ Finset.Icc 1 N ∧
    m ≤ H.card ∧ RelativelyLarge H ∧ ∃ i, Homog n c ↑H i

/-- The strengthened finite Ramsey theorem (Paris–Harrington principle). -/
def ParisHarringtonPrinciple : Prop := ∀ n k m : ℕ, ParisHarringtonAt n k m

/-- The infinite Ramsey theorem, relativised to an arbitrary infinite set of naturals. -/
theorem infinite_ramsey (n : ℕ) : ∀ {k : ℕ} (c : Finset ℕ → Fin k) (S : Set ℕ), S.Infinite →
    ∃ T ⊆ S, T.Infinite ∧ ∃ i, Homog n c T i := by
  induction n with
  | zero =>
      intro k c S hS
      refine ⟨S, subset_rfl, hS, c ∅, ?_⟩
      intro s _ hcard
      rw [Finset.card_eq_zero] at hcard
      subst hcard
      rfl
  | succ n ih =>
      intro k c S hS
      -- one step of the construction: from an infinite set, extract its least element `a`
      -- and an infinite subset above `a` which is homogeneous for `s ↦ c (insert a s)`
      have step : ∀ T : {T : Set ℕ // T.Infinite}, ∃ (a : ℕ) (i : Fin k)
          (T' : {T : Set ℕ // T.Infinite}), a ∈ T.1 ∧ T'.1 ⊆ {x ∈ T.1 | a < x} ∧
            (∀ s : Finset ℕ, ↑s ⊆ T'.1 → s.card = n → c (insert a s) = i) := by
        rintro ⟨T, hT⟩
        have haT : sInf T ∈ T := Nat.sInf_mem hT.nonempty
        have hinf : {x ∈ T | sInf T < x}.Infinite := by
          have hEq : {x ∈ T | sInf T < x} = T \ Set.Iic (sInf T) := by ext x; simp [not_le]
          rw [hEq]
          exact hT.diff (Set.finite_Iic _)
        obtain ⟨T', hT'sub, hT'inf, i, hi⟩ :=
          ih (fun s => c (insert (sInf T) s)) {x ∈ T | sInf T < x} hinf
        exact ⟨sInf T, i, ⟨T', hT'inf⟩, haT, hT'sub, hi⟩
      choose A col Nx hA hsub hcol using step
      -- iterate the step
      set seq : ℕ → {T : Set ℕ // T.Infinite} :=
        fun j => Nat.rec (motive := fun _ => {T : Set ℕ // T.Infinite}) ⟨S, hS⟩
          (fun _ T => Nx T) j
      set a : ℕ → ℕ := fun j => A (seq j)
      set d : ℕ → Fin k := fun j => col (seq j)
      have hmemseq : ∀ j, a j ∈ (seq j).1 := fun j => hA (seq j)
      have hstepsub : ∀ j, (seq (j + 1)).1 ⊆ {x ∈ (seq j).1 | a j < x} := fun j => hsub (seq j)
      have hchain : ∀ j l, j ≤ l → (seq l).1 ⊆ (seq j).1 := by
        intro j l hjl
        induction l with
        | zero => simp_all
        | succ l ihl =>
            rcases Nat.lt_or_ge j (l + 1) with hlt | hge
            · have hjl' : j ≤ l := Nat.lt_succ_iff.mp hlt
              exact fun x hx => ihl hjl' ((hstepsub l) hx).1
            · have : j = l + 1 := le_antisymm hjl hge
              subst this
              exact subset_rfl
      have hstrict : StrictMono a := by
        apply strictMono_nat_of_lt_succ
        intro j
        exact ((hstepsub j) (hmemseq (j + 1))).2
      -- pigeonhole on the colours `d j`
      obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber d
      have hJinf : {j : ℕ | d j = i}.Infinite := by
        rw [Set.infinite_coe_iff] at hi
        exact hi
      refine ⟨a '' {j : ℕ | d j = i}, ?_, hJinf.image (hstrict.injective.injOn), i, ?_⟩
      · rintro x ⟨j, -, rfl⟩
        exact hchain 0 j (Nat.zero_le j) (hmemseq j)
      · intro s hs hcard
        have hne : s.Nonempty := Finset.card_pos.mp (by omega)
        set x0 := s.min' hne
        have hx0s : x0 ∈ s := s.min'_mem hne
        obtain ⟨j0, hj0J, hj0⟩ := hs (by exact_mod_cast hx0s)
        have hins : insert x0 (s.erase x0) = s := Finset.insert_erase hx0s
        have hcard' : (s.erase x0).card = n := by
          rw [Finset.card_erase_of_mem hx0s, hcard]
          omega
        have hsub' : ↑(s.erase x0) ⊆ (seq (j0 + 1)).1 := by
          intro x hx
          rw [Finset.mem_coe, Finset.mem_erase] at hx
          obtain ⟨j, -, rfl⟩ := hs (by exact_mod_cast hx.2)
          have hlt : x0 < a j := by
            have h1 : x0 ≤ a j := s.min'_le _ hx.2
            have h2 : a j ≠ x0 := hx.1
            omega
          have hj0j : j0 < j := hstrict.lt_iff_lt.mp (by rw [hj0]; exact hlt)
          exact hchain (j0 + 1) j hj0j (hmemseq j)
        have := hcol (seq j0) (s.erase x0) hsub' hcard'
        rw [show A (seq j0) = x0 from hj0] at this
        rw [hins] at this
        rw [this]
        exact hj0J

/-- Compactness step: if the Paris–Harrington statement fails for some parameters, then
there is a single colouring of the `n`-element subsets of `ℕ` with no relatively large
homogeneous subset of `{1, 2, 3, …}` of size at least `m`. -/
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
theorem Paris_Harrington : ParisHarringtonPrinciple := by
  intro n k m
  by_contra hbad
  obtain ⟨c, hc⟩ := exists_bad_coloring_of_not_paris_harrington hbad
  obtain ⟨T, hTS, hTinf, i, hTi⟩ := infinite_ramsey n c (Set.Ici 1) (Set.Ici_infinite 1)
  -- pick a relatively large finite homogeneous subset of `T`
  set p := sInf T
  have hTne : T.Nonempty := hTinf.nonempty
  have hpT : p ∈ T := Nat.sInf_mem hTne
  obtain ⟨H', hH'T, hH'card⟩ := hTinf.exists_subset_card_eq (max m p)
  refine hc (insert p H') ?_ ?_ ?_ i ?_
  · intro x hx
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
    rcases hx with rfl | hx
    · exact hTS hpT
    · exact hTS (hH'T hx)
  · have h2 : H'.card ≤ (insert p H').card := Finset.card_le_card (Finset.subset_insert _ _)
    have h3 : m ≤ H'.card := hH'card ▸ le_max_left _ _
    omega
  · refine ⟨⟨p, Finset.mem_insert_self _ _⟩, ?_⟩
    have h1 : (insert p H').min' ⟨p, Finset.mem_insert_self _ _⟩ ≤ p :=
      Finset.min'_le _ _ (Finset.mem_insert_self _ _)
    have h2 : H'.card ≤ (insert p H').card := Finset.card_le_card (Finset.subset_insert _ _)
    have h3 : p ≤ H'.card := hH'card ▸ le_max_right _ _
    omega
  · intro s hs hcard
    refine hTi s ?_ hcard
    intro x hx
    have := hs hx
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at this
    rcases this with rfl | hx'
    · exact hpT
    · exact hH'T hx'

/-- The ordinary finite Ramsey theorem, obtained by forgetting the relative-largeness
requirement in the Paris–Harrington theorem. -/
theorem finite_ramsey (n k m : ℕ) :
    ∃ N : ℕ, ∀ c : Finset ℕ → Fin k, ∃ H : Finset ℕ, H ⊆ Finset.Icc 1 N ∧
      m ≤ H.card ∧ ∃ i, Homog n c ↑H i := by
  obtain ⟨N, hN⟩ := Paris_Harrington n k m
  refine ⟨N, fun c => ?_⟩
  obtain ⟨H, hH, hcard, -, hhom⟩ := hN c
  exact ⟨H, hH, hcard, hhom⟩

end Frontier

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

