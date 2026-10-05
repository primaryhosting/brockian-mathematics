import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set

namespace Frontier

/-! ## Basic notions -/

/-- A finite set of naturals is *relatively large* when it is nonempty and its cardinality
is at least its least element. -/

theorem homog_aux : ∀ (n : ℕ) (s : Finset ℕ), s.card = n → ↑s ⊆ Set.range (chainElt U D k) →
    ∀ i, i + n = k → D i s = D k ∅ := by
  intro n
  induction n with
  | zero =>
      intro s hs0 _ i hi
      rw [Finset.card_eq_zero] at hs0
      subst hs0
      simp only [Nat.add_zero] at hi
      subst hi
      rfl
  | succ n ih =>
      intro s hsc hs i hi
      have hne : s.Nonempty := Finset.card_pos.1 (by omega)
      set x := s.max' hne with hxdef
      have hxs : x ∈ s := s.max'_mem hne
      obtain ⟨p, hp⟩ : x ∈ Set.range (chainElt U D k) := hs hxs
      have hcard : (s.erase x).card = n := by
        rw [Finset.card_erase_of_mem hxs, hsc]
        omega
      have hsub : s.erase x ⊆ chain U D k p := by
        intro y hy
        have hys : y ∈ s := Finset.mem_of_mem_erase hy
        have hyne : y ≠ x := Finset.ne_of_mem_erase hy
        obtain ⟨q, hq⟩ : y ∈ Set.range (chainElt U D k) := hs hys
        have hylt : y < x := lt_of_le_of_ne (s.le_max' y hys) hyne
        have hqp : q < p := by
          rw [← hq, ← hp] at hylt
          exact (chainElt_strictMono U D k hU hD).lt_iff_lt.1 hylt
        rw [chain_eq_image U D k p]
        exact Finset.mem_image.2 ⟨q, Finset.mem_range.2 hqp, hq⟩
      have key := (chainElt_mem_goodSet U D k hU hD p).2 (s.erase x) hsub i (by omega)
      rw [hp, Finset.insert_erase hxs] at key
      rw [key]
      refine ih (s.erase x) hcard ?_ (i + 1) (by omega)
      exact fun y hy => hs (Finset.mem_of_mem_erase hy)

end Greedy

/-- **Infinite Ramsey theorem**: for every colouring of the `k`-element subsets of `ℕ` with
`r` colours there is an infinite homogeneous set. -/
