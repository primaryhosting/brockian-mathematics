import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- A finite set `Y` of positive integers is *relatively large* when its least element is at
most its cardinality. -/

lemma chain_G {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) (t : ℕ) :
    ∀ s ⊆ chain n c t, s.card ≤ n → G c (n - s.card) s = G c n ∅ := by
  induction t with
  | zero =>
      intro s hs _
      have : s = ∅ := by simpa [chain, Finset.subset_empty] using hs
      subst this
      simp
  | succ t ih =>
      intro s hs hcard
      set x : ℕ := next n c (chain n c t) with hxdef
      by_cases hxs : x ∈ s
      · have hs' : s.erase x ⊆ chain n c t := by
          intro y hy
          have hy1 : y ∈ s := Finset.mem_of_mem_erase hy
          have hy2 : y ≠ x := Finset.ne_of_mem_erase hy
          have := hs hy1
          rw [chain, Finset.mem_insert] at this
          rcases this with h | h
          · exact absurd h hy2
          · exact h
        have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨x, hxs⟩
        have hcard' : (s.erase x).card + 1 = s.card := by
          rw [Finset.card_erase_of_mem hxs]
          omega
        have hlt : (s.erase x).card < n := by omega
        have hins : insert x (s.erase x) = s := Finset.insert_erase hxs
        have hstep := (next_spec n c (chain n c t)).2.2 (s.erase x)
          (Finset.mem_powerset.mpr hs') hlt
        rw [hins] at hstep
        have hidx : n - (s.erase x).card - 1 = n - s.card := by omega
        rw [hidx] at hstep
        rw [hstep]
        exact ih (s.erase x) hs' (le_of_lt hlt)
      · have hs' : s ⊆ chain n c t := by
          intro y hy
          have := hs hy
          rw [chain, Finset.mem_insert] at this
          rcases this with h | h
          · exact absurd (show x ∈ s by rw [hxdef, ← h]; exact hy) hxs
          · exact h
        exact ih s hs' hcard

