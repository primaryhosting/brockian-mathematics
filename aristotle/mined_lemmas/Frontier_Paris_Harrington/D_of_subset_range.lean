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

set_option grind.warning false

namespace Frontier

namespace ParisHarrington

open Filter

/-- A fixed ultrafilter on `ℕ` refining the filter `atTop`; in particular every cofinite
set belongs to it. -/

lemma D_of_subset_range (c : Finset ℕ → Fin k) (n : ℕ) :
    ∀ (r q : ℕ), q + r ≤ n → ∀ t : Finset ℕ, (↑t ⊆ Set.range (seq c n)) → t.card = r →
      D c q t = D c (q + r) ∅ := by
  intro r
  induction r with
  | zero =>
      intro q _ t _ hcard
      have ht0 : t = ∅ := Finset.card_eq_zero.1 hcard
      subst ht0
      simp
  | succ r ih =>
      intro q hq t ht hcard
      have hne : t.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨j, hj⟩ : t.max' hne ∈ Set.range (seq c n) :=
        ht (Finset.mem_coe.2 (t.max'_mem hne))
      have hxt : t.max' hne ∈ t := t.max'_mem hne
      have hcard' : (t.erase (t.max' hne)).card = r := by
        rw [Finset.card_erase_of_mem hxt, hcard]
        omega
      have hsub' : ↑(t.erase (t.max' hne)) ⊆ Set.range (seq c n) := by
        intro y hy
        exact ht (Finset.mem_coe.2 (Finset.mem_of_mem_erase (Finset.mem_coe.1 hy)))
      have hins : insert (t.max' hne) (t.erase (t.max' hne)) = t := Finset.insert_erase hxt
      have hchosen : t.erase (t.max' hne) ⊆ chosen c n j := by
        intro y hy
        have hyt : y ∈ t := Finset.mem_of_mem_erase hy
        obtain ⟨l, hl⟩ : y ∈ Set.range (seq c n) := ht (Finset.mem_coe.2 hyt)
        have hylt : y < t.max' hne :=
          lt_of_le_of_ne (t.le_max' y hyt) (Finset.ne_of_mem_erase hy)
        have hlj : l < j := by
          have : seq c n l < seq c n j := by rw [hl, hj]; exact hylt
          exact (seq_strictMono c n).lt_iff_lt.1 this
        rw [chosen_eq_image]
        exact Finset.mem_image.2 ⟨l, Finset.mem_range.2 hlj, hl⟩
      have hpx : pick c n (chosen c n j) = t.max' hne := hj
      have hgood := pick_good c n (chosen c n j) (t.erase (t.max' hne))
        (Finset.mem_powerset.2 hchosen) q (by omega)
      rw [hpx, hins] at hgood
      rw [hgood, ih (q + 1) (by omega) _ hsub' hcard']
      congr 1
      omega

/-- **Infinite Ramsey theorem** (for `n`-element subsets and `k` colours): for every colouring
`c` of the finite subsets of `ℕ` with `k` colours there is a strictly monotone `f : ℕ → ℕ`
such that all `n`-element subsets of the range of `f` receive the same colour. -/
