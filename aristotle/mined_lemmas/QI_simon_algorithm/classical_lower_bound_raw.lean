/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- repeated as a module docstring immediately after the import.)

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Bit vectors -/

/-- `n`-bit strings, as a vector space over `ZMod 2`. -/
abbrev BV (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}


theorem classical_lower_bound_raw (k : ℕ) (A : ClassicalAlgo n)
    (hA : ∀ (f : BV n → BV n) (s : BV n), IsSimon f s → A.output (transcript A f k) = s) :
    2 ^ n ≤ k * k + 2 := by
  by_contra hcon
  push_neg at hcon
  set Q : Finset (BV n) := queries A id k with hQdef
  have hQcard : Q.card ≤ k := queries_card_le A id k
  set D : Finset (BV n) := insert 0 (diffs Q) with hDdef
  have hD : D.card ≤ k * k + 1 := by
    have h1 : D.card ≤ (diffs Q).card + 1 := by
      rw [hDdef]; exact Finset.card_insert_le _ _
    have h2 := diffs_card_le Q
    have h3 : Q.card * Q.card ≤ k * k := Nat.mul_le_mul hQcard hQcard
    omega
  have hcard : (Finset.univ : Finset (BV n)).card = 2 ^ n := by simp
  have h1 : 1 < (Finset.univ \ D).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ D), hcard]
    omega
  obtain ⟨s1, hs1, s2, hs2, hne⟩ := Finset.one_lt_card.mp h1
  have key : ∀ s ∈ Finset.univ \ D, A.output (transcript A id k) = s := by
    intro s hsm
    have hsD : s ∉ D := (Finset.mem_sdiff.mp hsm).2
    have hs0 : s ≠ 0 := by
      intro h
      exact hsD (by rw [hDdef, h]; exact Finset.mem_insert_self _ _)
    have hsd : s ∉ diffs Q := fun h => hsD (Finset.mem_insert_of_mem h)
    have hf : ∀ x ∈ queries A id k, adv Q s x = x :=
      fun x hx => adv_eq_self Q s (not_mem_diffs Q hsd) hx
    have ht := transcript_eq_of_agree A (adv Q s) k hf k le_rfl
    have hout := hA (adv Q s) s (isSimon_adv Q s hs0)
    rwa [ht] at hout
  exact hne ((key s1 hs1).symm.trans (key s2 hs2))

/-- **Classical lower bound.**  A deterministic classical algorithm that always identifies the
hidden shift needs at least `2 ^ (n / 2) - 2` queries: `Ω(2 ^ (n / 2))`. -/
