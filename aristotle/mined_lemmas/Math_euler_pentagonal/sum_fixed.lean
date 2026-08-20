/-
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
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

set_option grind.warning false

/-!
Euler's pentagonal number theorem.

We prove that the coefficient of `q^n` in the (truncated) product `∏_{i=1}^{N} (1 - q^i)`
(for any `N ≥ n`, so that the coefficient has already stabilised) equals
`∑_{k ∈ ℤ} (-1)^k [n = k(3k-1)/2]`.

The proof is Franklin's involution on partitions into distinct parts.
-/

namespace Math

open Finset

/-! ### Basic combinatorial gadgets -/

/-- `runLen s t` is the length of the maximal run `t, t-1, t-2, …` of consecutive
elements of `s` ending at `t`. -/

lemma sum_fixed (n : ℕ) :
    ∑ s ∈ (distinctParts n).filter (fun s => IsFixed s), (-1 : ℤ) ^ s.card
      = pentagonalSign n := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : (distinctParts 0).filter (fun s => IsFixed s) = {∅} := by
      ext s
      simp only [Finset.mem_filter, mem_distinctParts, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h0, hsum⟩, -⟩
        by_contra hcon
        obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hcon
        have hle : a ≤ 0 := by
          rw [← hsum]
          exact Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) ha
        exact h0 (by simpa [Nat.le_zero.1 hle] using ha)
      · rintro rfl
        exact ⟨⟨by simp, by simp⟩, Or.inl rfl⟩
    rw [h, pentagonalSign_eq]
    have h2 : pentIdx 0 = {(0 : ℤ)} := by
      ext k
      simp only [pentIdx, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨-, heq⟩
        have h0 : k * (3 * k - 1) = 0 := by push_cast at heq; linarith
        rcases mul_eq_zero.1 h0 with h | h
        · exact h
        · omega
      · rintro rfl
        norm_num
    rw [h2]
    simp
  · rw [pentagonalSign_eq]
    refine Finset.sum_nbij' pentIdxOf pentSet ?_ ?_ ?_ ?_ ?_
    · intro s hs
      obtain ⟨k, hk, hc⟩ := (mem_F_iff n hn s).1 hs
      rcases hc with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
      · rw [pentIdxOf_Ico1 hk]
        exact (mem_pentIdx_iff n hn _).2 ⟨k, hk, Or.inl ⟨rfl, ha⟩⟩
      · rw [pentIdxOf_Ico2 hk]
        exact (mem_pentIdx_iff n hn _).2 ⟨k, hk, Or.inr ⟨rfl, ha⟩⟩
    · intro k hk
      obtain ⟨j, hj1, hc⟩ := (mem_pentIdx_iff n hn k).1 hk
      rcases hc with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
      · rw [pentSet_ofNat hj1]
        exact (mem_F_iff n hn _).2 ⟨j, hj1, Or.inl ⟨rfl, ha⟩⟩
      · rw [pentSet_neg hj1]
        exact (mem_F_iff n hn _).2 ⟨j, hj1, Or.inr ⟨rfl, ha⟩⟩
    · intro s hs
      obtain ⟨k, hk, hc⟩ := (mem_F_iff n hn s).1 hs
      rcases hc with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
      · rw [pentIdxOf_Ico1 hk, pentSet_ofNat hk]
      · rw [pentIdxOf_Ico2 hk, pentSet_neg hk]
    · intro k hk
      obtain ⟨j, hj1, hc⟩ := (mem_pentIdx_iff n hn k).1 hk
      rcases hc with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
      · rw [pentSet_ofNat hj1, pentIdxOf_Ico1 hj1]
      · rw [pentSet_neg hj1, pentIdxOf_Ico2 hj1]
    · intro s hs
      obtain ⟨k, hk, hc⟩ := (mem_F_iff n hn s).1 hs
      rcases hc with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
      · rw [pentIdxOf_Ico1 hk, card_Ico1]
        simp
      · rw [pentIdxOf_Ico2 hk, card_Ico2]
        simp

