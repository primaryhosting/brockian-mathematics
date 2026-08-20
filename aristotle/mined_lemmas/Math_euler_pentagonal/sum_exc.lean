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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

/-- The smallest element of a finite set of naturals (junk value `0` if empty). -/

lemma sum_exc (n : ℕ) (hn : 1 ≤ n) :
    ∑ s ∈ (D n).filter isExc, (-1 : ℤ) ^ s.card
      = ∑ k ∈ (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun k => (2 * n : ℤ) = k * (3 * k - 1)),
          (-1 : ℤ) ^ k.natAbs := by
  refine Finset.sum_nbij' excIdx idxSet ?_ ?_ ?_ ?_ ?_
  · -- excIdx maps into the index set
    intro s hs
    obtain ⟨m, hm, hcase⟩ := exc_classify hn hs
    rw [Finset.mem_filter, Finset.mem_Icc]
    rcases hcase with ⟨hIcc, hcard, hcond, hsum⟩ | ⟨hIcc, hcard, hcond, hsum⟩
    · have hidx : excIdx s = (m : ℤ) := by rw [excIdx, if_pos hcond, hcard]
      have hmn : m ≤ n := pent_le1 hm hsum
      have hz : (2 * (n : ℤ)) = (m : ℤ) * (3 * (m : ℤ) - 1) := by
        have h1 : (1 : ℕ) ≤ 3 * m := by omega
        zify [h1] at hsum
        linarith
      have hmn' : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
      rw [hidx]
      exact ⟨⟨by omega, hmn'⟩, by linear_combination hz⟩
    · have hidx : excIdx s = -(m : ℤ) := by rw [excIdx, if_neg hcond, hcard]
      have hmn : m ≤ n := pent_le2 hm hsum
      have hz : (2 * (n : ℤ)) = (m : ℤ) * (3 * (m : ℤ) + 1) := by exact_mod_cast hsum
      have hmn' : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
      rw [hidx]
      exact ⟨⟨by omega, by omega⟩, by linear_combination hz⟩
  · -- idxSet maps back
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨-, hkeq⟩ := hk
    rcases lt_trichotomy k 0 with hneg | hzero | hpos
    · rw [idxSet_neg hneg]
      set m := (-k).toNat with hm
      have hk' : k = -(m : ℤ) := by omega
      have hm1 : 1 ≤ m := by omega
      refine Icc2_mem_exc hm1 ?_
      have : (2 * (n : ℤ)) = (m : ℤ) * (3 * (m : ℤ) + 1) := by rw [hk'] at hkeq; linarith [hkeq]
      exact_mod_cast this
    · exfalso; rw [hzero] at hkeq; simp at hkeq; omega
    · rw [idxSet_pos hpos]
      set m := k.toNat with hm
      have hk' : k = (m : ℤ) := by omega
      have hm1 : 1 ≤ m := by omega
      refine Icc1_mem_exc hm1 ?_
      have h1 : (1 : ℕ) ≤ 3 * m := by omega
      have : (2 * (n : ℤ)) = (m : ℤ) * (3 * (m : ℤ) - 1) := by rw [hk'] at hkeq; linarith [hkeq]
      zify [h1]
      linarith
  · -- left inverse
    intro s hs
    obtain ⟨m, hm, hcase⟩ := exc_classify hn hs
    rcases hcase with ⟨hIcc, hcard, hcond, -⟩ | ⟨hIcc, hcard, hcond, -⟩
    · have hidx : excIdx s = (m : ℤ) := by rw [excIdx, if_pos hcond, hcard]
      rw [hidx, idxSet_pos (by exact_mod_cast hm), Int.toNat_natCast, hIcc]
    · have hidx : excIdx s = -(m : ℤ) := by rw [excIdx, if_neg hcond, hcard]
      rw [hidx, idxSet_neg (by simp; omega), neg_neg, Int.toNat_natCast, hIcc]
  · -- right inverse
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨-, hkeq⟩ := hk
    rcases lt_trichotomy k 0 with hneg | hzero | hpos
    · rw [idxSet_neg hneg]
      set m := (-k).toNat with hm
      have hm1 : 1 ≤ m := by omega
      rw [excIdx_Icc2 hm1]
      omega
    · exfalso; rw [hzero] at hkeq; simp at hkeq; omega
    · rw [idxSet_pos hpos]
      set m := k.toNat with hm
      have hm1 : 1 ≤ m := by omega
      rw [excIdx_Icc1 hm1]
      omega
  · -- the summands match
    intro s hs
    obtain ⟨m, hm, hcase⟩ := exc_classify hn hs
    rcases hcase with ⟨-, hcard, hcond, -⟩ | ⟨-, hcard, hcond, -⟩
    · have hidx : excIdx s = (m : ℤ) := by rw [excIdx, if_pos hcond, hcard]
      rw [hidx, hcard]
      simp
    · have hidx : excIdx s = -(m : ℤ) := by rw [excIdx, if_neg hcond, hcard]
      rw [hidx, hcard]
      simp

/-! ### Euler's pentagonal number theorem -/

