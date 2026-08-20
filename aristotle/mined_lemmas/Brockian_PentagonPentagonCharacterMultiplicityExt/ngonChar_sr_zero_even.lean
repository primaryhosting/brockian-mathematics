import Mathlib

/-!
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
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

namespace Brockian

/-- The natural action of the dihedral group `DihedralGroup n` on the `n` vertices of a regular
`n`-gon, the vertices being modelled by `ZMod n`.  The rotation `r i` sends a vertex `x` to
`x - i`, and the reflection `sr i` sends `x` to `i - x`. -/

lemma ngonChar_sr_zero_even (n : ℕ) [NeZero n] (m : ℕ) (hn : n = 2 * m) :
    ngonChar n (DihedralGroup.sr 0) = 2 := by
  classical
  rw [ngonChar_sr]
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact absurd (by simp [hn, h] : n = 0) (NeZero.ne n)
    · exact h
  have hmne : ((m : ℕ) : ZMod n) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have : n ≤ m := Nat.le_of_dvd hm hdvd
    omega
  have hset : (Finset.univ.filter fun x : ZMod n => 2 * x = 0) = {0, (m : ZMod n)} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      have hd : ((d.val : ℕ) : ZMod n) = d := by simp [ZMod.natCast_val, ZMod.cast_id]
      have hval : ((2 * d.val : ℕ) : ZMod n) = 0 := by
        push_cast
        rw [hd]; exact h
      rw [ZMod.natCast_eq_zero_iff] at hval
      have hlt : d.val < n := ZMod.val_lt d
      have hmv : m ∣ d.val := by
        have h2 : 2 * m ∣ 2 * d.val := by rw [← hn]; exact hval
        exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp h2
      obtain ⟨k, hk⟩ := hmv
      have hk2 : k < 2 := by
        by_contra hcon
        push_neg at hcon
        have : 2 * m ≤ m * k := by nlinarith
        omega
      interval_cases k
      · left; rw [← hd]; simp [hk]
      · right; rw [← hd, hk]; simp
    · rintro (rfl | rfl)
      · simp
      · have hz : ((2 * m : ℕ) : ZMod n) = 0 := by rw [← hn]; exact ZMod.natCast_self n
        push_cast at hz
        exact hz
  rw [hset, Finset.card_insert_of_notMem (by simpa [eq_comm] using hmne), Finset.card_singleton]

/-- For even `n` the permutation character of the `n`-gon satisfies `⟨χ, χ⟩ = (n+2)/2`. -/
