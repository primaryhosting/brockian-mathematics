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

import Mathlib

/-!
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- The `n`-th triangular number, computed in `ℕ` (division after multiplication). -/
def T (n : ℕ) : ℕ := n * (n + 1) / 2

/-- Splitting `n = 10 * q + r` shows the triangular number decomposes with a multiple of 5. -/
lemma T_ten_mul_add (q r : ℕ) :
    T (10 * q + r) = 5 * (10 * q * q + 2 * q * r + q) + T r := by
  obtain ⟨s, hs⟩ : ∃ s, r * (r + 1) = 2 * s := by
    obtain ⟨s, hs⟩ := Nat.even_mul_succ_self r
    exact ⟨s, by omega⟩
  have h1 : (10 * q + r) * (10 * q + r + 1)
      = 2 * (5 * (10 * q * q + 2 * q * r + q) + s) := by
    have : (10 * q + r) * (10 * q + r + 1)
        = 100 * q * q + 20 * q * r + 10 * q + r * (r + 1) := by ring
    rw [this, hs]; ring
  unfold T
  rw [h1, Nat.mul_div_cancel_left _ (by norm_num), hs,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

/-- `T n` modulo 5 has period 10 in `n`. -/
lemma T_mod_five_periodic (n : ℕ) : T n % 5 = T (n % 10) % 5 := by
  conv_lhs => rw [show n = 10 * (n / 10) + n % 10 by omega]
  rw [T_ten_mul_add]
  omega

/-- The residue of `T n` mod 5, at the level of natural numbers. -/
lemma T_mod_five_cases (n : ℕ) : T n % 5 = 0 ∨ T n % 5 = 1 ∨ T n % 5 = 3 := by
  rw [T_mod_five_periodic n]
  have hr : n % 10 < 10 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (n % 10) <;> simp [T]

/-- Triangular numbers only ever land on the residues `0`, `1`, `3` mod 5. -/
theorem triangular_mod5_mem (n : ℕ) : ((T n : ℕ) : ZMod 5) ∈ ({0, 1, 3} : Set (ZMod 5)) := by
  have hcast : ((T n : ℕ) : ZMod 5) = ((T n % 5 : ℕ) : ZMod 5) := by
    simp [ZMod.natCast_mod]
  rcases T_mod_five_cases n with h | h | h <;> rw [hcast, h] <;> simp

/-- Rays `2` and `4` mod 5 carry no triangular number. -/
theorem triangular_mod5_ne_two_four (n : ℕ) :
    ((T n : ℕ) : ZMod 5) ≠ 2 ∧ ((T n : ℕ) : ZMod 5) ≠ 4 := by
  have h := triangular_mod5_mem n
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩

end Brockian.ConeLine

