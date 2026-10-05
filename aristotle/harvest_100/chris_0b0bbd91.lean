import Mathlib
/-!
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` lines to precede every other command, including
-- module doc comments, so the requested header block appears immediately after the import.

namespace Brockian.ConeLine

/-- The `n`-th triangular number, computed in `ℕ` (division happens before casting). -/
def T (n : ℕ) : ℕ := n * (n + 1) / 2

lemma two_dvd_mul_succ (n : ℕ) : 2 ∣ n * (n + 1) :=
  (Nat.even_mul_succ_self n).two_dvd

/-- Shifting the index by `10` changes the triangular number by a multiple of `5`. -/
lemma T_add_ten (n : ℕ) : T (n + 10) = T n + 5 * (2 * n + 11) := by
  have h : 2 ∣ n * (n + 1) := two_dvd_mul_succ n
  have hb : (n + 10) * (n + 10 + 1) = n * (n + 1) + 2 * (5 * (2 * n + 11)) := by ring
  simp only [T, hb]
  omega

/-- Triangular numbers only occupy residues `0, 1, 3` modulo `5`;
rays `2` and `4` carry no triangular number. -/
theorem triangular_mod5_mem (n : ℕ) :
    ((n * (n + 1) / 2 : ℕ) : ZMod 5) ∈ ({0, 1, 3} : Set (ZMod 5)) := by
  show ((T n : ℕ) : ZMod 5) ∈ _
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n 10 with hn | hn
    · simp only [T]
      interval_cases n <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
      have hm : ((T m : ℕ) : ZMod 5) ∈ ({0, 1, 3} : Set (ZMod 5)) := ih m (by omega)
      have hstep : ((T (m + 10) : ℕ) : ZMod 5) = ((T m : ℕ) : ZMod 5) := by
        rw [T_add_ten]
        push_cast
        have h5 : (5 : ZMod 5) = 0 := by decide
        rw [h5]
        ring
      rw [hstep]
      exact hm

/-- Rays `2` and `4` carry no triangular number. -/
theorem triangular_mod5_ne_two_four (n : ℕ) :
    ((n * (n + 1) / 2 : ℕ) : ZMod 5) ≠ 2 ∧ ((n * (n + 1) / 2 : ℕ) : ZMod 5) ≠ 4 := by
  have h := triangular_mod5_mem n
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩

end Brockian.ConeLine

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

