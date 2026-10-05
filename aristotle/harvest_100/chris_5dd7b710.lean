import Mathlib

/-!
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
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

namespace Brockian
namespace ConeLine

/-- The `n`-th triangular number, `T n = n(n+1)/2` (natural-number division). -/
def T (n : ℕ) : ℕ := n * (n + 1) / 2

/-- Twice a triangular number is `n(n+1)`. -/
lemma two_mul_T (n : ℕ) : 2 * T n = n * (n + 1) := by
  have h : 2 ∣ n * (n + 1) := (Nat.even_mul_succ_self n).two_dvd
  rw [T, Nat.mul_div_cancel' h]

/-- In `ZMod 5`, the triangular number `T n` equals `3 * n * (n + 1)`. -/
lemma T_cast (n : ℕ) : (T n : ZMod 5) = 3 * (n : ZMod 5) * ((n : ZMod 5) + 1) := by
  have h : ((2 * T n : ℕ) : ZMod 5) = ((n * (n + 1) : ℕ) : ZMod 5) := by
    rw [two_mul_T]
  push_cast at h
  have h6 : (3 : ZMod 5) * 2 = 1 := by decide
  calc (T n : ZMod 5) = ((3 : ZMod 5) * 2) * (T n : ZMod 5) := by rw [h6, one_mul]
    _ = 3 * (2 * (T n : ZMod 5)) := by ring
    _ = 3 * ((n : ZMod 5) * ((n : ZMod 5) + 1)) := by rw [h]
    _ = 3 * (n : ZMod 5) * ((n : ZMod 5) + 1) := by ring

/-- Triangular numbers land only on rays `0, 1, 3` modulo `5`:
for every `n`, `T n = n(n+1)/2` satisfies `(T n : ZMod 5) ∈ {0, 1, 3}`;
rays `2` and `4` carry no triangular number. -/
theorem triangular_mod5_mem (n : ℕ) :
    ((n * (n + 1) / 2 : ℕ) : ZMod 5) ∈ ({0, 1, 3} : Set (ZMod 5)) := by
  have key : ∀ x : ZMod 5, 3 * x * (x + 1) = 0 ∨ 3 * x * (x + 1) = 1 ∨ 3 * x * (x + 1) = 3 := by
    decide
  have h := key (n : ZMod 5)
  rw [show (n * (n + 1) / 2 : ℕ) = T n from rfl, T_cast n]
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h

end ConeLine
end Brockian

