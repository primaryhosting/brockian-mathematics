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

set_option autoImplicit false

namespace Brockian
namespace ConeLine

/-- The `n`-th triangular number, computed in `ℕ` (so the division is exact). -/
def T (n : ℕ) : ℕ := n * (n + 1) / 2

/-- Splitting off a multiple of `10`: `T (10 * k + m) = T m + 5 * (…)`.
This exhibits the period `10` of `n ↦ T n mod 5`. -/
lemma T_ten_mul_add (k m : ℕ) :
    T (10 * k + m) = T m + 5 * (10 * k * k + 2 * k * m + k) := by
  have h : (10 * k + m) * (10 * k + m + 1)
      = m * (m + 1) + 2 * (5 * (10 * k * k + 2 * k * m + k)) := by ring
  simp only [T, h, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]

/-- `T n mod 5` only depends on `n mod 10`. -/
lemma T_mod_five (n : ℕ) : T n % 5 = T (n % 10) % 5 := by
  conv_lhs => rw [← Nat.div_add_mod n 10, T_ten_mul_add]
  simp [Nat.add_mul_mod_self_left]

/-- The finite check: for the ten residues `m < 10`, `T m mod 5 ∈ {0, 1, 3}`. -/
lemma T_mod_five_small : ∀ m < 10, T m % 5 = 0 ∨ T m % 5 = 1 ∨ T m % 5 = 3 := by decide

/-- Triangular numbers land only on the rays `0, 1, 3` modulo `5`:
for every `n`, `T n = n (n + 1) / 2` satisfies `T n mod 5 ∈ {0, 1, 3}`,
so the rays `2` and `4` carry no triangular number. -/
theorem triangular_mod5_mem (n : ℕ) :
    ((n * (n + 1) / 2 : ℕ) : ZMod 5) ∈ ({0, 1, 3} : Set (ZMod 5)) := by
  have hlt : n % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hres : T n % 5 = 0 ∨ T n % 5 = 1 ∨ T n % 5 = 3 := by
    rw [T_mod_five n]
    exact T_mod_five_small _ hlt
  have hcast : ((n * (n + 1) / 2 : ℕ) : ZMod 5) = ((T n % 5 : ℕ) : ZMod 5) := by
    rw [ZMod.natCast_mod]
    rfl
  rw [hcast]
  rcases hres with h | h | h <;> rw [h] <;> simp

end ConeLine
end Brockian

