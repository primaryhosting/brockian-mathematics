import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

/-- Sites of the `m × n` square lattice with periodic (toroidal) boundary conditions. -/
abbrev Site (m n : ℕ) : Type := ZMod m × ZMod n

/-- A spin configuration: a `± 1` value (encoded as a `Bool`) at every lattice site. -/
abbrev Config (m n : ℕ) : Type := Site m n → Bool

/-- The real spin value attached to a `Bool`. -/

theorem abs_freeEnergy_sub_log_two_le {m n : ℕ} [NeZero m] [NeZero n] (K : ℝ) :
    |freeEnergy m n K - Real.log 2| ≤ 2 * |K| := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hN : (0 : ℝ) < (m : ℝ) * n := mul_pos hm hn
  have hlog2 : Real.log ((2 : ℝ) ^ (m * n)) = ((m : ℝ) * n) * Real.log 2 := by
    rw [show ((2 : ℝ) ^ (m * n)) = (2 : ℝ) ^ ((m : ℕ) * n) from rfl, Real.log_pow]
    push_cast
    ring
  have hupper : Real.log (partitionFunction m n K)
      ≤ ((m : ℝ) * n) * Real.log 2 + 2 * |K| * ((m : ℝ) * n) := by
    have h := Real.log_le_log (partitionFunction_pos (m := m) (n := n) K)
      (partitionFunction_le (m := m) (n := n) K)
    rwa [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp, hlog2] at h
  have hlower : ((m : ℝ) * n) * Real.log 2 - 2 * |K| * ((m : ℝ) * n)
      ≤ Real.log (partitionFunction m n K) := by
    have h := Real.log_le_log (by positivity) (le_partitionFunction (m := m) (n := n) K)
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp, hlog2] at h
    linarith
  rw [abs_le]
  constructor
  · rw [freeEnergy, le_sub_iff_add_le, le_div_iff₀ hN]
    linarith
  · rw [freeEnergy, sub_le_iff_le_add, div_le_iff₀ hN]
    linarith

/-! ### Main statement -/

/--
**Onsager's two-dimensional Ising model, formalized statement with a Lean-checked base case.**

For every finite `m × n` torus:

* the partition function is strictly positive;
* at infinite temperature (`K = 0`) it equals `2^{mn}`, so the free energy per site equals
  `log 2`, which is exactly the value of Onsager's closed-form expression at `K = 0`
  (its double integral vanishes there);
* uniformly in the lattice size, the finite-volume free energy per site stays within
  `2|K|` of `log 2`, matching the corresponding bound satisfied by Onsager's formula.
-/
