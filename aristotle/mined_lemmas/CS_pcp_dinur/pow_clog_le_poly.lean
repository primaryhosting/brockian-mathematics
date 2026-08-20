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
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- A *constraint graph* (a binary constraint satisfaction instance): `n` variables taking
values in the alphabet `Fin (q+1)`, together with a list of binary constraints, each given by
an ordered pair of variables and a decidable relation on the alphabet. -/
structure ConstraintGraph where
  /-- Number of variables. -/
  n : ℕ
  /-- The alphabet is `Fin (q+1)`; in particular it is nonempty. -/
  q : ℕ
  /-- The constraints: each is a pair of variables together with a relation they must satisfy. -/
  edges : List ((Fin n × Fin n) × (Fin (q + 1) → Fin (q + 1) → Bool))

namespace ConstraintGraph

/-- An assignment of alphabet values to the variables of `G`. -/
abbrev Assignment (G : ConstraintGraph) := Fin G.n → Fin (G.q + 1)

/-- The number of constraints of `G` (its size). -/

lemma pow_clog_le_poly (K m : ℕ) (hm : 1 ≤ m) :
    K ^ (Nat.clog 2 m) ≤ (2 * m) ^ (Nat.clog 2 K) := by
  have hpow : 2 ^ (Nat.clog 2 m) ≤ 2 * m := by
    rcases eq_or_lt_of_le hm with h | h
    · simp [← h]
    · have h1 : 0 < Nat.clog 2 m := Nat.clog_pos (by norm_num) h
      have h2 : 2 ^ (Nat.clog 2 m - 1) < m := Nat.pow_pred_clog_lt_self (by norm_num) h
      calc 2 ^ (Nat.clog 2 m) = 2 * 2 ^ (Nat.clog 2 m - 1) := by
            rw [← pow_succ']; congr 1; omega
        _ ≤ 2 * m := by omega
  have hK : K ≤ 2 ^ (Nat.clog 2 K) := Nat.le_pow_clog (by norm_num) K
  calc K ^ (Nat.clog 2 m) ≤ (2 ^ (Nat.clog 2 K)) ^ (Nat.clog 2 m) :=
        Nat.pow_le_pow_left hK _
    _ = (2 ^ (Nat.clog 2 m)) ^ (Nat.clog 2 K) := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (2 * m) ^ (Nat.clog 2 K) := Nat.pow_le_pow_left hpow _

/--
**The PCP theorem, in Dinur's gap-amplification form.**

Assume a gap-amplification step `amp` on binary constraint graphs which
* blows up the size by at most a constant factor `K`,
* doubles the unsat value until it reaches the constant `α ∈ (0,1]`,
* and preserves satisfiability (perfect completeness).

Then, applying `amp` a logarithmic number of times, every constraint graph `G` reduces to a
constraint graph `H` of polynomial size such that `H` is satisfiable if `G` is, while
`H` has unsat value at least the constant `α` if `G` is unsatisfiable.

This is exactly the gap-producing reduction from constraint satisfaction to gap constraint
satisfaction that constitutes the PCP theorem.
-/
