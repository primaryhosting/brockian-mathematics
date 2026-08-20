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

/-
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Dinur's gap amplification and the PCP theorem (CSP form)

This file formalizes the combinatorial skeleton of Irit Dinur's proof of the PCP theorem.

We model a *constraint graph* as a finite nonempty list of binary constraints over a finite
alphabet `Fin (q+1)`, with variables indexed by `Fin n`.  For an assignment `a` the quantity
`unsatWith G a` is the fraction of constraints violated by `a`, and `unsat G` is the minimum
of this quantity over all assignments (the *unsat value*, or gap, of `G`).

Dinur's key technical result is the *gap amplification step*: there are a fixed alphabet size
`q0`, a constant `C` and a constant `α > 0` such that every constraint graph `G` over
`Fin (q0+1)` can be transformed into a constraint graph `step G` over the same alphabet with

* `size (step G) ≤ C * size G`   (linear blow-up),
* `min (2 * unsat G) α ≤ unsat (step G)`  (the gap doubles, until it reaches `α`),
* `unsat G = 0 → unsat (step G) = 0`  (perfect completeness is preserved).

This is packaged as the structure `CS.Amplifier`.  The main theorem `CS.pcp_dinur` shows how
the PCP theorem, in its equivalent "gap constraint satisfaction" form, follows: iterating the
amplification step `O(log (size G))` many times yields, in polynomial size, a constraint graph
whose gap is either `0` (if `G` is satisfiable) or at least the absolute constant `α`.

The efficiency (polynomial-time computability) of the reduction is *not* modelled here -- only
its size behaviour; correspondingly `CS.Amplifier` is a purely combinatorial hypothesis, and
`CS.amplifier_nonempty` records that it is consistent (so the main theorem is not vacuous).
-/

namespace CS

/-- A *constraint graph*: `n` variables taking values in the alphabet `Fin (q+1)`, together with
a nonempty list of binary constraints, each given by a pair of variables and a boolean relation
on the alphabet. -/
structure ConstraintGraph where
  /-- number of variables -/
  n : ℕ
  /-- the alphabet is `Fin (q+1)` -/
  q : ℕ
  /-- the list of constraints -/
  edges : List (Fin n × Fin n × (Fin (q + 1) → Fin (q + 1) → Bool))
  /-- there is at least one constraint -/
  edges_ne : edges ≠ []

namespace ConstraintGraph

/-- The size of a constraint graph is its number of constraints. -/

lemma pow_log_le_pow (C N : ℕ) : C ^ Nat.log 2 N ≤ (N + 1) ^ (Nat.log 2 C + 1) := by
  have h2 : (2:ℕ) ^ Nat.log 2 N ≤ N + 1 := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · simp [hN]
    · exact le_trans (Nat.pow_log_le_self 2 hN.ne') (Nat.le_succ N)
  have hC : C ≤ 2 ^ (Nat.log 2 C + 1) := (Nat.lt_pow_succ_log_self (by norm_num) C).le
  calc C ^ Nat.log 2 N ≤ (2 ^ (Nat.log 2 C + 1)) ^ Nat.log 2 N := Nat.pow_le_pow_left hC _
    _ = (2 ^ Nat.log 2 N) ^ (Nat.log 2 C + 1) := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (N + 1) ^ (Nat.log 2 C + 1) := Nat.pow_le_pow_left h2 _

/-- **The PCP theorem in gap-CSP form, via Dinur's gap amplification.**

Given a gap amplification step `A` (Dinur's main technical lemma), there are constants `c`, `d`
such that every constraint graph `G` over the alphabet `Fin (A.q0 + 1)` can be transformed into a
constraint graph `G'` over the same alphabet, of size at most `c * (size G + 1) ^ d`, such that

* if `G` is satisfiable then so is `G'` (perfect completeness), and
* if `G` is unsatisfiable then *every* assignment to `G'` violates at least an `A.alpha` fraction
  of its constraints (soundness with an absolute constant gap).

Thus deciding satisfiability of constraint graphs reduces, in polynomial size, to distinguishing
satisfiable instances from instances with constant gap: the PCP theorem. -/
