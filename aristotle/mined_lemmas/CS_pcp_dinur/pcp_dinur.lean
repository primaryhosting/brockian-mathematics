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

theorem pcp_dinur (A : Amplifier) :
    ∃ c d : ℕ, ∀ G : ConstraintGraph, G.q = A.q0 →
      ∃ G' : ConstraintGraph,
        G'.q = A.q0 ∧
        G'.size ≤ c * (G.size + 1) ^ d ∧
        (G.unsat = 0 → G'.unsat = 0) ∧
        (G.unsat ≠ 0 → A.alpha ≤ G'.unsat) := by
  set a : ℕ := ⌈A.alpha⌉₊ with ha
  set d : ℕ := Nat.log 2 A.C + 1 with hd
  refine ⟨A.C * (a + 1) ^ d, d + 1, ?_⟩
  intro G hG
  set m : ℕ := G.size with hm
  set N : ℕ := ⌈A.alpha * m⌉₊ with hN
  set k : ℕ := Nat.log 2 N + 1 with hk
  refine ⟨A.step^[k] G, A.iterate_alphabet k G hG, ?_, ?_, ?_⟩
  · -- size bound
    have h1 : (A.step^[k] G).size ≤ A.C ^ k * m := A.iterate_size k G
    have h2 : A.C ^ k = A.C * A.C ^ Nat.log 2 N := by rw [hk, pow_succ]; ring
    have h3 : A.C ^ Nat.log 2 N ≤ (N + 1) ^ d := pow_log_le_pow A.C N
    have hNa : N ≤ a * m := by
      rw [hN, Nat.ceil_le]
      push_cast
      exact mul_le_mul_of_nonneg_right (Nat.le_ceil A.alpha) (by positivity)
    have h4 : N + 1 ≤ (a + 1) * (m + 1) := by nlinarith [hNa, Nat.zero_le a, Nat.zero_le m]
    calc (A.step^[k] G).size ≤ A.C ^ k * m := h1
      _ = A.C * A.C ^ Nat.log 2 N * m := by rw [h2]
      _ ≤ A.C * (N + 1) ^ d * m := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h3)
      _ ≤ A.C * ((a + 1) * (m + 1)) ^ d * (m + 1) := by
          exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h4 _))
            (Nat.le_succ m)
      _ = A.C * (a + 1) ^ d * ((m + 1) ^ d * (m + 1)) := by rw [Nat.mul_pow]; ring
      _ = A.C * (a + 1) ^ d * (m + 1) ^ (d + 1) := by ring
  · -- completeness
    exact fun h => A.iterate_complete k G h
  · -- soundness
    intro h
    have hgap := A.iterate_gap k G hG
    have hmpos : (0:ℚ) < m := by exact_mod_cast G.size_pos
    have hu : 1 / (m:ℚ) ≤ G.unsat := G.inv_size_le_unsat h
    -- `2 ^ k` exceeds `A.alpha * m`
    have hNlt : (N:ℚ) < 2 ^ k := by
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
      exact_mod_cast this
    have hle : A.alpha * m ≤ (N:ℚ) := by
      rw [hN]; exact_mod_cast Nat.le_ceil (A.alpha * m)
    have hkey : A.alpha ≤ 2 ^ k * G.unsat := by
      have h1 : A.alpha * m ≤ (2:ℚ) ^ k := le_of_lt (lt_of_le_of_lt hle hNlt)
      have h2 : (2:ℚ) ^ k * (1 / m) ≤ 2 ^ k * G.unsat := by
        have : (0:ℚ) < 2 ^ k := by positivity
        exact mul_le_mul_of_nonneg_left hu this.le
      have h3 : A.alpha ≤ (2:ℚ) ^ k * (1 / m) := by
        rw [mul_one_div, le_div_iff₀ hmpos]
        exact h1
      linarith
    rw [min_eq_right hkey] at hgap
    exact hgap

/-- **The PCP theorem, verifier formulation.**

Restating `CS.pcp_dinur` in terms of the canonical two-query verifier attached to a constraint
graph: satisfiability of constraint graphs reduces, with polynomial size blow-up, to a promise
problem for a verifier that reads only two symbols of the proof and has perfect completeness and
soundness error at most `1 - A.alpha`. -/
