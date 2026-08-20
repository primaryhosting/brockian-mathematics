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

lemma accProb_eq_one_sub_unsatWith (G : ConstraintGraph) (a : Fin G.n → Fin (G.q + 1)) :
    G.accProb a = 1 - G.unsatWith a := by
  have hs : (G.size : ℚ) ≠ 0 := by exact_mod_cast (G.size_pos).ne'
  have hlen : G.size
      = G.edges.countP (fun e => e.2.2 (a e.1) (a e.2.1))
        + G.edges.countP (fun e => ! e.2.2 (a e.1) (a e.2.1)) := by
    have := List.length_eq_countP_add_countP (l := G.edges)
      (fun e => e.2.2 (a e.1) (a e.2.1))
    simpa [size, Bool.not_eq_true'] using this
  have hlen' : (G.size : ℚ)
      = (G.edges.countP (fun e => e.2.2 (a e.1) (a e.2.1)) : ℚ)
        + (G.edges.countP (fun e => ! e.2.2 (a e.1) (a e.2.1)) : ℚ) := by
    exact_mod_cast hlen
  unfold accProb unsatWith
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hs]
  exact hlen'.symm

/-- If every assignment violates the same fraction `c` of constraints, then the gap is `c`. -/
