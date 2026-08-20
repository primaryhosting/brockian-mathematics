import Mathlib
import RequestProject.Circuits

/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option autoImplicit false

/-!
## Overview

This file formalises the statement `NP = PCP(log n, O(1))` (the PCP theorem) in the
non-uniform (Boolean circuit) model of efficient computation, and proves the "easy"
inclusion `PCP(log n, O(1)) ⊆ NP` in full.

*  A language is a predicate on bit strings (`CS.Language`).
*  `CS.InNP L` says that `L` has a polynomial-length witness that is checked by a
   polynomial-size Boolean circuit.
*  `CS.InPCP L` says that `L` has a probabilistically checkable proof system with
   `O(log n)` random bits, a constant number `q` of queries, perfect completeness and
   soundness error at most `1/2`; the query positions and the decision predicate are
   computed by polynomial-size circuits.

`CS.pcp_subset_np` proves `PCP(log n, O(1)) ⊆ NP` unconditionally: a witness for the NP
system is the table of answers of the PCP verifier on all `2^{O(log n)} = poly(n)` random
strings, together with the consistency requirement that two queries landing on the same
proof position receive the same answer.

Proof positions are named by bit strings of length `pbits n` with `pbits` polynomially
bounded; since the verifier only ever inspects `2 ^ rlen n * q = poly(n)` positions, no
further restriction on the proof length is needed.

The reverse inclusion `NP ⊆ PCP(log n, O(1))` is the deep content of the PCP theorem
(Arora–Safra, Arora–Lund–Motwani–Sudan–Szegedy); it is *not* proved here, and appears as
an explicit hypothesis `hard` of `CS.pcp_theorem`.
-/

namespace CS

/-- A language: a set of finite bit strings. -/
abbrev Language := List Bool → Prop

/-- The variable assignment described by a bit string (out-of-range variables are `false`). -/

lemma size_comp_le (c : Circ) (s : ℕ → Circ) (S : ℕ) (h : ∀ i, (s i).size ≤ S) :
    (c.comp s).size ≤ c.size * (S + 1) := by
  induction c with
  | var i => simpa [comp, size] using le_trans (h i) (Nat.le_succ S)
  | cst b => simp [comp, size]
  | neg c ih =>
      have : (c.comp s).size + 1 ≤ c.size * (S + 1) + (S + 1) := by omega
      simpa [comp, size, Nat.succ_mul, Nat.add_mul] using this
  | conj a b iha ihb =>
      have : (a.comp s).size + (b.comp s).size + 1
          ≤ a.size * (S + 1) + b.size * (S + 1) + (S + 1) := by omega
      simpa [comp, size, Nat.add_mul] using this
  | disj a b iha ihb =>
      have : (a.comp s).size + (b.comp s).size + 1
          ≤ a.size * (S + 1) + b.size * (S + 1) + (S + 1) := by omega
      simpa [comp, size, Nat.add_mul] using this

/-- Conjunction of a list of circuits. -/
