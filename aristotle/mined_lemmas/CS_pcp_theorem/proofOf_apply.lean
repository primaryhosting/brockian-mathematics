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

lemma proofOf_apply (V : PCPVerifier) (x w : List Bool)
    (hcons : ∀ i < 2 ^ V.rlen x.length, ∀ j < V.q, ∀ i' < 2 ^ V.rlen x.length, ∀ j' < V.q,
      V.position x (rstr V x.length i) j = V.position x (rstr V x.length i') j' →
        w.getD (i * V.q + j) false = w.getD (i' * V.q + j') false)
    {i j : ℕ} (hi : i < 2 ^ V.rlen x.length) (hj : j < V.q) :
    proofOf V x w (V.position x (rstr V x.length i) j) = w.getD (i * V.q + j) false := by
  classical
  set p := V.position x (rstr V x.length i) j with hp
  set l := pairsList (2 ^ V.rlen x.length) V.q with hl
  set f : ℕ × ℕ → Bool := fun ij => V.position x (rstr V x.length ij.1) ij.2 == p with hf
  have hmem : (i, j) ∈ l := mem_pairsList.2 ⟨hi, hj⟩
  cases hfind : l.find? f with
  | none =>
      have hne := (List.find?_eq_none.1 hfind) (i, j) hmem
      simp only [hf, beq_iff_eq] at hne
      exact absurd hp.symm hne
  | some ij =>
      have hp' : f ij = true := List.find?_some hfind
      have hmem' : ij ∈ l := List.mem_of_find?_eq_some hfind
      obtain ⟨hi', hj'⟩ := mem_pairsList.1 (show (ij.1, ij.2) ∈ l by simpa using hmem')
      have hposeq : V.position x (rstr V x.length ij.1) ij.2 = p := by
        simpa [hf] using hp'
      have := hcons ij.1 hi' ij.2 hj' i hi j hj (by rw [hposeq, hp])
      simp only [proofOf, ← hl, ← hf, hfind]
      exact this

/-- **The easy inclusion of the PCP theorem**: every language with a `(O(log n), O(1))`
probabilistically checkable proof system is in NP. -/
