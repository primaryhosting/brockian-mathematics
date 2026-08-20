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

theorem ppoly_subset_pcp {L : Language} (h : InPpoly L) : InPCP L := by
  obtain ⟨C, hpoly, hC⟩ := h
  refine ⟨{ q := 0, rlen := fun _ => 0, pbits := fun _ => 0,
            posCirc := fun _ _ _ => Circ.cst false, accCirc := C,
            rand_log := by simpa using isPoly_const 1,
            pbits_poly := isPoly_const 0,
            pos_size_poly := ⟨1, 0, by simp [Circ.size]⟩,
            acc_size_poly := hpoly }, ?_, ?_⟩
  · intro x hx
    refine ⟨fun _ => false, ?_⟩
    intro r hr
    have hrnil : r = [] := List.length_eq_zero_iff.1 (mem_allBits.1 hr)
    subst hrnil
    have : (C x.length).eval (asFun x) = true := (hC x).1 hx
    simpa [PCPVerifier.Accepts, PCPVerifier.acc, PCPVerifier.accWith,
      PCPVerifier.answers] using this
  · intro x hx pi
    have hfalse : (C x.length).eval (asFun x) = false := by
      cases hv : (C x.length).eval (asFun x) with
      | false => rfl
      | true => exact absurd ((hC x).2 hv) hx
    simp [PCPVerifier.acceptCount, allBits, PCPVerifier.acc, PCPVerifier.accWith,
      PCPVerifier.answers, hfalse]

/-! ## The PCP theorem -/

/-- **The PCP theorem**, `NP = PCP(log n, O(1))`.

The inclusion `PCP(log n, O(1)) ⊆ NP` is proved here unconditionally
(`CS.pcp_subset_np`).  The converse inclusion `NP ⊆ PCP(log n, O(1))` — the deep half of
the PCP theorem of Arora–Safra and Arora–Lund–Motwani–Sudan–Szegedy — is taken as the
hypothesis `hard`; it is not proved in this development. -/
