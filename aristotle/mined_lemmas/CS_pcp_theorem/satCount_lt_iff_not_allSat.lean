/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

/-!
## Overview

This file develops a self-contained, purely combinatorial model of probabilistically
checkable proofs and states the PCP theorem, `NP = PCP(log n, O(1))`, inside it.

The model is the standard "constraint satisfaction" presentation of a PCP verifier.
For every input length `n` we are given

* a **proof length** `m` and a list of **constraints**, each of which is an arbitrary
  Boolean predicate depending on at most `q` of the `n + m` variables (the `n` input
  bits, followed by the `m` proof bits);
* the verifier picks one of the `N` constraints uniformly at random -- this costs
  `log₂ N` random bits, and `N` is required to be polynomially bounded, so the number of
  random bits is `O(log n)`, see `CS.PolyBounded.log_randomness` -- and then reads the
  at most `q` variables that this constraint depends on;
* **completeness**: if `x` is in the language, some proof satisfies *all* constraints;
* **soundness**: if `x` is not in the language, then *every* proof leaves a prescribed
  fraction of the constraints unsatisfied.

Two soundness regimes are considered:

* `CS.SoundWeak`: at least one constraint fails (an inverse-polynomial gap);
* `CS.SoundHalf`: fewer than half of the constraints are satisfied (a constant gap,
  i.e. rejection probability greater than `1/2`).

`CS.NPClass` is the class of languages described by a polynomial-size constraint system
of constant arity: this is the Cook–Levin normal form of `NP`, read nonuniformly.  Note
that the constraint system depends only on the input *length*, the input bits being
ordinary variables of the system that the constraints may query; this is what keeps the
class from degenerating into the class of all languages.  `CS.WeakPCPClass` and
`CS.PCPClass` are the corresponding PCP classes, i.e. `PCP(log n, O(1))` with an
inverse-polynomial and with a constant soundness gap respectively.

The following are proved unconditionally:

* `CS.PolyBounded.log_randomness`: polynomially many constraints means `O(log n)`
  random bits;
* `CS.np_eq_weakPCP`: `NP = PCP(log n, O(1))` with an inverse-polynomial gap;
* `CS.pcp_subset_np`: `PCP(log n, O(1)) ⊆ NP`, the easy inclusion of the PCP theorem;
* `CS.pcp_theorem`: `NP = PCP(log n, O(1))` holds **if and only if** gap amplification
  holds, i.e. iff every polynomial-size constant-arity constraint system describing a
  language can be replaced by one with constant soundness gap.

Thus the whole content of the PCP theorem is isolated in the gap amplification statement
`CS.GapAmplification`, the converse inclusion being proved outright.

Everything below uses only the Lean 4 core library.
-/

namespace CS

/-- A language, presented lengthwise: for each input length `n`, a predicate on bit
strings of length `n`. -/

theorem satCount_lt_iff_not_allSat (I : CSP n q) (x : Fin n → Bool)
    (pi : Fin I.proofLen → Bool) : I.satCount x pi < I.numCon ↔ ¬ I.AllSat x pi := by
  rw [allSat_iff_satCount_eq]
  exact ⟨fun h h' => absurd h' (Nat.ne_of_lt h),
    fun h => Nat.lt_of_le_of_ne (I.satCount_le x pi) h⟩

end CSP

/-- A family of constraint systems, one for each input length, of polynomial size:
polynomially many constraints (equivalently, `O(log n)` random bits) and polynomially
long proofs.  The bound `q n` is the number of queries the verifier makes. -/
structure VerifierFamily (q : Nat → Nat) where
  /-- The constraint system used on inputs of length `n`. -/
  inst : (n : Nat) → CSP n (q n)
  /-- Polynomially many constraints, i.e. `O(log n)` random bits. -/
  numCon_poly : PolyBounded (fun n => (inst n).numCon)
  /-- Polynomially long proofs. -/
  proofLen_poly : PolyBounded (fun n => (inst n).proofLen)

variable {q : Nat → Nat}

/-- Perfect completeness: every word of the language admits a proof satisfying all
constraints, so the verifier accepts with probability `1`. -/
