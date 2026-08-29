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

def satCount (I : CSP n q) (x : Fin n → Bool) (pi : Fin I.proofLen → Bool) : Nat :=
  I.con.countP (fun c => c.eval (Sum.elim x pi))

/-- All constraints are satisfied by the input `x` together with the proof `π`. -/
