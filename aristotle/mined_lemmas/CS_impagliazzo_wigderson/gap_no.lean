/-!
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
## Overview

This file formalises the *hardness versus randomness* theorem of Impagliazzo and
Wigderson: strong (exponential) circuit lower bounds imply `P = BPP`.

The development is self contained (it uses only the Lean 4 core library) and is
organised in three clearly separated layers.

* **Boolean circuits and pseudorandomness.**  Boolean circuits, their size, the
  number of accepted inputs of a Boolean function, and the notion of a *pseudorandom
  generator* (a map on short seeds whose output distribution `1/12`-fools every small
  circuit) are defined concretely.  The derandomisation gap lemma
  (`CS.fooled_gap`) — the combinatorial heart of the argument — is proved from
  scratch: a fooled circuit whose acceptance probability is at least `2/3` accepts a
  strict majority of the generator's seeds, and one whose acceptance probability is at
  most `1/3` does not.

* **An abstract model of deterministic polynomial time.**  Rather than fixing a
  Turing machine model, the structure `CS.Model` axiomatises the standard closure
  properties of deterministic polynomial time that the argument needs: a deterministic
  algorithm is a randomised algorithm ignoring its randomness (`poly2_const`), a
  polynomial-time randomised algorithm is simulated on each input by a polynomial-size
  circuit acting on its random bits (`circuit_sim`, Cook–Levin), and polynomial time is
  closed under taking a majority vote over a polynomially large seed space
  (`derandomize`).  The classes `Model.P` and `Model.BPP` are then defined in the usual
  way, `BPP` with the standard two-sided error bounds `2/3` and `1/3`.

* **The Nisan–Wigderson / Impagliazzo–Wigderson generator.**  The construction of a
  pseudorandom generator with logarithmic seed length out of an exponentially hard
  function is taken as an explicit hypothesis `hIW` of the main theorem; the strong
  circuit lower bound itself is the hypothesis `hHard`.

The main theorem `CS.impagliazzo_wigderson` then proves `BPP = P`.  Both inclusions
are established; the substantial one derandomises an arbitrary `BPP` algorithm by
taking the majority vote of its answers over all seeds of the generator.

Randomness is modelled by a natural number `k < 2 ^ m` whose bits `k.testBit i`,
`i < m`, are the `m` random bits; the uniform distribution on `{0,1}^m` is therefore
the uniform distribution on `{0, …, 2^m - 1}`, and probabilities are expressed as
counting inequalities between natural numbers.
-/

namespace CS

/-- Binary strings, the inputs of our algorithms. -/
abbrev Str := List Bool

/-- A language is a predicate on binary strings. -/
abbrev Lang := Str → Bool

/-! ### Counting -/

/-- `countLt p N` is the number of `k < N` with `p k = true`. -/

theorem gap_no {a b L M : Nat} (hM : 0 < M)
    (h : 12 * a * M ≤ 12 * b * L + L * M) (hb : 3 * b ≤ M) : 2 * a ≤ L := by
  have h1 : (4 * L) * (3 * b) ≤ (4 * L) * M := Nat.mul_le_mul_left _ hb
  have h2 : (12 * a) * M ≤ (5 * L) * M := by grind
  have h3 : 12 * a ≤ 5 * L := Nat.le_of_mul_le_mul_right h2 hM
  omega

/-- **The derandomisation gap lemma.**  If `G` `1/12`-fools all circuits of size `s`
on `m` inputs and `C` is such a circuit, then the majority vote of `C` over all seeds
of `G` reproduces the answer of `C` under the uniform distribution, provided the
latter has two-sided error at most `1/3`. -/
