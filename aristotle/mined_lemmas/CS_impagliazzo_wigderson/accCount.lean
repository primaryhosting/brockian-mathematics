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

def accCount (A : Str → Nat → Bool) (m : Nat → Nat) (x : Str) : Nat :=
  countLt (A x) (2 ^ m x.length)

/-! ### An abstract model of deterministic polynomial time -/

/-- An abstract model of deterministic polynomial-time computation.

Rather than committing to a concrete machine model we record those closure properties
of deterministic polynomial time that the derandomisation argument uses.  Every
standard machine model (multitape Turing machines, RAMs, …) satisfies them. -/
structure Model where
  /-- `Poly1 f`: the language `f` is decidable in deterministic polynomial time. -/
  Poly1 : (Str → Bool) → Prop
  /-- `Poly2 A`: the randomised algorithm `A`, taking an input string and a random
  string (encoded as a natural number), runs in deterministic polynomial time. -/
  Poly2 : (Str → Nat → Bool) → Prop
  /-- `InE f`: the family `f` of Boolean functions (`f n` is a function of `n` input
  bits, presented as a number `< 2 ^ n`) is computable in deterministic time
  `2 ^ O(n)`, i.e. it lies in the class `E`. -/
  InE : (Nat → Nat → Bool) → Prop
  /-- `PolyGen l G`: the generator family `G`, with seed length `l n` on inputs of
  length `n`, is computable in deterministic polynomial time. -/
  PolyGen : (Nat → Nat) → (Nat → Nat → Nat) → Prop
  /-- A deterministic polynomial-time algorithm is in particular a randomised
  polynomial-time algorithm which ignores its randomness. -/
  poly2_const : ∀ f : Str → Bool, Poly1 f → Poly2 (fun x _ => f x)
  /-- Cook–Levin style simulation: for a polynomial-time randomised algorithm `A`
  using `m n` random bits on inputs of length `n`, there is a polynomial size bound
  `s` such that for every input `x` the map `r ↦ A x r` is computed on all `m |x|`-bit
  strings by a circuit on `m |x|` inputs of size at most `s |x|`. -/
  circuit_sim : ∀ (A : Str → Nat → Bool) (m : Nat → Nat), Poly2 A → PolyBound m →
    ∃ s : Nat → Nat, PolyBound s ∧ ∀ x : Str, ∃ C : Circuit,
      C.usesOnly (m x.length) = true ∧ C.size ≤ s x.length ∧
        ∀ k, k < 2 ^ m x.length → C.eval k = A x k
  /-- Deterministic polynomial time is closed under taking the majority vote of a
  polynomial-time randomised algorithm over the polynomially many outputs of a
  polynomial-time generator with logarithmic seed length. -/
  derandomize : ∀ (A : Str → Nat → Bool) (l : Nat → Nat) (G : Nat → Nat → Nat),
    Poly2 A → PolyGen l G → SeedBound l →
    Poly1 (fun x => decide (2 ^ l x.length <
      2 * countLt (fun u => A x (G x.length u)) (2 ^ l x.length)))

namespace Model

variable (M : Model)

/-- The class `P`: languages decidable in deterministic polynomial time. -/
