/-
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace CS

/-!
## Setting

We formalise the derandomisation half of the Impagliazzo–Wigderson theorem:

*strong circuit lower bounds ⟹ P = BPP.*

The hardness-versus-randomness construction (Nisan–Wigderson generator together with
hardness amplification) turns a function in `E` requiring circuits of size `2^{Ω(n)}`
into a pseudorandom generator `G` with logarithmic seed length that fools all
polynomial-size circuits with error `1/6`.  That generator is taken here as the
hypothesis `hPRG` (together with the logarithmic seed length `hlog`), and what is
proved is that such a generator collapses `BPP` into `P`: the bounded-error
randomised algorithm `A` is replaced by a deterministic majority vote over the
polynomially many outputs of `G`, and this deterministic procedure decides the
language exactly.

Inputs are bit strings (`List Bool`), a language is a predicate `L : List Bool → Bool`,
and a randomised algorithm on inputs of length `n` uses `m n` random bits.
-/

/-- The acceptance probability of a test `f` on `m` uniform random bits, i.e. the
fraction of the `2 ^ m` random strings on which `f` outputs `true`. -/

def majorityVote {t : ℕ} (f : Fin t → Bool) : Bool :=
  decide (t < 2 * (Finset.univ.filter fun i => f i = true).card)

/-- `L` is decided deterministically in polynomial time given the (polynomial-time)
algorithm `A`: there is a polynomially bounded family of seeds, computed
deterministically from the input, such that the majority vote of `A` over those seeds
decides `L` on every input. -/
