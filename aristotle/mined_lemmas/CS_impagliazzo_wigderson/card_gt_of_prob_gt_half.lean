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

theorem card_gt_of_prob_gt_half {s : ℕ} (f : (Fin s → Bool) → Bool) (h : 1 / 2 < prob f) :
    2 ^ s < 2 * (Finset.univ.filter fun y => f y = true).card := by
  rw [prob, lt_div_iff₀ (by positivity)] at h
  have : ((2 : ℚ) ^ s : ℚ) < 2 * ((Finset.univ.filter fun y => f y = true).card : ℚ) := by
    linarith
  exact_mod_cast this

/-- **Impagliazzo–Wigderson (derandomisation form): strong circuit lower bounds imply
`P = BPP`.**

Assume `L` is decided by a bounded-error randomised algorithm `A` using `m n` random
bits on inputs of length `n` (`hBPP`: the algorithm is correct with probability more
than `2/3`).  Assume moreover that the hardness-versus-randomness construction supplies
a pseudorandom generator `G` with seed length `s n` which fools the tests attached to
`A` with error at most `1/6` (`hPRG`) and whose seed length is logarithmic, so that the
seed space has polynomial size (`hlog`).

Then `L` is decided deterministically by the majority vote of `A` over the polynomially
many pseudorandom strings `G y`, i.e. `L ∈ P` (relative to the deterministic
polynomial-time algorithm `A`). -/
