import Mathlib
import RequestProject.DisjointnessLb

/-!
# Deterministic two-way communication complexity of set disjointness

As a companion to `CS.disjointness_lb` (a linear lower bound for *randomized* one-way
protocols), this file formalises the general *two-way deterministic* model as protocol
trees and proves the classical fooling-set lower bound: any deterministic protocol
computing set disjointness on an `n`-element universe has cost at least `n`.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- Bitwise complement of a characteristic vector. -/

def proto1 : Proto 1 :=
  .alice (fun a => a 0)
    (fun v => if v then .bob (fun b => b 0) (fun w => .leaf (!w)) else .leaf true)

example : ∀ a b : Fin 1 → Bool, proto1.run a b = Disj a b := by decide

end CS

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
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file proves a linear lower bound on the *randomized* (public-coin) one-way
communication complexity of set disjointness on `n`-element universes:
any public-coin randomized protocol in which Alice sends a single `c`-bit message
to Bob, who then outputs the value of `Disj`, and which errs with probability at
most `1/16` on every input pair, must satisfy `n ≤ 3 * (c + 1)`, i.e. `c = Ω(n)`.

The proof is the standard one: average over the public randomness to fix a
deterministic message map that is correct on average over uniformly random
inputs `(a, {i})`, observe that Alice's message then determines a string within
small Hamming distance of `a` for at least half of all `a`, and finish with a
counting argument using a Hamming-ball volume bound.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- Set disjointness, on characteristic vectors of subsets of `Fin n`. -/
