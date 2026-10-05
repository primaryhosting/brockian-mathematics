import Mathlib

/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
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

set_option grind.warning false

namespace CS

/-! ## A model of bounded-memory (space-bounded) computation

A `Alg Q Ans In Out` is a deterministic algorithm which

* has a finite set `S` of memory configurations,
* starts, on input `x : In`, in configuration `init x`,
* in each configuration either *halts* with an output in `Out`, or issues a query `q : Q`
  about its (read-only) input and moves to a new configuration determined by the answer.

The *space* used by the algorithm is `Nat.log 2 (card A)`, so "logarithmic space" means
`A.card ≤ p n` for a polynomial `p`.  This is the standard configuration-counting
characterisation of deterministic logarithmic space: a machine with a read-only input and
`c * log n` bits of work memory has polynomially many configurations, and conversely.
-/

structure Alg (Q Ans In Out : Type) where
  /-- The finite set of memory configurations. -/
  S : Type
  /-- Finiteness of the configuration space. -/
  fin : Fintype S
  /-- Initial configuration on a given input. -/
  init : In → S
  /-- In each configuration, either query the input and continue, or halt with an output. -/
  trans : S → ((Q × (Ans → S)) ⊕ Out)

namespace Alg

variable {Q Ans In Out : Type}

/-- The number of memory configurations; `Nat.log 2` of it is the space used. -/

lemma enc_lt {d : ℕ} (hd : 0 < d) : ∀ l : List (Fin d), enc d l < d ^ l.length := by
  intro l
  induction l with
  | nil => simpa [enc] using hd
  | cons a l ih =>
      have h1 : enc d l + 1 ≤ d ^ l.length := ih
      have h2 : (a : ℕ) + d * enc d l < d * (enc d l + 1) := by
        have := a.isLt
        nlinarith [a.isLt]
      calc (a : ℕ) + d * enc d l < d * (enc d l + 1) := h2
        _ ≤ d * d ^ l.length := Nat.mul_le_mul_left _ h1
        _ = d ^ (l.length + 1) := by ring
      
/-- The walk determined by the digits of `enc d l` is exactly the walk with labels `l`. -/
