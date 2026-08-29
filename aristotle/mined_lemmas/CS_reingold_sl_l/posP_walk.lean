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

lemma posP_walk {N d : ℕ} (nbr : Fin N → Fin d → Fin N) (hd : 0 < d) :
    ∀ (j : ℕ) (v : Fin N) (k : ℕ), ∃ l : List (Fin d), l.length = j ∧
      walk nbr v l = posP nbr hd v k j := by
  intro j
  induction j with
  | zero => intro v k; exact ⟨[], rfl, rfl⟩
  | succ j ih =>
      intro v k
      obtain ⟨l, hl, hw⟩ := ih (nbr v (digit d k 0 hd)) (k / d)
      exact ⟨digit d k 0 hd :: l, by simp [hl], by simpa [walk] using hw⟩

/-- Base-`d` encoding of a list of digits (least significant first). -/
