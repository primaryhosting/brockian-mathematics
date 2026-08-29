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

lemma good_step (σ : ES N d D) (h : Good hd nbr s t σ) :
    Good hd nbr s t ((enumAlg N d D hd).stepOnce (nbrOracle nbr) σ) := by
  match σ with
  | Sum.inr b => simpa [Alg.stepOnce, enumAlg, etrans] using h
  | Sum.inl (s', t', k, j, v) =>
      obtain ⟨rfl, rfl, hv⟩ := h
      by_cases hvt : v = t
      · have : (enumAlg N d D hd).stepOnce (nbrOracle nbr) (Sum.inl (s, t, k, j, v))
            = Sum.inr true := by
          simp [Alg.stepOnce, enumAlg, etrans, hvt]
        rw [this]
        intro _
        obtain ⟨l, _, hl⟩ := posP_walk nbr hd (j : ℕ) s (k : ℕ)
        exact ⟨l, by rw [hl, ← hv, hvt]⟩
      · by_cases hj : (j : ℕ) < D
        · have : (enumAlg N d D hd).stepOnce (nbrOracle nbr) (Sum.inl (s, t, k, j, v))
              = Sum.inl (s, t, k, ⟨(j : ℕ) + 1, by omega⟩,
                  nbr v (digit d (k : ℕ) (j : ℕ) hd)) := by
            simp [Alg.stepOnce, enumAlg, etrans, hvt, hj, nbrOracle]
          rw [this]
          refine ⟨rfl, rfl, ?_⟩
          rw [hv, ← posP_succ]
        · by_cases hk : (k : ℕ) + 1 < d ^ D
          · have : (enumAlg N d D hd).stepOnce (nbrOracle nbr) (Sum.inl (s, t, k, j, v))
                = Sum.inl (s, t, ⟨(k : ℕ) + 1, hk⟩, ⟨0, Nat.succ_pos D⟩, s) := by
              simp [Alg.stepOnce, enumAlg, etrans, hvt, hj, hk, nbrOracle]
            rw [this]
            exact ⟨rfl, rfl, rfl⟩
          · have : (enumAlg N d D hd).stepOnce (nbrOracle nbr) (Sum.inl (s, t, k, j, v))
                = Sum.inr false := by
              simp [Alg.stepOnce, enumAlg, etrans, hvt, hj, hk]
            rw [this]
            simp

