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

lemma run_inner (k : Fin (d ^ D))
    (h0 : ∃ n, erun hd nbr s t n = Sum.inl (s, t, k, ⟨0, Nat.succ_pos D⟩, s)) :
    ∀ j : ℕ, ∀ hj : j ≤ D,
      (∃ n, erun hd nbr s t n =
          Sum.inl (s, t, k, ⟨j, Nat.lt_succ_of_le hj⟩, posP nbr hd s (k : ℕ) j)) ∨
      (∃ n, (enumAlg N d D hd).out (erun hd nbr s t n) = some true) := by
  intro j
  induction j with
  | zero => intro _; exact Or.inl h0
  | succ j ih =>
      intro hj
      have hj' : j ≤ D := by omega
      rcases ih hj' with ⟨n, hn⟩ | h
      · set v := posP nbr hd s (k : ℕ) j with hvdef
        by_cases hvt : v = t
        · refine Or.inr ⟨n + 1, ?_⟩
          have hstep : erun hd nbr s t (n + 1) = Sum.inr true := by
            rw [erun_succ, hn]
            simp [Alg.stepOnce, enumAlg, etrans, hvt]
          rw [hstep]
          simp [Alg.out, enumAlg, etrans]
        · have hjD : j < D := by omega
          refine Or.inl ⟨n + 1, ?_⟩
          rw [erun_succ, hn]
          have : (enumAlg N d D hd).stepOnce (nbrOracle nbr)
              (Sum.inl (s, t, k, (⟨j, Nat.lt_succ_of_le hj'⟩ : Fin (D + 1)), v))
              = Sum.inl (s, t, k, ⟨j + 1, by omega⟩,
                  nbr v (digit d (k : ℕ) j hd)) := by
            simp [Alg.stepOnce, enumAlg, etrans, hvt, hjD, nbrOracle]
          rw [this, hvdef, ← posP_succ]
      · exact Or.inr h

/-- Outer loop: the algorithm starts every label sequence, unless it answers `true` first. -/
