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

lemma run_outer :
    ∀ k : ℕ, ∀ hk : k < d ^ D,
      (∃ n, erun hd nbr s t n = Sum.inl (s, t, ⟨k, hk⟩, ⟨0, Nat.succ_pos D⟩, s)) ∨
      (∃ n, (enumAlg N d D hd).out (erun hd nbr s t n) = some true) := by
  intro k
  induction k with
  | zero => intro hk; exact Or.inl ⟨0, rfl⟩
  | succ k ih =>
      intro hk
      have hk' : k < d ^ D := by omega
      rcases ih hk' with h0 | h
      · rcases run_inner hd nbr s t ⟨k, hk'⟩ h0 D le_rfl with ⟨n, hn⟩ | h
        · set v := posP nbr hd s k D with hvdef
          by_cases hvt : v = t
          · refine Or.inr ⟨n + 1, ?_⟩
            have hstep : erun hd nbr s t (n + 1) = Sum.inr true := by
              rw [erun_succ, hn]
              simp [Alg.stepOnce, enumAlg, etrans, hvt]
            rw [hstep]; simp [Alg.out, enumAlg, etrans]
          · refine Or.inl ⟨n + 1, ?_⟩
            rw [erun_succ, hn]
            simp [Alg.stepOnce, enumAlg, etrans, hvt, hk, nbrOracle]
        · exact Or.inr h
      · exact Or.inr h

end Correct

/-- **The exhaustive-walk algorithm is correct.**  If every pair of vertices joined by a
walk is joined by a walk of length at most `D`, then `enumAlg` decides reachability. -/
