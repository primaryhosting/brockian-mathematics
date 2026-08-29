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

theorem enumAlg_decides (N d D : ℕ) (hd : 0 < d) (nbr : Fin N → Fin d → Fin N)
    (hdiam : ∀ v w : Fin N, WalkReach nbr v w → ∃ l : List (Fin d),
      l.length ≤ D ∧ walk nbr v l = w) (s t : Fin N) :
    ∃ b : Bool, (enumAlg N d D hd).Outputs (nbrOracle nbr) (s, t) b ∧
      (b = true ↔ WalkReach nbr s t) := by
  by_cases hreach : WalkReach nbr s t
  · refine ⟨true, ?_, by simp [hreach]⟩
    obtain ⟨l, hlen, hl⟩ := hdiam s t hreach
    have hk : enc d l < d ^ D :=
      lt_of_lt_of_le (enc_lt hd l) (Nat.pow_le_pow_right hd hlen)
    rcases run_outer hd nbr s t (enc d l) hk with h0 | h
    · rcases run_inner hd nbr s t ⟨enc d l, hk⟩ h0 l.length (by omega) with ⟨n, hn⟩ | h
      · refine ⟨n + 1, ?_⟩
        have hv : posP nbr hd s (enc d l) l.length = t := by
          rw [posP_enc nbr hd l s, hl]
        have hstep : erun hd nbr s t (n + 1) = Sum.inr true := by
          rw [erun_succ, hn]
          simp [Alg.stepOnce, enumAlg, etrans, hv]
        show (enumAlg N d D hd).out (erun hd nbr s t (n + 1)) = some true
        rw [hstep]; simp [Alg.out, enumAlg, etrans]
      · exact h
    · exact h
  · refine ⟨false, ?_, by simp [hreach]⟩
    have hne : ∀ (k j : ℕ), posP nbr hd s k j ≠ t := by
      intro k j hcontra
      obtain ⟨l, _, hl⟩ := posP_walk nbr hd j s k
      exact hreach ⟨l, by rw [hl, hcontra]⟩
    have hd0 : 0 < d ^ D := Nat.pos_pow_of_pos _ hd
    rcases run_outer hd nbr s t (d ^ D - 1) (by omega) with h0 | h
    · rcases run_inner hd nbr s t ⟨d ^ D - 1, by omega⟩ h0 D le_rfl with ⟨n, hn⟩ | h
      · refine ⟨n + 1, ?_⟩
        have hvt : posP nbr hd s (d ^ D - 1) D ≠ t := hne _ _
        have hk : ¬ ((d ^ D - 1) + 1 < d ^ D) := by omega
        have hstep : erun hd nbr s t (n + 1) = Sum.inr false := by
          rw [erun_succ, hn]
          simp [Alg.stepOnce, enumAlg, etrans, hvt, hk]
        show (enumAlg N d D hd).out (erun hd nbr s t (n + 1)) = some false
        rw [hstep]; simp [Alg.out, enumAlg, etrans]
      · exact absurd (sound_true hd nbr s t h.choose h.choose_spec) hreach
    · exact absurd (sound_true hd nbr s t h.choose h.choose_spec) hreach

/-! ## Undirected `s`-`t` connectivity and the class L -/

/-- Undirected reachability in a graph given by a symmetric Boolean adjacency matrix. -/
