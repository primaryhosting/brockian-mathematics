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

lemma sound_true (n : ℕ) (h : (enumAlg N d D hd).out (erun hd nbr s t n) = some true) :
    WalkReach nbr s t := by
  have hg := good_erun hd nbr s t n
  match hσ : erun hd nbr s t n with
  | Sum.inr b =>
      rw [hσ] at h
      have hb : b = true := by
        simpa [Alg.out, enumAlg, etrans] using h
      rw [hσ] at hg
      exact hg hb
  | Sum.inl (s', t', k, j, v) =>
      rw [hσ] at h
      simp only [Alg.out, enumAlg, etrans] at h
      by_cases hvt : v = t'
      · simp [hvt] at h
        -- halted with `true`; extract reachability from the invariant
        rw [hσ] at hg
        obtain ⟨rfl, rfl, hv⟩ := hg
        obtain ⟨l, _, hl⟩ := posP_walk nbr hd (j : ℕ) s (k : ℕ)
        exact ⟨l, by rw [hl, ← hv, hvt]⟩
      · by_cases hj : (j : ℕ) < D
        · simp [hvt, hj] at h
        · by_cases hk : (k : ℕ) + 1 < d ^ D
          · simp [hvt, hj, hk] at h
          · simp [hvt, hj, hk] at h

/-- Inner loop: from the start of the `k`-th label sequence we reach every step `j ≤ D`
of that sequence, unless the algorithm has already answered `true`. -/
