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

lemma posP_enc {N d : ℕ} (nbr : Fin N → Fin d → Fin N) (hd : 0 < d) :
    ∀ (l : List (Fin d)) (v : Fin N), posP nbr hd v (enc d l) l.length = walk nbr v l := by
  intro l
  induction l with
  | nil => intro v; rfl
  | cons a l ih =>
      intro v
      have hmod : digit d (enc d (a :: l)) 0 hd = a := by
        apply Fin.ext
        simp [digit, enc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
      have hdiv : enc d (a :: l) / d = enc d l := by
        simp [enc, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt a.isLt]
      show posP nbr hd (nbr v (digit d (enc d (a :: l)) 0 hd)) (enc d (a :: l) / d) l.length = _
      rw [hmod, hdiv, ih]
      rfl

/-! ## The exhaustive-walk algorithm

For a graph of degree `d` all of whose components have diameter at most `D`, `s`-`t`
connectivity is decided by trying, one after the other, all `d ^ D` label sequences of
length `D`, and checking whether `t` occurs on the corresponding walk from `s`.

The memory used is a label sequence (`D * log d` bits), a step counter, and three vertex
names, hence `O(D * log d + log N)` bits.  For `d` constant and `D = O(log N)` this is
logarithmic space -- this is the final step of Reingold's algorithm.
-/

/-- Configurations of the exhaustive-walk algorithm: either a running configuration
`(s, t, k, j, v)` (source, target, current label sequence, step counter, current vertex),
or a halted configuration carrying the answer. -/
abbrev ES (N d D : ℕ) : Type :=
  (Fin N × Fin N × Fin (d ^ D) × Fin (D + 1) × Fin N) ⊕ Bool

/-- The transition function of the exhaustive-walk algorithm. -/
