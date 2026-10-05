import RequestProject.TodaCube

/-!
# Affine hashing over GF(2) and the isolation lemma

We encode an affine hash function `y ↦ A y + b` from `GF(2)^q` to `GF(2)^k` as a bit string
consisting of `q+4` blocks of length `q+1`; block `i` consists of the `i`-th row of `A`
followed by the `i`-th coordinate of `b`.  Only the first `k` blocks are used.

The main results are the two counting lemmas (uniformity and pairwise independence) and the
Valiant–Vazirani isolation lemma `CS.isolation`.
-/

open Classical BigOperators

namespace CS

/-- Inner product over `GF(2)` of two bit strings. -/

theorem card_filter_blocks (T B : ℕ) (P : ℕ → Str → Prop) [∀ j, DecidablePred (P j)] :
    ((Cube (T * B)).filter (fun v => ∀ j < T, P j (blk B j v))).card
      = ∏ j ∈ Finset.range T, ((Cube B).filter (P j)).card := by
  have h1 : ∀ v : Str, (if (∀ j < T, P j (blk B j v)) then (1 : ℕ) else 0)
      = ∏ j ∈ Finset.range T, (if P j (blk B j v) then (1 : ℕ) else 0) := by
    intro v
    rw [Finset.prod_boole]
    congr 1
    simp
  simp only [Finset.card_filter]
  rw [Finset.sum_congr rfl (fun v _ => h1 v), prod_sum_blocks B T
      (fun j u => if P j u then (1 : ℕ) else 0)]

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

