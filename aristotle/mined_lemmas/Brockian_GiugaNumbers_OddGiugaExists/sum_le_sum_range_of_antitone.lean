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

import Mathlib

/-!
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GiugaNumbers

open Finset

/-- A *Giuga number* is a composite number `n > 1` such that every prime `p` dividing `n`
satisfies `p ∣ n / p - 1`. -/

lemma sum_le_sum_range_of_antitone {f : ℕ → ℚ} (hf : Antitone f) (T : Finset ℕ) :
    ∑ i ∈ T, f i ≤ ∑ i ∈ range T.card, f i := by
  induction hk : T.card generalizing T with
  | zero => simp [Finset.card_eq_zero.1 hk]
  | succ k ih =>
    have hne : T.Nonempty := Finset.card_pos.1 (by omega)
    have hmem : T.max' hne ∈ T := T.max'_mem hne
    have hsub : T ⊆ range (T.max' hne + 1) := fun x hx =>
      Finset.mem_range.2 (Nat.lt_succ_of_le (T.le_max' x hx))
    have hcard : k + 1 ≤ T.max' hne + 1 := by
      calc k + 1 = T.card := hk.symm
        _ ≤ (range (T.max' hne + 1)).card := Finset.card_le_card hsub
        _ = T.max' hne + 1 := by simp
    have herase : (T.erase (T.max' hne)).card = k := by
      rw [Finset.card_erase_of_mem hmem, hk]
      omega
    have hih := ih (T.erase (T.max' hne)) herase
    have hsum : ∑ i ∈ T.erase (T.max' hne), f i + f (T.max' hne) = ∑ i ∈ T, f i :=
      Finset.sum_erase_add T f hmem
    have hle : f (T.max' hne) ≤ f k := hf (by omega)
    rw [← hsum, Finset.sum_range_succ]
    linarith

/-- Enumeration of the numbers `≥ 5` that are coprime to `6`: `5, 7, 11, 13, 17, 19, 23, 25, …`. -/
