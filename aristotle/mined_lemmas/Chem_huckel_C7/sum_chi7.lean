/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Chem

open Finset Complex

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- A primitive 7-th root of unity. -/

lemma sum_chi7 : ∑ k : ZMod 7, chi7 k = 0 := by
  have hsum : ∑ k : ZMod 7, chi7 k = ∑ n ∈ Finset.range 7, zeta7 ^ n := by
    rw [Finset.sum_nbij' (fun (k : ZMod 7) => k.val) (fun n => (n : ZMod 7))] <;>
      intros <;> simp_all [chi7, ZMod.val_lt, ZMod.val_natCast, Nat.mod_eq_of_lt,
        ZMod.natCast_val, ZMod.cast_id]
  rw [hsum]
  have h1 : zeta7 ≠ 1 := by
    intro h
    have hp := zeta7_prim
    rw [h] at hp
    have := hp.eq_orderOf
    simp at this
  rw [geom_sum_eq h1, zeta7_pow_seven]
  simp

