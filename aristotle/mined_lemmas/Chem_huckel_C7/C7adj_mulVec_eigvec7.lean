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

theorem C7adj_mulVec_eigvec7 (k : ZMod 7) :
    C7adj.mulVec (eigvec7 k) = lam7 k • eigvec7 k := by
  funext i
  rw [mulVec_C7adj]
  simp only [eigvec7, Pi.smul_apply, smul_eq_mul]
  rw [← chi7_add_chi7_neg k]
  have h1 : (i - 1) * k = i * k + (-k) := by ring
  have h2 : (i + 1) * k = i * k + k := by ring
  rw [h1, h2, chi7_add, chi7_add]
  ring

/-- Orthogonality: the sum of the character over `ZMod 7` vanishes. -/
