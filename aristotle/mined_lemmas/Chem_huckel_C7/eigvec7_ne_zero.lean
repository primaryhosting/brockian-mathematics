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

lemma eigvec7_ne_zero (k : ZMod 7) : eigvec7 k ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp only [eigvec7, Pi.zero_apply, zero_mul] at h0
  exact chi7_ne_zero 0 h0

/-- Each Fourier vector is an eigenvector with eigenvalue `2cos(2πk/7)`. -/
