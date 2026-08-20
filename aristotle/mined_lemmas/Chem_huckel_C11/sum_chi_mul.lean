/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset Complex

noncomputable section

/-- A primitive 11-th root of unity. -/

lemma sum_chi_mul (d : ZMod 11) (hd : d ≠ 0) : ∑ k : ZMod 11, chi (k * d) = 0 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have := Equiv.sum_comp (Equiv.mulRight₀ d hd) chi
  simpa [Equiv.mulRight₀] using this.trans sum_chi

