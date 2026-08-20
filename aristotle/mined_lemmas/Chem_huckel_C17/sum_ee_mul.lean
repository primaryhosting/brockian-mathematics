/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Complex

/-! ### A primitive 17-th root of unity and the associated additive character -/

/-- A primitive 17-th root of unity. -/

lemma sum_ee_mul (t : ZMod 17) : ∑ m : ZMod 17, ee (m * t) = if t = 0 then 17 else 0 := by
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  by_cases ht : t = 0
  · subst ht; simp [ee_zero]
  · rw [if_neg ht]
    rw [Fintype.sum_equiv (Equiv.mulRight₀ t ht) (fun m => ee (m * t)) ee (fun m => rfl)]
    exact sum_ee

/-! ### The adjacency matrix of `C₁₇` -/

/-- The adjacency matrix of the cycle graph `C₁₇`, with vertices indexed by `ZMod 17`:
two vertices are adjacent exactly when they differ by `1` modulo `17`. -/
