/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hückel theory for the cycle C₁₁

The adjacency eigenvalues of the cycle graph `C₁₁` are exactly `2 cos (2πk/11)`, `k = 0,…,10`.
-/

open Complex Matrix Finset

namespace Chem

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-! ## The cycle graph and its adjacency matrix -/

/-- The cycle graph on 11 vertices, realised on `ZMod 11`: `i ~ j` iff `i - j = ±1`. -/

lemma e_add (a b : ZMod 11) : e (a + b) = e a * e b := by
  have h : om ^ (a.val + b.val) = e (((a.val + b.val : ℕ) : ZMod 11)) := om_pow_nat _
  rw [pow_add] at h
  simpa [e, ZMod.natCast_val, ZMod.cast_id] using h.symm

