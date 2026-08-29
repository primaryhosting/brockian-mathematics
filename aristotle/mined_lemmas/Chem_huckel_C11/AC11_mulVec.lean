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

lemma AC11_mulVec (v : ZMod 11 → ℂ) (i : ZMod 11) :
    (AC11 *ᵥ v) i = v (i - 1) + v (i + 1) := by
  have h : ∀ j : ZMod 11, AC11 i j * v j
      = (if j = i - 1 then v j else 0) + (if j = i + 1 then v j else 0) := by
    intro j
    rw [AC11_apply]
    by_cases h1 : j = i - 1
    · subst h1; simp [sub_one_ne_add_one i]
    · by_cases h2 : j = i + 1 <;> simp [h1, h2, Ne.symm (sub_one_ne_add_one i)]
  simp only [Matrix.mulVec, dotProduct, h]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (i - 1) v,
    Finset.sum_ite_eq' Finset.univ (i + 1) v]
  simp

/-! ## Roots of unity -/

/-- A primitive 11-th root of unity. -/
