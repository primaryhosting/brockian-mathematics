import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex SimpleGraph

namespace Chem

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₁₄`, i.e. the Hückel matrix of the
carbon skeleton of a 14-membered annulene in units where `α = 0` and `β = 1`. -/

private lemma C14adj_mulVec_zmod (v : ZMod 14 → ℂ) (i : ZMod 14) :
    C14adj.mulVec v i = v (i + -1) + v (i + 1) := by
  have h := C14adj_mulVec v i
  rw [sub_eq_add_neg] at h
  exact h

/-- `χ(k) + χ(-k) = 2 cos (2πk/14)`. -/
