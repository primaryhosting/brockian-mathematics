/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex Matrix Polynomial

namespace Chem

/-- The adjacency matrix of the cycle graph `C₂₀`, with vertices indexed by `ZMod 20`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`.  In Hückel theory (with `α = 0`,
`β = 1`) this is the Hückel matrix of the annulene `C₂₀`. -/

lemma C20root_eq_pow (k : ZMod 20) : C20root k = (C20root 1) ^ k.val := by
  rw [C20root, C20root, ← Complex.exp_nat_mul]
  congr 1
  push_cast [show (1 : ZMod 20).val = 1 from rfl]
  ring

