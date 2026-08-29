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

lemma C20root_inj {i j : ZMod 20} (h : C20root i = C20root j) : i = j := by
  rw [C20root_eq_pow i, C20root_eq_pow j] at h
  have := C20root_isPrimitiveRoot.pow_inj (ZMod.val_lt i) (ZMod.val_lt j) h
  exact (ZMod.val_injective 20) this

