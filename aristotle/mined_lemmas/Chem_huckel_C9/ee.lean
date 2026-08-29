import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

noncomputable section

/-- A primitive 9-th root of unity. -/

noncomputable def ee (a : ZMod 9) : ℂ := om ^ a.val

/-- Adjacency matrix of the cycle graph `C₉`, on the vertex set `ZMod 9`:
vertices `i` and `j` are adjacent iff `j = i + 1` or `j = i - 1`. -/
