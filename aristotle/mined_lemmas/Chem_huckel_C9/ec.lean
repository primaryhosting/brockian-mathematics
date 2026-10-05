import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- A primitive ninth root of unity. -/

noncomputable def ec (x : ZMod 9) : ℂ := zeta9 ^ x.val

/-- The adjacency matrix of the cycle graph `C₉`, with vertices indexed by `ZMod 9`:
two vertices are adjacent exactly when they differ by `±1`. -/
