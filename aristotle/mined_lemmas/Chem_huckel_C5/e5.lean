/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Chem

/-- A primitive fifth root of unity. -/

noncomputable def e5 (m : ZMod 5) : ℂ := zeta5 ^ m.val

/-- The adjacency matrix of the cycle graph `C₅`, with vertices indexed by `ZMod 5`:
vertex `i` is adjacent to `i + 1` and `i - 1`. -/
