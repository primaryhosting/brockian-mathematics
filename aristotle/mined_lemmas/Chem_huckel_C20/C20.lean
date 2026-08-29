import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset Matrix

/-- A primitive 20-th root of unity. -/

noncomputable def C20 : Matrix (ZMod 20) (ZMod 20) ℂ := (SimpleGraph.cycleGraph 20).adjMatrix ℂ

