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

noncomputable def C14adj : Matrix (Fin 14) (Fin 14) ℂ := (cycleGraph 14).adjMatrix ℂ

/-- The standard additive character `j ↦ exp (2 π I j / 14)` on `ZMod 14`. -/
private noncomputable abbrev chi : AddChar (ZMod 14) ℂ := ZMod.stdAddChar

/-- Multiplying by the adjacency matrix of `C₁₄` sums the two cyclic neighbours. -/
