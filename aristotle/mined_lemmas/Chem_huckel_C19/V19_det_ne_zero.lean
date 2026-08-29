import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to precede any module documentation, so the requested
header comment appears immediately after the single `import Mathlib` line.)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₉`, i.e. the Hückel matrix of the
carbon skeleton of a 19-membered annulene (with `α = 0`, `β = 1`). -/

lemma V19_det_ne_zero : V19.det ≠ 0 := by
  rw [V19]
  refine Matrix.det_vandermonde_ne_zero_iff.mpr ?_
  intro a b hab
  exact Fin.ext (zeta19_isPrimitiveRoot.pow_inj a.isLt b.isLt hab)

