/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Complex

namespace Chem

/-- A primitive 18-th root of unity. -/

noncomputable def Vunit : (Matrix (Fin 18) (Fin 18) ℂ)ˣ := ⟨V, W, V_mul_W, W_mul_V⟩

/-- For every `k`, the vector `j ↦ exp (2πi jk / 18)` is a nonzero eigenvector of the adjacency
matrix of `C₁₈` with eigenvalue `2 cos (2πk/18)`. -/
