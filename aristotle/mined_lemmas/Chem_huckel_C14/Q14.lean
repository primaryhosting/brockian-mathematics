import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph Matrix

namespace Chem

/-! ### Arithmetic in `Fin 14`

`Fin 14` carries the modular `+`, `-`, `*` and `-·` operations used by
`SimpleGraph.cycleGraph_adj`, but no `CommRing` instance is available for the numeral `14`,
so the handful of ring identities we need are checked by decision procedure. -/

section Fin14


noncomputable def Q14 : Matrix (Fin 14) (Fin 14) ℂ := fun k l => (14 : ℂ)⁻¹ * zeta (-(k * l))

/-- The Hückel eigenvalues `2 cos (2πk/14)`. -/
