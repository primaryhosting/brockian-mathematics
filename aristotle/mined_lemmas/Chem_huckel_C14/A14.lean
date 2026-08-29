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


noncomputable def A14 : Matrix (Fin 14) (Fin 14) ℂ := (cycleGraph 14).adjMatrix ℂ

/-- The discrete Fourier matrix. -/
