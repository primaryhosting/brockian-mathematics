/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 4000000

namespace Chem

/-- A primitive 8-th root of unity. -/

noncomputable def mu (k : Fin 8) : ℂ := zeta ^ (k : ℕ) + zeta ^ (7 * (k : ℕ))

/-- The (unnormalized) discrete Fourier matrix; its columns are the eigenvectors. -/
