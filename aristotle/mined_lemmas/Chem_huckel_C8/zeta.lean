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

noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

/-- The adjacency matrix of the cycle graph `C₈` (the Hückel matrix of cyclooctatetraene
in units where `α = 0`, `β = 1`), indexed by `Fin 8` with cyclic adjacency. -/
