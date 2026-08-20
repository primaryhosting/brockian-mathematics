import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header block is placed immediately after `import Mathlib`, since Lean 4 requires
-- `import` commands to come first in a file.)

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Finset

/-- A primitive 16-th root of unity. -/

noncomputable def evC16 (k : ZMod 16) : ℂ := 2 * (Real.cos (2 * Real.pi * k.val / 16) : ℂ)

/-- The (unnormalized) discrete Fourier transform matrix. -/
