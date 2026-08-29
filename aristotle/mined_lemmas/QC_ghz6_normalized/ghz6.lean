/-
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2`, as a vector in the complex
Euclidean space whose basis is indexed by the 6-bit strings `Fin 6 → Fin 2`:
the amplitude is `1/√2` on the all-zeros and all-ones strings, and `0` elsewhere. -/

noncomputable def ghz6 : EuclideanSpace ℂ (Fin 6 → Fin 2) :=
  WithLp.toLp 2 fun v =>
    if (v = fun _ => 0) ∨ (v = fun _ => 1) then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0

/-- The 6-qubit GHZ state is a unit vector. -/
