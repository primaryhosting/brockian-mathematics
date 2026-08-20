/-
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2`, represented as a vector in the
Hilbert space `ℂ^(Fin 6 → Bool)`, whose index type is the set of 6-bit computational
basis labels. -/

noncomputable def ghz6 : EuclideanSpace ℂ (Fin 6 → Bool) :=
  WithLp.toLp 2 (fun b =>
    if b = (fun _ => false) then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else if b = (fun _ => true) then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else 0)

/-- The 6-qubit GHZ state is a unit vector. -/
