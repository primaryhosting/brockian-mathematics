/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Chem

/-- A primitive fifth root of unity. -/

noncomputable def F5 : Matrix (ZMod 5) (ZMod 5) ℂ := fun j k => e5 (j * k)

/-- The inverse (up to normalization) of the discrete Fourier matrix. -/
