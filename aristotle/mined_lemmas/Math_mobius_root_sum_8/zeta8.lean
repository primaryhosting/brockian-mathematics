/-
# Mobius Root Sum 8
Category: Pure Mathematics
Target: Math.mobius_root_sum_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- A fixed primitive `8`-th root of unity in `ℂ`. -/

noncomputable def zeta8 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

