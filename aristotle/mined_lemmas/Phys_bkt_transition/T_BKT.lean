/-
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

/-- Parameters of the two–dimensional XY model on a disc of radius `R`:
`J` is the spin stiffness (coupling), `kB` Boltzmann's constant and `a` the
short–distance cutoff (lattice spacing / vortex core size). -/
structure XYParams where
  /-- spin stiffness -/
  J : ℝ
  /-- Boltzmann constant -/
  kB : ℝ
  /-- short distance cutoff (core radius) -/
  a : ℝ
  hJ : 0 < J
  hkB : 0 < kB
  ha : 0 < a

/-- Energy of a single vortex (topological defect of winding number `±1`) in a
system of linear size `R`: `E = π J log (R / a)`. -/

noncomputable def T_BKT (p : XYParams) : ℝ :=
  Real.pi * p.J / (2 * p.kB)

