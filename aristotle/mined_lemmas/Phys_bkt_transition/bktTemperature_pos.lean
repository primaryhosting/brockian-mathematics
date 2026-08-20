/-
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- Energy cost of a single vortex in a 2D XY model with spin stiffness `J`, in a
square sample of linear size `L` with short-distance (core) cutoff `a`:
`E = π J log (L / a)`. -/

lemma bktTemperature_pos {J kB : ℝ} (hJ : 0 < J) (hkB : 0 < kB) :
    0 < bktTemperature J kB := by
  unfold bktTemperature
  positivity

/-- **Berezinskii–Kosterlitz–Thouless topological phase transition of the 2D XY model.**

For a single vortex in a sample of linear size `L` with core size `a < L`, the free
energy `F = E - T S`, with `E = π J log (L / a)` the vortex energy and
`S = 2 k_B log (L / a)` its positional entropy, changes sign exactly at the
BKT temperature `T_BKT = π J / (2 k_B)`:

* below `T_BKT` the free energy of an isolated vortex is positive and diverges as
  `L → ∞`, so free vortices are suppressed and the system is in the quasi-long-range
  ordered (bound vortex–antivortex) phase;
* at `T_BKT` the free energy vanishes identically;
* above `T_BKT` the free energy is negative and diverges to `-∞` as `L → ∞`, so free
  vortices proliferate and destroy the quasi-long-range order.

The divergence in `L` is recorded by the fact that the free energy is the sign-fixed
coefficient `π J - 2 k_B T` times `log (L / a) → ∞`. -/
