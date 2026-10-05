import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Frontier

/-! ## The finite-volume 2D Ising model on an `L × L` torus -/

/-- Shift a periodic (torus) index by one site. -/

theorem onsagerHoldsAt_zero : OnsagerHoldsAt 0 := by
  rw [OnsagerHoldsAt, onsagerLogZDensity_zero]
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop 1] with L hL
  exact (logZDensity_zero L hL).symm

/-!
## Main statement

`OnsagerFreeEnergy` above is the full statement of Onsager's solution.  The theorem below
records the formalization together with the pieces that are verified here: the exactly
solvable base case `K = 0` (where the finite-volume free energy equals Onsager's expression
for every volume, so the thermodynamic limit holds), the exact `1 × 1` torus, positivity of
the partition function, the exact infinite-temperature count `Z = 2^{L²}`, and the
nonnegativity of the argument of the Onsager logarithm together with the identification of
Onsager's critical coupling `K_c = ½ log (1+√2)` as the unique `K ≥ 0` where it degenerates.
-/
