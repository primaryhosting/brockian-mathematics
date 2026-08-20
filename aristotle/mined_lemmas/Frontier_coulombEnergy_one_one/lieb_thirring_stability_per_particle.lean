/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## Configuration space -/

/-- Physical three dimensional space. -/
abbrev Space : Type := EuclideanSpace ℝ (Fin 3)

/-! ## The many body Coulomb energy

For `N` electrons (unit negative charge) at positions `x 0, …, x (N-1)` and `K` nuclei of
charges `z 0, …, z (K-1)` at positions `R 0, …, R (K-1)`, the classical Coulomb energy is

`W = ∑_{i<j} 1/|xᵢ - xⱼ| - ∑_{i,k} z_k/|xᵢ - R_k| + ∑_{k<l} z_k z_l/|R_k - R_l|`.

This is the potential part of the Hamiltonian appearing in the stability of matter problem. -/

theorem lieb_thirring_stability_per_particle {N K : ℕ} (z : Fin K → ℝ)
    (x : Fin N → Space) (R : Fin K → Space)
    (T S D cLT cB cScr : ℝ)
    (hcLT : 0 < cLT) (hcB : 0 < cB)
    (hS : 0 ≤ S) (hD : 0 ≤ D)
    (hkin : cLT * S ≤ T)
    (hpot : -(cB * (S ^ ((3 : ℝ) / 5) * D ^ ((2 : ℝ) / 5))) ≤ coulombEnergy z x R)
    (hscr : D ≤ cScr * ((N : ℝ) + K))
    (hpos : 0 < (N : ℝ) + K) :
    -stabilityConstant cLT cB cScr ≤ (T + coulombEnergy z x R) / ((N : ℝ) + K) := by
  have h := lieb_thirring_stability z x R T S D cLT cB cScr hcLT hcB hS hD hkin hpot hscr
  rw [le_div_iff₀ hpos]
  linarith [h]

end Frontier

