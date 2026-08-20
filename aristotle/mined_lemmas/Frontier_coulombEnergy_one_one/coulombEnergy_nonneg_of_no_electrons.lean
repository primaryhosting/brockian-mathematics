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

theorem coulombEnergy_nonneg_of_no_electrons {K : ℕ} (z : Fin K → ℝ) (hz : ∀ k, 0 ≤ z k)
    (R : Fin K → Space) :
    0 ≤ coulombEnergy z (fun _ : Fin 0 => (0 : Space)) R := by
  have h : (0 : ℝ) ≤ ∑ q ∈ Finset.univ.filter (fun q : Fin K × Fin K => q.1 < q.2),
      z q.1 * z q.2 / dist (R q.1) (R q.2) := by
    refine Finset.sum_nonneg ?_
    intro q _
    exact div_nonneg (mul_nonneg (hz _) (hz _)) dist_nonneg
  simpa [coulombEnergy] using h

/-! ## The analytic core: a weighted arithmetic–geometric mean bound

The Lieb–Thirring kinetic energy inequality controls the kinetic energy from below by
`c_LT * ∫ ρ^{5/3}`, while the electrostatic (Baxter / Lieb–Yau) inequality together with
Hölder's inequality controls the Coulomb energy from below by
`-c_B * (∫ ρ^{5/3})^{3/5} * D^{2/5}`, where `D` is a screening integral bounded by a constant
times the number of particles.  Stability then follows from the elementary optimisation
`a t - b t^{3/5} d^{2/5} ≥ -C d`, which is the content of the next two lemmas. -/

/-- A scaled weighted AM–GM bound: for every `lam > 0` and nonnegative `t`, `d`,
`t^{3/5} d^{2/5} ≤ (3/5) lam t + (2/5) lam^{-3/2} d`. -/
