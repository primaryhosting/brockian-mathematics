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

noncomputable def coulombEnergy {N K : ℕ} (z : Fin K → ℝ)
    (x : Fin N → Space) (R : Fin K → Space) : ℝ :=
  (∑ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2), 1 / dist (x p.1) (x p.2))
    - (∑ i : Fin N, ∑ k : Fin K, z k / dist (x i) (R k))
    + (∑ q ∈ Finset.univ.filter (fun q : Fin K × Fin K => q.1 < q.2),
        z q.1 * z q.2 / dist (R q.1) (R q.2))

/-- Sanity check on the definition: one electron and one nucleus of charge `z` give the
hydrogenic potential energy `-z/|x - R|`. -/
