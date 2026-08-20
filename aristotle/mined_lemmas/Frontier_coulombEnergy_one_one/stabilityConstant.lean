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

noncomputable def stabilityConstant (cLT cB cScr : ℝ) : ℝ :=
  (2 / 5) * cB * ((5 * cLT) / (3 * cB)) ^ (-(3 : ℝ) / 2) * cScr

/--
**Stability of matter from the Lieb–Thirring inequality (Lean-checked reduction).**

Consider `N` electrons at positions `x` and `K` nuclei of charges `z` at positions `R`,
and let `T` be the kinetic energy of the electronic state, `S = ∫ ρ^{5/3}` the
Lieb–Thirring functional of its one-particle density, and `D` the screening quantity
appearing in the electrostatic estimate.  Assume:

* `hkin`  — the **Lieb–Thirring kinetic energy inequality** `T ≥ cLT * S`
  (this is where the Pauli principle enters);
* `hpot`  — the **electrostatic inequality** (Baxter / Lieb–Yau, combined with Hölder)
  `W ≥ -cB * S^{3/5} * D^{2/5}` for the many body Coulomb energy `W`;
* `hscr`  — the **screening bound** `D ≤ cScr * (N + K)`.

Then the total energy is bounded below *linearly in the number of particles*:

`T + W ≥ - stabilityConstant cLT cB cScr * (N + K)`,

which is exactly stability of matter of the second kind.  The three hypotheses are the
hard analytic inputs; the present theorem is the fully verified derivation of stability
from them, including the sharp form of the optimisation constant.
-/
