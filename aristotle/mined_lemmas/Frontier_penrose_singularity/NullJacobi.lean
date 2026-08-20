import Mathlib

/-!
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
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

/-!
## Setting

Mathlib does not (yet) contain Lorentzian causal theory, so the Penrose singularity

noncomputable def NullJacobi.toNullCongruence {L : ℝ} (J : NullJacobi L) : NullCongruence L where
  theta := fun t => 2 * J.drho t / J.rho t
  dtheta := fun t => (2 * J.ddrho t * J.rho t - 2 * J.drho t * J.drho t) / J.rho t ^ 2
  hasDerivAt := by
    intro t ht
    have h1 : HasDerivAt (fun x => 2 * J.drho x) (2 * J.ddrho t) t :=
      (J.hasDerivAt_drho t ht).const_mul 2
    have h2 : HasDerivAt J.rho (J.drho t) t := J.hasDerivAt_rho t ht
    exact h1.div h2 (ne_of_gt (J.rho_pos t ht))
  raychaudhuri := by
    intro t ht
    have hpos : 0 < J.rho t := J.rho_pos t ht
    have hsq : (0 : ℝ) < J.rho t ^ 2 := by positivity
    have hdd : J.ddrho t ≤ 0 := J.jacobi_nec t ht
    rw [div_le_iff₀ hsq]
    have hexp : -(2 * J.drho t / J.rho t) ^ 2 / 2 * J.rho t ^ 2 = -2 * J.drho t ^ 2 := by
      field_simp
    rw [hexp]
    nlinarith

/-- **Penrose singularity theorem, focal-point form.**

If the null geodesic congruence orthogonal to a trapped surface (`rho' 0 < 0`) obeys the
null energy condition in Jacobi form (`rho'' ≤ 0`), then it stays regular (`rho > 0`) only
for affine parameter less than `-rho 0 / rho' 0`: a focal point of the surface occurs at or
before that affine parameter.  Consequently the congruence — and hence the spacetime —
cannot be null geodesically complete. -/
