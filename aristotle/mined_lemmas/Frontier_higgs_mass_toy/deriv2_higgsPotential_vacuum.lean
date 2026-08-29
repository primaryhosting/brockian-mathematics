/-
# Higgs Mass Toy
Category: Frontier Physics
Target: Frontier.higgs_mass_toy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Higgs Mass Toy
Category: Frontier Physics
Target: Frontier.higgs_mass_toy
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

/-- The "Mexican hat" scalar potential of the abelian Higgs toy model,
written in terms of the modulus `r = |φ|` of the complex scalar field:
`V(r) = lam * (r² - v²)²`. -/

lemma deriv2_higgsPotential_vacuum :
    deriv (deriv fun x : ℝ => higgsPotential lam v x) v = higgsMassSq lam v := by
  have h : (deriv fun x : ℝ => higgsPotential lam v x)
      = fun r : ℝ => 4 * lam * r * (r ^ 2 - v ^ 2) := by
    funext r; exact deriv_higgsPotential lam v r
  rw [h]
  have hd : HasDerivAt (fun r : ℝ => 4 * lam * r * (r ^ 2 - v ^ 2))
      (4 * lam * (3 * v ^ 2 - v ^ 2)) v := by
    have h1 : HasDerivAt (fun r : ℝ => 4 * lam * r) (4 * lam) v := by
      simpa using (hasDerivAt_id v).const_mul (4 * lam)
    have h2 : HasDerivAt (fun r : ℝ => r ^ 2 - v ^ 2) (2 * v) v := by
      simpa using ((hasDerivAt_pow 2 v).sub_const (v ^ 2))
    have := h1.mul h2
    convert this using 1
    ring
  rw [hd.deriv, higgsMassSq]
  ring

end Potential

section GaugeMass

variable (g v : ℝ)

/-- Expanding the gauge kinetic term about the vacuum `r = v + h` isolates a
mass term `m_A² A²` for the gauge field, plus interactions of order `h`. -/
