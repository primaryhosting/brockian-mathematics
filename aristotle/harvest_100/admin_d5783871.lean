/-
# Asymptotic Freedom Sign
Category: Frontier Physics
Target: Frontier.asymptotic_freedom_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Asymptotic Freedom Sign
Category: Frontier Physics
Target: Frontier.asymptotic_freedom_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Real

/-- The one-loop coefficient `b₀ = (11 N - 2 N_f)/3` of the SU(N) gauge beta function
with `N_f` Dirac fermions in the fundamental representation. -/
noncomputable def betaZeroCoeff (N Nf : ℕ) : ℝ := (11 * (N : ℝ) - 2 * (Nf : ℝ)) / 3

/-- The one-loop renormalization-group beta function of the SU(N) gauge coupling `g`,
`β(g) = - b₀ g³ / (16 π²)`. -/
noncomputable def betaOneLoop (N Nf : ℕ) (g : ℝ) : ℝ :=
  -betaZeroCoeff N Nf * g ^ 3 / (16 * π ^ 2)

/-- **Asymptotic freedom.** For an SU(N) gauge theory with fewer than `11N/2` fundamental
Dirac fermions and positive coupling `g`, the one-loop beta function is strictly negative:
the coupling decreases at short distances. -/
theorem asymptotic_freedom_sign (N Nf : ℕ) (hNf : 2 * Nf < 11 * N) {g : ℝ} (hg : 0 < g) :
    betaOneLoop N Nf g < 0 := by
  have hb : 0 < betaZeroCoeff N Nf := by
    have : (2 * Nf : ℝ) < 11 * N := by exact_mod_cast hNf
    unfold betaZeroCoeff
    linarith
  have hpi : 0 < 16 * π ^ 2 := by positivity
  have hg3 : 0 < g ^ 3 := by positivity
  unfold betaOneLoop
  apply div_neg_of_neg_of_pos _ hpi
  nlinarith [mul_pos hb hg3]

/-- Concrete case: QCD, i.e. SU(3) with the six known quark flavours. -/
theorem asymptotic_freedom_QCD {g : ℝ} (hg : 0 < g) : betaOneLoop 3 6 g < 0 :=
  asymptotic_freedom_sign 3 6 (by norm_num) hg

end Frontier

import Mathlib

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

