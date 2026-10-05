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

/-- The one-loop coefficient `b₀ = 11N/3 - 2 n_f/3` of the SU(N) gauge beta function,
with `N` colours and `n_f` Dirac fermions in the fundamental representation. -/
noncomputable def betaZeroCoeff (N nf : ℕ) : ℝ := 11 / 3 * (N : ℝ) - 2 / 3 * (nf : ℝ)

/-- The one-loop beta function of an SU(N) gauge theory:
`β(g) = - b₀ g³ / (16 π²)`. -/
noncomputable def oneLoopBeta (N nf : ℕ) (g : ℝ) : ℝ :=
    -betaZeroCoeff N nf * g ^ 3 / (16 * Real.pi ^ 2)

/-- The one-loop coefficient is positive whenever the number of fermion flavours obeys the
asymptotic-freedom bound `2 n_f < 11 N`. -/
theorem betaZeroCoeff_pos {N nf : ℕ} (h : 2 * nf < 11 * N) : 0 < betaZeroCoeff N nf := by
  have h' : (2 : ℝ) * (nf : ℝ) < 11 * (N : ℝ) := by exact_mod_cast h
  unfold betaZeroCoeff
  linarith

/-- **Asymptotic freedom.** For an SU(N) gauge theory with `2 n_f < 11 N` (in particular for
pure SU(N) Yang–Mills, `n_f = 0`, `N ≥ 1`), the one-loop beta function is strictly negative at
any positive coupling `g`, so the coupling decreases at short distances. -/
theorem asymptotic_freedom_sign {N nf : ℕ} (h : 2 * nf < 11 * N) {g : ℝ} (hg : 0 < g) :
    oneLoopBeta N nf g < 0 := by
  have hb : 0 < betaZeroCoeff N nf := betaZeroCoeff_pos h
  have hg3 : 0 < g ^ 3 := by positivity
  have hpi : 0 < 16 * Real.pi ^ 2 := by positivity
  unfold oneLoopBeta
  apply div_neg_of_neg_of_pos _ hpi
  nlinarith

/-- Specialisation to pure SU(3) Yang–Mills with the six Standard-Model quark flavours:
`b₀ = 11 - 4 = 7 > 0`, so the QCD beta function is negative. -/
theorem asymptotic_freedom_sign_qcd {g : ℝ} (hg : 0 < g) : oneLoopBeta 3 6 g < 0 :=
  asymptotic_freedom_sign (by norm_num) hg

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

