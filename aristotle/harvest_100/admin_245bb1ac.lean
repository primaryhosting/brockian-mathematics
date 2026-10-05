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

/-- The one-loop coefficient `b₀` of the SU(N) beta function with `nf` Dirac fermions
in the fundamental representation:  `b₀ = (11 N - 2 n_f) / 3`. -/
noncomputable def b0 (N nf : ℕ) : ℝ := (11 * (N : ℝ) - 2 * (nf : ℝ)) / 3

/-- The one-loop beta function of SU(N) gauge theory with `nf` fundamental Dirac fermions:
`β(g) = - b₀ g³ / (16 π²)`. -/
noncomputable def betaOneLoop (N nf : ℕ) (g : ℝ) : ℝ :=
  -(b0 N nf) * g ^ 3 / (16 * Real.pi ^ 2)

/-- The one-loop coefficient is positive whenever there are few enough fermion flavours,
`2 n_f < 11 N`. -/
theorem b0_pos {N nf : ℕ} (h : 2 * nf < 11 * N) : 0 < b0 N nf := by
  have h' : (2 * nf : ℝ) < 11 * N := by exact_mod_cast h
  unfold b0
  linarith

/-- **Asymptotic freedom sign.**  For an SU(N) gauge theory with `nf` fundamental Dirac
fermions satisfying `2 n_f < 11 N` (in particular the pure gauge case `n_f = 0` for any
`N ≥ 1`), the one-loop beta function is strictly negative at every nonzero coupling
`g > 0`; hence the coupling decreases with increasing energy scale. -/
theorem asymptotic_freedom_sign {N nf : ℕ} (h : 2 * nf < 11 * N) {g : ℝ} (hg : 0 < g) :
    betaOneLoop N nf g < 0 := by
  have hb : 0 < b0 N nf := b0_pos h
  have hg3 : 0 < g ^ 3 := by positivity
  have hpi : 0 < 16 * Real.pi ^ 2 := by positivity
  unfold betaOneLoop
  apply div_neg_of_neg_of_pos _ hpi
  nlinarith

/-- Specialization: pure SU(3) Yang–Mills (and QCD with the physical six flavours) is
asymptotically free. -/
theorem asymptotic_freedom_sign_qcd {g : ℝ} (hg : 0 < g) : betaOneLoop 3 6 g < 0 :=
  asymptotic_freedom_sign (by norm_num) hg

end Frontier

