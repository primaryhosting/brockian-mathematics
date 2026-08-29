/-
# Asymptotic Freedom Sign
Category: Frontier Physics
Target: Frontier.asymptotic_freedom_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- The one-loop coefficient `b₀ = (11 N - 2 n_f)/3` of the SU(N) gauge beta function,
with `N` colours and `n_f` Dirac fermion flavours in the fundamental representation. -/
noncomputable def betaZeroCoeff (N nf : ℕ) : ℝ := (11 * (N : ℝ) - 2 * (nf : ℝ)) / 3

/-- The one-loop SU(N) beta function `β(g) = - b₀ g³ / (16 π²)`. -/
noncomputable def oneLoopBeta (N nf : ℕ) (g : ℝ) : ℝ :=
  -betaZeroCoeff N nf * g ^ 3 / (16 * Real.pi ^ 2)

/-- **Asymptotic freedom sign.** For an SU(N) gauge theory with `n_f` fermion flavours
satisfying the asymptotic-freedom condition `2 n_f < 11 N`, the one-loop beta function
is strictly negative at any positive coupling `g`. -/
theorem asymptotic_freedom_sign (N nf : ℕ) (h : 2 * nf < 11 * N) (g : ℝ) (hg : 0 < g) :
    oneLoopBeta N nf g < 0 := by
  have hb : 0 < betaZeroCoeff N nf := by
    have : (2 * nf : ℝ) < 11 * N := by exact_mod_cast h
    unfold betaZeroCoeff
    have h2 : (0:ℝ) < 11 * (N : ℝ) - 2 * (nf : ℝ) := by push_cast at this ⊢; linarith
    positivity
  have hpi : (0:ℝ) < 16 * Real.pi ^ 2 := by positivity
  have hg3 : 0 < g ^ 3 := by positivity
  unfold oneLoopBeta
  apply div_neg_of_neg_of_pos _ hpi
  nlinarith

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

