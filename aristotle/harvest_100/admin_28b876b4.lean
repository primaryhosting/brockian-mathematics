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

namespace Frontier

/-- The one-loop coefficient `b₀` of the beta function of an `SU(N)` gauge theory
coupled to `Nf` Dirac fermions in the fundamental representation:
`b₀ = 11/3 * N - 2/3 * Nf`. -/
noncomputable def b0 (N Nf : ℕ) : ℝ := (11 / 3) * (N : ℝ) - (2 / 3) * (Nf : ℝ)

/-- The one-loop beta function of an `SU(N)` gauge theory with `Nf` fundamental Dirac
fermions, `β(g) = - b₀ g³ / (16 π²)`. -/
noncomputable def betaOneLoop (N Nf : ℕ) (g : ℝ) : ℝ :=
  - b0 N Nf * g ^ 3 / (16 * Real.pi ^ 2)

/-- The one-loop coefficient `b₀` is positive precisely in the asymptotically free regime
`2 Nf < 11 N`. -/
theorem b0_pos {N Nf : ℕ} (h : 2 * Nf < 11 * N) : 0 < b0 N Nf := by
  have h' : (2 : ℝ) * (Nf : ℝ) < 11 * (N : ℝ) := by
    exact_mod_cast (by exact_mod_cast h : ((2 * Nf : ℕ) : ℝ) < ((11 * N : ℕ) : ℝ))
  unfold b0
  linarith

/-- **Asymptotic freedom (sign of the one-loop beta function).**
For an `SU(N)` gauge theory with `Nf` fundamental Dirac fermions satisfying `2 Nf < 11 N`
(in particular for pure `SU(N)` Yang–Mills, `Nf = 0`, `N ≥ 1`), the one-loop beta function
is strictly negative at any positive coupling `g`. -/
theorem asymptotic_freedom_sign {N Nf : ℕ} (h : 2 * Nf < 11 * N) {g : ℝ} (hg : 0 < g) :
    betaOneLoop N Nf g < 0 := by
  have hb : 0 < b0 N Nf := b0_pos h
  have hg3 : 0 < g ^ 3 := pow_pos hg 3
  have hpi : 0 < 16 * Real.pi ^ 2 := by positivity
  unfold betaOneLoop
  apply div_neg_of_neg_of_pos _ hpi
  nlinarith

/-- Base case: pure `SU(3)` Yang–Mills (no fermions) is asymptotically free. -/
theorem asymptotic_freedom_sign_SU3 {g : ℝ} (hg : 0 < g) : betaOneLoop 3 0 g < 0 :=
  asymptotic_freedom_sign (by norm_num) hg

end Frontier

