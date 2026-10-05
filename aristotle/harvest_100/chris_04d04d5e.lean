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

/-- The one-loop beta-function coefficient `b₀` of an `SU(N)` gauge theory with
`nf` Dirac fermions in the fundamental representation:
`b₀ = 11 N / 3 - 2 nf / 3`. -/
noncomputable def betaZero (N nf : ℕ) : ℝ := 11 * (N : ℝ) / 3 - 2 * (nf : ℝ) / 3

/-- The one-loop beta function of the `SU(N)` gauge coupling `g`:
`β(g) = - b₀ g³ / (16 π²)`. -/
noncomputable def betaOneLoop (N nf : ℕ) (g : ℝ) : ℝ :=
  -betaZero N nf * g ^ 3 / (16 * Real.pi ^ 2)

/-- Positivity of the one-loop coefficient `b₀` when the number of flavours obeys
`2 nf < 11 N` (in particular for pure gauge theory, `nf = 0`, with `N ≥ 1`). -/
theorem betaZero_pos {N nf : ℕ} (h : 2 * nf < 11 * N) : 0 < betaZero N nf := by
  have h' : (2 : ℝ) * (nf : ℝ) < 11 * (N : ℝ) := by exact_mod_cast h
  unfold betaZero
  linarith

/-- **Asymptotic freedom sign.**  For an `SU(N)` gauge theory with `nf` fermion flavours
satisfying `2 nf < 11 N` (e.g. QCD, `N = 3`, `nf ≤ 16`), and any nonzero coupling `g > 0`,
the one-loop beta function is strictly negative: the coupling decreases at short distances. -/
theorem asymptotic_freedom_sign {N nf : ℕ} (h : 2 * nf < 11 * N) {g : ℝ} (hg : 0 < g) :
    betaOneLoop N nf g < 0 := by
  have hb : 0 < betaZero N nf := betaZero_pos h
  have hg3 : 0 < g ^ 3 := by positivity
  have hden : 0 < 16 * Real.pi ^ 2 := by positivity
  unfold betaOneLoop
  apply div_neg_of_neg_of_pos _ hden
  nlinarith

end Frontier

