/-
# Asymptotic Freedom Sign
Category: Frontier Physics
Target: Frontier.asymptotic_freedom_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not permit a module docstring `/-! ... -/` before `import`, so the
-- required header above is written as an ordinary block comment; its text is verbatim.)

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

namespace Frontier

/-- The one-loop beta-function coefficient `b₀` of an `SU(N)` gauge theory with
`Nf` Dirac fermions in the fundamental representation:
`b₀ = 11N/3 - 2Nf/3`. -/
noncomputable def betaZero (N Nf : ℕ) : ℝ :=
  (11 * (N : ℝ)) / 3 - (2 * (Nf : ℝ)) / 3

/-- The one-loop beta function of an `SU(N)` gauge theory with `Nf` fundamental
Dirac fermions, `β(g) = -b₀ g³ / (16π²)`. -/
noncomputable def betaOneLoop (N Nf : ℕ) (g : ℝ) : ℝ :=
  -betaZero N Nf * g ^ 3 / (16 * Real.pi ^ 2)

/-- **Asymptotic freedom sign.**  For an `SU(N)` gauge theory (`N ≥ 2`) with `Nf`
fundamental Dirac fermions satisfying the asymptotic-freedom bound `2 Nf < 11 N`
(i.e. `Nf < 11N/2`), the one-loop beta function is strictly negative at any
positive coupling `g`. -/
theorem asymptotic_freedom_sign
    (N Nf : ℕ) (hN : 2 ≤ N) (hNf : 2 * Nf < 11 * N) (g : ℝ) (hg : 0 < g) :
    betaOneLoop N Nf g < 0 := by
  have hb : 0 < betaZero N Nf := by
    have h : (2 * Nf : ℝ) < 11 * N := by
      exact_mod_cast hNf
    have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    unfold betaZero
    linarith
  have hpi : 0 < 16 * Real.pi ^ 2 := by positivity
  have hg3 : 0 < g ^ 3 := by positivity
  unfold betaOneLoop
  apply div_neg_of_neg_of_pos _ hpi
  nlinarith

/-- The physical QCD case: `SU(3)` with six quark flavours is asymptotically free. -/
theorem asymptotic_freedom_sign_qcd (g : ℝ) (hg : 0 < g) :
    betaOneLoop 3 6 g < 0 :=
  asymptotic_freedom_sign 3 6 (by norm_num) (by norm_num) g hg

/-- Pure `SU(N)` Yang–Mills (`Nf = 0`, `N ≥ 2`) is asymptotically free. -/
theorem asymptotic_freedom_sign_pure_gauge (N : ℕ) (hN : 2 ≤ N) (g : ℝ) (hg : 0 < g) :
    betaOneLoop N 0 g < 0 :=
  asymptotic_freedom_sign N 0 hN (by omega) g hg

#print axioms Frontier.asymptotic_freedom_sign

end Frontier

