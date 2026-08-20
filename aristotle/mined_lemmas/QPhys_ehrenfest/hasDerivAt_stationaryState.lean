/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The commutator `[H, A] = H A - A H` of two continuous linear operators. -/

theorem hasDerivAt_stationaryState (hbar E0 : ℝ) (H : E →L[ℂ] E) (v : E)
    (hv : H v = (E0 : ℂ) • v) (t : ℝ) :
    HasDerivAt (stationaryState hbar E0 v)
      ((-Complex.I / hbar) • H (stationaryState hbar E0 v t)) t := by
  have hlin : HasDerivAt (fun s : ℝ => -Complex.I * E0 * s / hbar)
      (-Complex.I * E0 / hbar) t := by
    simpa [mul_div_assoc] using
      ((hasDerivAt_id t).ofReal_comp.const_mul (-Complex.I * E0)).div_const hbar
  have hexp := (hlin.cexp).smul_const v
  refine hexp.congr_deriv ?_
  simp only [stationaryState, hv, smul_smul, ContinuousLinearMap.map_smul]
  congr 1
  field_simp

/-- **Non-vacuity / consistency check.** In a stationary state, the expectation value of a
time-independent observable `B` is constant: its derivative vanishes.  This is derived from
`QPhys.ehrenfest`, so in particular the hypotheses of that theorem are satisfiable. -/
