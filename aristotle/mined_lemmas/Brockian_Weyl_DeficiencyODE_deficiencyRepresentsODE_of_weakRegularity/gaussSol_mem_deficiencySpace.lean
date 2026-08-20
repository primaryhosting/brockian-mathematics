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

/-
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Set MeasureTheory

namespace Brockian.Weyl.DeficiencyODE

/-- The state space of a first-order linear system of `n` equations. -/
abbrev State (n : ℕ) : Type := Fin n → ℂ

variable {n : ℕ}

/-- *Weak regularity* of the coefficient family of the first-order linear system
`u' t = A t (u t)`: the coefficient operators depend continuously on time.  This is the
hypothesis retained in the Weyl-theoretic statement below. -/

theorem gaussSol_mem_deficiencySpace : gaussSol ∈ deficiencySpace gaussCoeff := by
  constructor
  · intro t
    have hr : HasDerivAt (fun s : ℝ => Real.exp (-s ^ 2)) (Real.exp (-t ^ 2) * (-(2 * t))) t := by
      have h1 : HasDerivAt (fun s : ℝ => -s ^ 2) (-(2 * t)) t := by
        simpa using (hasDerivAt_pow 2 t).neg
      simpa using h1.exp
    have hc : HasDerivAt (fun s : ℝ => ((Real.exp (-s ^ 2) : ℝ) : ℂ))
        (((Real.exp (-t ^ 2) * (-(2 * t)) : ℝ) : ℂ)) t := hr.ofReal_comp
    rw [hasDerivAt_pi]
    intro i
    simpa [gaussSol, gaussCoeff, Complex.ofReal_mul, mul_comm] using hc
  · have hnorm : ∀ t : ℝ, ‖gaussSol t‖ = Real.exp (-t ^ 2) := by
      intro t
      unfold gaussSol
      simp [Pi.norm_def, Complex.norm_exp, -Complex.ofReal_pow]
    have hcont : Continuous gaussSol := by
      unfold gaussSol; exact continuous_pi fun _ => by fun_prop
    show MemLp gaussSol 2 volume
    rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
    have hI : Integrable (fun t : ℝ => Real.exp (-2 * t ^ 2)) volume :=
      integrable_exp_neg_mul_sq (by norm_num)
    refine hI.congr ?_
    filter_upwards with t
    rw [hnorm t, show (-2 * t ^ 2 : ℝ) = (-t ^ 2) + (-t ^ 2) by ring, Real.exp_add]
    ring

/-- The bound proved above is not vacuous: there are weakly regular systems whose deficiency
space is nonzero. -/
