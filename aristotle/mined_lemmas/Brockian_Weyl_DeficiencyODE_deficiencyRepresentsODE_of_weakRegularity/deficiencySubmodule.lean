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

import Mathlib

/-!
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Set MeasureTheory

namespace Brockian.Weyl.DeficiencyODE

/-- **Weak regularity of the potential.** The coefficient `q` is bounded on every compact
interval.  This is far weaker than continuity (no measurability, no smoothness); it is exactly
the amount of regularity needed for Weyl's deficiency theory of the Sturm–Liouville expression
`τ u = -u'' + q u`. -/

def deficiencySubmodule (q : ℝ → ℂ) (z : ℂ) (μ : Measure ℝ) : Submodule ℂ (ℝ → ℂ × ℂ) where
  carrier := {Y | IsPhaseSolution q z Y ∧ MemLp (fun t => (Y t).1) 2 μ}
  add_mem' := by
    rintro Y W ⟨hY, hY2⟩ ⟨hW, hW2⟩
    refine ⟨fun t => ?_, ?_⟩
    · have h := (hY t).add (hW t)
      refine h.congr_deriv ?_
      simp only [field, Pi.add_apply, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
      rw [mul_add]
    · exact hY2.add hW2
  zero_mem' := by
    refine ⟨fun t => ?_, ?_⟩
    · have h : HasDerivAt (fun _ : ℝ => (0 : ℂ × ℂ)) 0 t := hasDerivAt_const t 0
      refine h.congr_deriv ?_
      simp [field, Prod.ext_iff]
    · simp
  smul_mem' := by
    rintro c Y ⟨hY, hY2⟩
    refine ⟨fun t => ?_, ?_⟩
    · have h := (hY t).const_smul c
      refine h.congr_deriv ?_
      simp only [field, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, smul_eq_mul]
      ring_nf
    · exact hY2.const_smul c

/-- Evaluation of a deficiency element at a point `t₀`, i.e. taking the initial data
`(u t₀, u' t₀)` of the solution. -/
