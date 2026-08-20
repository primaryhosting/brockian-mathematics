/-
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open MeasureTheory Set Real

namespace Brockian
namespace DilationGenerator

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The substitution operator `U : (U f)(t) = e^{t/2} · f(eᵗ)`, at the level of functions. -/

noncomputable def mellinLogEquiv :
    Lp F 2 (volume.restrict (Ioi (0 : ℝ))) ≃ₗᵢ[𝕜] Lp F 2 (volume : Measure ℝ) :=
  LinearIsometryEquiv.mk
    { toFun := fun f => MemLp.toLp (logSub (f : ℝ → F)) (memLp_logSub (Lp.memLp f))
      map_add' := by
        intro f g
        refine Lp.ext ?_
        refine ((MemLp.coeFn_toLp _).trans ?_).trans (Lp.coeFn_add _ _).symm
        refine (logSub_congr_ae (Lp.coeFn_add f g)).trans ?_
        filter_upwards [MemLp.coeFn_toLp (memLp_logSub (Lp.memLp f)),
          MemLp.coeFn_toLp (memLp_logSub (Lp.memLp g))] with t h1 h2
        simp only [logSub, Pi.add_apply, smul_add, h1, h2]
      map_smul' := by
        intro c f
        refine Lp.ext ?_
        refine ((MemLp.coeFn_toLp _).trans ?_).trans (Lp.coeFn_smul _ _).symm
        refine (logSub_congr_ae (Lp.coeFn_smul c f)).trans ?_
        filter_upwards [MemLp.coeFn_toLp (memLp_logSub (Lp.memLp f))] with t h1
        simp only [logSub, Pi.smul_apply, h1, RingHom.id_apply, smul_comm]
      invFun := fun h => MemLp.toLp (logSubSymm (h : ℝ → F)) (memLp_logSubSymm (Lp.memLp h))
      left_inv := by
        intro f
        refine Lp.ext ?_
        refine (MemLp.coeFn_toLp _).trans ?_
        refine (logSubSymm_congr_ae (MemLp.coeFn_toLp (memLp_logSub (Lp.memLp f)))).trans ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact logSubSymm_logSub _ hx
      right_inv := by
        intro h
        refine Lp.ext ?_
        refine (MemLp.coeFn_toLp _).trans ?_
        refine (logSub_congr_ae (MemLp.coeFn_toLp (memLp_logSubSymm (Lp.memLp h)))).trans ?_
        rw [logSub_logSubSymm] }
    (by
      intro f
      simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_def]
      rw [eLpNorm_congr_ae (MemLp.coeFn_toLp _), eLpNorm_logSub])

@[simp]
