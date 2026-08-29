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

def deficiencyEval (q : ℝ → ℂ) (z : ℂ) (μ : Measure ℝ) (t₀ : ℝ) :
    deficiencySubmodule q z μ →ₗ[ℂ] ℂ × ℂ where
  toFun Y := (Y : ℝ → ℂ × ℂ) t₀
  map_add' := by intro Y W; rfl
  map_smul' := by intro c Y; rfl

/-- **Deficiency represents the ODE (under weak regularity only).**

Let `q : ℝ → ℂ` be weakly regular (bounded on compact intervals — no continuity, smoothness or
measurability is assumed) and let `z : ℂ`.  Then, for the deficiency space at `z` relative to any
measure `μ`:

1. every element of the deficiency space is genuinely a solution of the Sturm–Liouville
   differential equation `-u'' + q u = z u`, its two components being `u` and `u'`;
2. an element of the deficiency space is uniquely determined by its initial data
   `(u t₀, u' t₀)` at any point `t₀`, i.e. the deficiency space is faithfully represented
   inside the two-dimensional space of initial data of the ODE;
3. consequently the deficiency space is finite-dimensional and the deficiency index is at most
   the order `2` of the differential expression. -/
