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

lemma hasDerivAt_snd {f : ℝ → ℂ × ℂ} {w : ℂ × ℂ} {t : ℝ} (h : HasDerivAt f w t) :
    HasDerivAt (fun s => (f s).2) w.2 t :=
  (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t h

/-- A phase-space solution really solves the second-order equation: its first component `u`
is differentiable with derivative the second component, and that second component is
differentiable with derivative `(q - z) u`. -/
