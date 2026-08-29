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

open scoped BigOperators
open scoped Real
open scoped Classical

open MeasureTheory Set

namespace Brockian.Weyl.DeficiencyODE

/-- `IsWeakSolution q z u v` says that the pair `(u, v)` is a *weak* solution of the
deficiency equation `u'' = (q - z) * u` of the Sturm–Liouville expression
`L u = -u'' + q u`, in the sense that `u` and `v` are merely continuous and satisfy the
integrated (Volterra) form of the system `u' = v`, `v' = (q - z) u`.

No differentiability whatsoever is assumed: this is the "weak regularity" hypothesis. -/
structure IsWeakSolution (q : ℝ → ℂ) (z : ℂ) (u v : ℝ → ℂ) : Prop where
  continuous_u : Continuous u
  continuous_v : Continuous v
  integral_u : ∀ t : ℝ, u t = u 0 + ∫ s in (0:ℝ)..t, v s
  integral_v : ∀ t : ℝ, v t = v 0 + ∫ s in (0:ℝ)..t, (q s - z) * u s

variable {q : ℝ → ℂ} {z : ℂ} {u v : ℝ → ℂ}

/-- A weak solution is automatically differentiable, with derivative the second component. -/

theorem hasDerivAt_cexp_ofReal (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (s : ℂ)) (Complex.exp (t : ℂ)) t :=
  (Complex.hasDerivAt_exp ((t : ℂ))).comp_ofReal

/-- The notion of weak solution is non-vacuous: for `q = 0` and `z = -1` the exponential
is a nonzero weak solution of `u'' = (q - z) u`, i.e. of `u'' = u`. -/
