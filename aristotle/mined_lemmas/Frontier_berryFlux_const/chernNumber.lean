/-
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
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

/-- The (first) Chern number of a Bloch band with Berry curvature `F` on the Brillouin-zone
torus `[0, 2π] × [0, 2π]`: the integral of the Berry curvature divided by `2π`. -/

noncomputable def chernNumber (F : ℝ → ℝ → ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ kx in (0:ℝ)..(2 * Real.pi), ∫ ky in (0:ℝ)..(2 * Real.pi), F kx ky

/-- The TKNN (Thouless–Kohmoto–Nightingale–den Nijs) Hall conductance of a filled Bloch band
with Berry curvature `F`, in terms of the conductance quantum `e² / h`. -/
