import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

open MeasureTheory

/-! ## Basic objects -/

/-- Physical space `ℝ^d`, with its Euclidean structure and Lebesgue measure. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Negative part `t⁻ = max (-t) 0` of a real number. -/

lemma ltConst_pos {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 0 < L) : 0 < ltConst d L := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hb : (0:ℝ) < 2 / (L * (d + 2)) := by positivity
  unfold ltConst
  positivity

/-- **Legendre duality reduction.**  The Lieb–Thirring bound on the sum of negative
eigenvalues implies the Lieb–Thirring kinetic energy inequality, with the explicit
(optimal, for this argument) constant `ltConst d L`. -/
