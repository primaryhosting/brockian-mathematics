/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The Lieb–Thirring constant appearing in the kinetic energy inequality that is dual to
the Lieb–Thirring eigenvalue bound with constant `L` (in dimension `3`, exponent `γ = 1`). -/

theorem young_liebThirring {L a b : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ≤ ltKineticConst L * a ^ ((5 : ℝ) / 3) + L * b ^ ((5 : ℝ) / 2) := by
  have hconj : Real.HolderConjugate ((5 : ℝ) / 3) ((5 : ℝ) / 2) := by constructor <;> norm_num
  set s : ℝ := 2 / (5 * L) with hs_def
  have hs : 0 < s := by positivity
  set t : ℝ := s ^ ((2 : ℝ) / 5) with ht_def
  have ht : 0 < t := Real.rpow_pos_of_pos hs _
  have hyoung := Real.young_inequality_of_nonneg (a := t * a) (b := b / t)
    (mul_nonneg ht.le ha) (div_nonneg hb ht.le) hconj
  have e0 : (t * a) * (b / t) = a * b := by field_simp
  have e1 : (t * a) ^ ((5 : ℝ) / 3) = s ^ ((2 : ℝ) / 3) * a ^ ((5 : ℝ) / 3) := by
    rw [Real.mul_rpow ht.le ha, ht_def, ← Real.rpow_mul hs.le]
    norm_num
  have e2 : (b / t) ^ ((5 : ℝ) / 2) = b ^ ((5 : ℝ) / 2) / s := by
    rw [Real.div_rpow hb ht.le, ht_def, ← Real.rpow_mul hs.le]
    norm_num
  rw [e0, e1, e2] at hyoung
  have key : s ^ ((2 : ℝ) / 3) * a ^ ((5 : ℝ) / 3) / (5 / 3) + b ^ ((5 : ℝ) / 2) / s / (5 / 2)
      = ltKineticConst L * a ^ ((5 : ℝ) / 3) + L * b ^ ((5 : ℝ) / 2) := by
    rw [ltKineticConst, ← hs_def, hs_def]
    field_simp
  linarith [hyoung, key.le, key.ge]

/-- **Legendre duality step.** If for every nonnegative potential `V` the kinetic energy `T`
of the state dominates `∫ V ρ - L ∫ V ^ (5/2)` (this is exactly what the Lieb–Thirring
eigenvalue bound `∑ |λ_j(-Δ - V)| ≤ L ∫ V₊^(5/2)` gives for a fermionic state with
one-particle density `ρ`), then `T` obeys the Thomas–Fermi type kinetic energy inequality
`T ≥ K_L ∫ ρ^(5/3)`. -/
