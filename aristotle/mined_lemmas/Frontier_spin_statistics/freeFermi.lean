import Mathlib
/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
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

/-! ## Minkowski spacetime -/

/-- Four dimensional Minkowski spacetime, as coordinate tuples `(x⁰, x¹, x², x³)`. -/
abbrev Spacetime : Type := Fin 4 → ℝ

/-- The Minkowski quadratic form `x·x = (x⁰)² - (x¹)² - (x²)² - (x³)²`
(mostly-minus signature). -/

noncomputable def freeFermi : RelativisticQuantumField where
  twoSpin := 1
  stat := -1
  stat_sq := by norm_num
  W := fun x => ((x 0 : ℝ) : ℂ) * (((minkowskiSq x) ^ 2 : ℝ) : ℂ)⁻¹
  locality := by
    intro x _
    have h : minkowskiSq (-x) = minkowskiSq x := minkowskiSq_neg x
    simp [h]
  bhw := by
    intro x _
    have h : minkowskiSq (-x) = minkowskiSq x := minkowskiSq_neg x
    simp [h]
  e := ![1, 2, 0, 0]
  e_spacelike := by
    norm_num [IsSpacelike, minkowskiSq, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons, Matrix.head_cons]
  Wc := fun z => (9 * z ^ 3)⁻¹
  analytic := by
    intro z hz
    have hz' : z ≠ 0 := by simpa using hz
    have h1 : AnalyticAt ℂ (fun z : ℂ => 9 * z ^ 3) z := analyticAt_const.mul (analyticAt_id.pow 3)
    exact h1.inv (by simp [hz'])
  slice := by
    intro t ht
    have hx0 : (t • (![1, 2, 0, 0] : Spacetime)) 0 = t := by simp
    have hms : minkowskiSq (t • (![1, 2, 0, 0] : Spacetime)) = -3 * t ^ 2 := by
      simp [minkowskiSq, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
        Matrix.head_cons]
      ring
    rw [hx0, hms]
    have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    push_cast
    field_simp
    ring
  nontrivial := ⟨1, one_ne_zero, by norm_num⟩

end Frontier

