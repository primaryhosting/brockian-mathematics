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

noncomputable def freeScalar : RelativisticQuantumField where
  twoSpin := 0
  stat := 1
  stat_sq := by norm_num
  W := fun x => ((minkowskiSq x : ℝ) : ℂ)⁻¹
  locality := by intro x _; simp [minkowskiSq_neg]
  bhw := by intro x _; simp [minkowskiSq_neg]
  e := ![0, 1, 0, 0]
  e_spacelike := by
    norm_num [IsSpacelike, minkowskiSq, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons, Matrix.head_cons]
  Wc := fun z => -(z ^ 2)⁻¹
  analytic := by
    intro z hz
    have hz' : z ≠ 0 := by simpa using hz
    have h1 : AnalyticAt ℂ (fun z : ℂ => z ^ 2) z := analyticAt_id.pow 2
    exact (h1.inv (pow_ne_zero 2 hz')).neg
  slice := by
    intro t _
    have h : minkowskiSq (t • (![0, 1, 0, 0] : Spacetime)) = -t ^ 2 := by
      simp [minkowskiSq, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
        Matrix.head_cons]
    rw [h]
    push_cast
    ring
  nontrivial := ⟨1, one_ne_zero, by norm_num⟩

/-- A spin-`1/2`-type field (`2j = 1`, Fermi): a parity-odd two-point function
`W x = x⁰ / (x·x)²`, sliced along the spacelike direction `e = (1,2,0,0)`. -/
