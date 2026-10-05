/-
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
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

set_option grind.warning false

open MeasureTheory Set Real Asymptotics

namespace Frontier

/-! ## Mirzakhani's integration kernel -/

/-- The basic "logistic" profile appearing in Mirzakhani's kernels:
`logistic u = 1 / (1 + exp (u / 2))`. -/

lemma integral_mirzKernel_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    ∫ x in Ioi (0:ℝ), x * mirzKernel x t = t ^ 2 / 2 + 2 * π ^ 2 / 3 := by
  have iA : IntegrableOn (fun x => x * logistic (x + t)) (Ioi 0) volume := by
    simpa using integrableOn_affine_mul_logistic 0 1 0 t
  have iB : IntegrableOn (fun x => x * logistic (x + -t)) (Ioi 0) volume := by
    simpa using integrableOn_affine_mul_logistic 0 1 0 (-t)
  have i1 : IntegrableOn (fun y => (y + t) * logistic y) (Ioi (-t)) volume := by
    simpa using integrableOn_affine_mul_logistic' (-t) 1 t
  have i1' : IntegrableOn (fun y => (y + t) * logistic y) (Ioc (-t) t) volume :=
    i1.mono_set (fun x hx => hx.1)
  have i2 : IntegrableOn (fun y => (y + t) * logistic y) (Ioi t) volume := by
    simpa using integrableOn_affine_mul_logistic' t 1 t
  have i3 : IntegrableOn (fun y => (y - t) * logistic y) (Ioi t) volume := by
    have := integrableOn_affine_mul_logistic' t 1 (-t)
    refine this.congr_fun (fun x _ => by ring) measurableSet_Ioi
  have i4 : IntegrableOn (fun y => 2 * y * logistic y) (Ioi (0:ℝ)) volume := by
    have := integrableOn_affine_mul_logistic' 0 2 0
    refine this.congr_fun (fun x _ => by ring) measurableSet_Ioi
  have i4' : IntegrableOn (fun y => 2 * y * logistic y) (Ioc (0:ℝ) t) volume :=
    i4.mono_set (fun x hx => hx.1)
  have i4'' : IntegrableOn (fun y => 2 * y * logistic y) (Ioi t) volume :=
    i4.mono_set (fun x hx => lt_of_le_of_lt ht hx)
  -- split the kernel
  have hsplit : ∫ x in Ioi (0:ℝ), x * mirzKernel x t
      = (∫ x in Ioi (0:ℝ), x * logistic (x + t)) + ∫ x in Ioi (0:ℝ), x * logistic (x + -t) := by
    rw [← integral_add iA iB]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only
    rw [mirzKernel_eq, ← sub_eq_add_neg]
    ring
  have hA : ∫ x in Ioi (0:ℝ), x * logistic (x + t) = ∫ y in Ioi t, (y - t) * logistic y := by
    rw [← shift_Ioi (fun y => (y - t) * logistic y) t]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by simp)
  have hB : ∫ x in Ioi (0:ℝ), x * logistic (x + -t) = ∫ y in Ioi (-t), (y + t) * logistic y := by
    rw [← shift_Ioi (fun y => (y + t) * logistic y) (-t)]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by simp)
  have hdisj : Disjoint (Ioc (-t) t) (Ioi t) := by simp [Set.disjoint_left]
  have hunion : Ioc (-t) t ∪ Ioi t = Ioi (-t) := Set.Ioc_union_Ioi_eq_Ioi (by linarith)
  have hB2 : ∫ y in Ioi (-t), (y + t) * logistic y
      = (∫ y in Ioc (-t) t, (y + t) * logistic y) + ∫ y in Ioi t, (y + t) * logistic y := by
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Ioi i1' i2
  -- combine the two half-line pieces above `t`
  have hIoi : (∫ y in Ioi t, (y - t) * logistic y) + ∫ y in Ioi t, (y + t) * logistic y
      = ∫ y in Ioi t, 2 * y * logistic y := by
    rw [← integral_add i3 i2]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only
    ring
  -- reassemble the half-line integral of `2 y logistic y`
  have hfull : (∫ y in Ioc (0:ℝ) t, 2 * y * logistic y) + ∫ y in Ioi t, 2 * y * logistic y
      = ∫ y in Ioi (0:ℝ), 2 * y * logistic y := by
    rw [← setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi i4' i4'',
      Set.Ioc_union_Ioi_eq_Ioi ht]
  have hval : ∫ y in Ioi (0:ℝ), 2 * y * logistic y = 2 * (π ^ 2 / 3) := by
    rw [← integral_lin_mul_logistic, ← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring
  rw [hsplit, hA, hB, hB2, integral_Ioc_reflect ht]
  have : (∫ y in Ioi t, (y - t) * logistic y)
      + (t ^ 2 / 2 + (∫ y in Ioc (0:ℝ) t, 2 * y * logistic y)
        + ∫ y in Ioi t, (y + t) * logistic y)
      = t ^ 2 / 2 + ((∫ y in Ioc (0:ℝ) t, 2 * y * logistic y)
        + ((∫ y in Ioi t, (y - t) * logistic y) + ∫ y in Ioi t, (y + t) * logistic y)) := by
    ring
  rw [this, hIoi, hfull, hval]
  ring

/-- The basic kernel integral `F₁(t) = ∫₀^∞ x H(x,t) dx = t²/2 + 2π²/3`. -/
