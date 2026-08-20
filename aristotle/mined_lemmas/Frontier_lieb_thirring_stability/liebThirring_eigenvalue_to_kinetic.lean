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

theorem liebThirring_eigenvalue_to_kinetic {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 0 < L)
    (h : LiebThirringEigenvalue d L) : LiebThirringKinetic d (ltConst d L) := by
  intro n u hadm hint
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  set b : ℝ := 2 / (L * (d + 2)) with hbdef
  have hbpos : 0 < b := by rw [hbdef]; positivity
  set c : ℝ := b ^ ((2:ℝ)/d) with hcdef
  have hcpos : 0 < c := Real.rpow_pos_of_pos hbpos _
  have hcd : c ^ ((d:ℝ)/2) = b := by
    rw [hcdef, ← Real.rpow_mul hbpos.le, show (2:ℝ)/d * ((d:ℝ)/2) = 1 by field_simp,
      Real.rpow_one]
  set A : ℝ := ∫ x, density u x ^ ((1:ℝ) + 2/d) with hAdef
  set V : Space d → ℝ := fun x => -(c * density u x ^ ((2:ℝ)/d)) with hVdef
  have hnp : ∀ x, negPart (V x) = c * density u x ^ ((2:ℝ)/d) := fun x =>
    negPart_neg_of_nonneg (by have := density_nonneg u x; positivity)
  have hpow : ∀ x, negPart (V x) ^ ((1:ℝ) + d/2)
      = c ^ ((1:ℝ) + d/2) * density u x ^ ((1:ℝ) + 2/d) := by
    intro x
    rw [hnp x, Real.mul_rpow hcpos.le (Real.rpow_nonneg (density_nonneg u x) _),
      ← Real.rpow_mul (density_nonneg u x), show (2:ℝ)/d * ((1:ℝ) + d/2) = (1:ℝ) + 2/d by
        field_simp; ring]
  have hsplit : ∀ x, density u x ^ ((1:ℝ)+2/d) = density u x ^ ((2:ℝ)/d) * density u x := by
    intro x
    rw [show (1:ℝ)+2/d = (2:ℝ)/d + 1 by ring,
      Real.rpow_add' (density_nonneg u x) (by positivity), Real.rpow_one]
  have hVr : ∀ x, V x * density u x = -c * density u x ^ ((1:ℝ)+2/d) := by
    intro x; rw [hsplit x, hVdef]; ring
  have hint1 : Integrable (fun x => negPart (V x) ^ ((1:ℝ) + (d:ℝ)/2)) := by
    refine (hint.const_mul (c ^ ((1:ℝ) + (d:ℝ)/2))).congr ?_
    filter_upwards with x
    exact (hpow x).symm
  have hint2 : Integrable (fun x => V x * density u x) := by
    refine (hint.const_mul (-c)).congr ?_
    filter_upwards with x
    exact (hVr x).symm
  have hrmeas : Measurable (fun x => density u x) :=
    Finset.measurable_sum _ (fun i _ => ((hadm.measurable i).pow_const 2))
  have hVmeas : Measurable V := ((hrmeas.pow_const _).const_mul c).neg
  have hI1 : (∫ x, negPart (V x) ^ ((1:ℝ) + (d:ℝ)/2)) = c ^ ((1:ℝ) + (d:ℝ)/2) * A := by
    simp_rw [hpow]; rw [integral_const_mul, ← hAdef]
  have hI2 : potentialEnergy V u = -c * A := by
    unfold potentialEnergy; simp_rw [hVr]; rw [integral_const_mul, ← hAdef]
  have hmain := h n u V hadm hVmeas hint1 hint2
  rw [hI1, hI2] at hmain
  have hcsplit : c ^ ((1:ℝ)+(d:ℝ)/2) = c * c ^ ((d:ℝ)/2) := by
    rw [Real.rpow_add' hcpos.le (by positivity), Real.rpow_one]
  have hLc : L * c ^ ((1:ℝ)+(d:ℝ)/2) = c * (2/((d:ℝ)+2)) := by
    rw [hcsplit, hcd, hbdef]; field_simp
  have hlt : ltConst d L = ((d:ℝ)/((d:ℝ)+2)) * c := by rw [hcdef, hbdef]; rfl
  rw [hlt]
  have hkey : c*A - L*(c ^ ((1:ℝ)+(d:ℝ)/2))*A = ((d:ℝ)/((d:ℝ)+2))*c*A := by
    rw [hLc]; field_simp; ring
  nlinarith [hmain, hkey]

/-- **Base case of stability of matter**: a system with no nuclear charge has nonnegative
energy, hence satisfies the stability bound for every `C ≥ 0`. -/
