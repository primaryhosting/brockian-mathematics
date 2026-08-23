import Mathlib
import Brockian.Cassini

/-!
# Ford circles: Farey tangency and the Fibonacci chain

This module gives a Euclidean realization of the determinant arithmetic already present in
`Brockian.FareySeparation` and `Brockian.Cassini`.

For an integer numerator `a` and positive natural denominator `q`, the Ford circle has center

`a / q + (1 / (2q²)) i`

and radius `1 / (2q²)`.  The main geometric theorem proves that two such circles are externally
tangent exactly when the square of their cross-determinant is one.  For integer data this is the
usual Farey-neighbor condition `|ad - cq| = 1`.

Applying Cassini's identity then shows that the Ford circles based at consecutive Fibonacci
convergents `Fₙ/Fₙ₊₁` and `Fₙ₊₁/Fₙ₊₂` are tangent.

All results here are classical reference mathematics.  They do not enter the novelty ledger and
do not identify the Farey graph with the phase-depth pentagon.

Reference: Lester R. Ford, *Fractions*, The American Mathematical Monthly 45 (1938).
-/

namespace Brockian.FordCircles

open Complex EuclideanGeometry
open Filter
open scoped Topology goldenRatio

noncomputable section

/-- The radius of the Ford circle with denominator `q`. -/
def fordRadius (q : ℕ) : ℝ :=
  1 / (2 * (q : ℝ) ^ 2)

/-- The center in the complex upper half-plane of the Ford circle based at `a / q`. -/
def fordCenter (a : ℤ) (q : ℕ) : ℂ :=
  Complex.ofReal ((a : ℝ) / (q : ℝ)) + Complex.ofReal (fordRadius q) * I

/-- The Ford circle based at the rational data `a / q`, represented as a Euclidean sphere in
the complex plane. Positivity and reducedness are hypotheses of the relevant theorems rather
than fields of this definition. -/
def fordCircle (a : ℤ) (q : ℕ) : Sphere ℂ where
  center := fordCenter a q
  radius := fordRadius q

/-- The integral cross-determinant of two rational data pairs. -/
def crossDet (a : ℤ) (q : ℕ) (c : ℤ) (d : ℕ) : ℤ :=
  a * d - c * q

/-- The real point at which the Ford circle is tangent to the boundary line. -/
def fordBase (a : ℤ) (q : ℕ) : ℂ :=
  Complex.ofReal ((a : ℝ) / (q : ℝ))

@[simp] theorem fordCircle_center (a : ℤ) (q : ℕ) :
    (fordCircle a q).center = fordCenter a q := rfl

@[simp] theorem fordCircle_radius (a : ℤ) (q : ℕ) :
    (fordCircle a q).radius = fordRadius q := rfl

theorem fordRadius_pos {q : ℕ} (hq : 0 < q) : 0 < fordRadius q := by
  simp only [fordRadius, one_div]
  positivity

theorem fordRadius_nonneg {q : ℕ} (hq : 0 < q) : 0 ≤ fordRadius q :=
  (fordRadius_pos hq).le

@[simp] theorem fordCenter_re (a : ℤ) (q : ℕ) :
    (fordCenter a q).re = (a : ℝ) / (q : ℝ) := by
  simp [fordCenter]

@[simp] theorem fordCenter_im (a : ℤ) (q : ℕ) :
    (fordCenter a q).im = fordRadius q := by
  simp [fordCenter]

@[simp] theorem fordBase_re (a : ℤ) (q : ℕ) :
    (fordBase a q).re = (a : ℝ) / (q : ℝ) := by
  simp [fordBase]

@[simp] theorem fordBase_im (a : ℤ) (q : ℕ) :
    (fordBase a q).im = 0 := by
  simp [fordBase]

/-- The rational base point lies on its Ford circle. -/
theorem fordBase_mem_fordCircle (a : ℤ) {q : ℕ} (hq : 0 < q) :
    fordBase a q ∈ fordCircle a q := by
  rw [mem_sphere']
  simp only [fordCircle_center, fordCircle_radius, fordBase, fordCenter, dist_eq_norm]
  rw [Complex.norm_def]
  simp only [Complex.normSq_apply, add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im,
    I_re, I_im, mul_zero, mul_one, sub_re, sub_im, add_zero, sub_zero, sub_self, zero_add]
  rw [show fordRadius q * fordRadius q = fordRadius q ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_pos (fordRadius_pos hq)]

/-- The exact squared-distance defect from external tangency. The right-hand side isolates the
arithmetic obstruction: it vanishes exactly when the cross-determinant has square one. -/
theorem ford_distance_gap (a c : ℤ) {q d : ℕ} (hq : 0 < q) (hd : 0 < d) :
    dist (fordCenter a q) (fordCenter c d) ^ 2 -
        (fordRadius q + fordRadius d) ^ 2 =
      (((a : ℝ) * (d : ℝ) - (c : ℝ) * (q : ℝ)) ^ 2 - 1) /
        ((q : ℝ) ^ 2 * (d : ℝ) ^ 2) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hcenter :
      fordCenter a q - fordCenter c d =
        ((((a : ℝ) / (q : ℝ) - (c : ℝ) / (d : ℝ) : ℝ) : ℂ) +
          (((fordRadius q - fordRadius d : ℝ) : ℂ) * I)) := by
    simp only [fordCenter]
    push_cast
    ring
  rw [dist_eq_norm, Complex.sq_norm, hcenter, Complex.normSq_add_mul_I]
  simp only [fordRadius]
  field_simp
  ring

/-- **Ford tangency criterion.** Two Ford circles with positive denominators are externally
tangent exactly when the square of the real cross-determinant is one. -/
theorem ford_isExtTangent_iff_crossDet_sq (a c : ℤ) {q d : ℕ} (hq : 0 < q) (hd : 0 < d) :
    (fordCircle a q).IsExtTangent (fordCircle c d) ↔
      ((a : ℝ) * (d : ℝ) - (c : ℝ) * (q : ℝ)) ^ 2 = 1 := by
  rw [Sphere.isExtTangent_iff_dist_center]
  simp only [fordCircle_center, fordCircle_radius]
  have hrq : 0 ≤ fordRadius q := fordRadius_nonneg hq
  have hrd : 0 ≤ fordRadius d := fordRadius_nonneg hd
  simp only [hrq, hrd, and_self, and_true]
  rw [← sq_eq_sq₀ dist_nonneg (add_nonneg hrq hrd)]
  have hden : 0 < (q : ℝ) ^ 2 * (d : ℝ) ^ 2 := by positivity
  constructor
  · intro ht
    have hgap := ford_distance_gap a c hq hd
    rw [ht, sub_self] at hgap
    exact (sub_eq_zero.mp (div_eq_zero_iff.mp hgap.symm |>.resolve_right (ne_of_gt hden)))
  · intro hdet
    have hgap := ford_distance_gap a c hq hd
    rw [hdet, sub_self, zero_div] at hgap
    linarith

@[simp] theorem crossDet_cast_real (a c : ℤ) (q d : ℕ) :
    (crossDet a q c d : ℝ) =
      (a : ℝ) * (d : ℝ) - (c : ℝ) * (q : ℝ) := by
  simp [crossDet]

/-- The integral form of the Ford tangency criterion: external tangency is equivalent to the
usual Farey-neighbor condition `|ad - cq| = 1`. -/
theorem ford_isExtTangent_iff_crossDet_natAbs (a c : ℤ) {q d : ℕ}
    (hq : 0 < q) (hd : 0 < d) :
    (fordCircle a q).IsExtTangent (fordCircle c d) ↔
      (crossDet a q c d).natAbs = 1 := by
  rw [ford_isExtTangent_iff_crossDet_sq a c hq hd, ← crossDet_cast_real]
  constructor
  · intro h
    have hz : crossDet a q c d ^ 2 = (1 : ℤ) ^ 2 := by exact_mod_cast h
    simpa using (Int.natAbs_eq_iff_sq_eq.mpr hz)
  · intro h
    have hz : crossDet a q c d ^ 2 = (1 : ℤ) ^ 2 := by
      apply Int.natAbs_eq_iff_sq_eq.mp
      simpa using h
    exact_mod_cast hz

/-- Distinct rational data have nonoverlapping Ford interiors: a nonzero integral
cross-determinant forces the center distance to be at least the sum of the radii. Equality is
the tangent/Farey-neighbor case characterized above. -/
theorem ford_radius_add_le_dist_of_crossDet_ne_zero (a c : ℤ) {q d : ℕ}
    (hq : 0 < q) (hd : 0 < d) (hdet : crossDet a q c d ≠ 0) :
    fordRadius q + fordRadius d ≤ dist (fordCenter a q) (fordCenter c d) := by
  have hrq : 0 ≤ fordRadius q := fordRadius_nonneg hq
  have hrd : 0 ≤ fordRadius d := fordRadius_nonneg hd
  rw [← sq_le_sq₀ (add_nonneg hrq hrd) dist_nonneg]
  have habsInt : (1 : ℤ) ≤ |crossDet a q c d| := Int.one_le_abs hdet
  have habsReal : (1 : ℝ) ≤ |(crossDet a q c d : ℝ)| := by exact_mod_cast habsInt
  have hdetSq : (1 : ℝ) ≤ (crossDet a q c d : ℝ) ^ 2 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (crossDet a q c d : ℝ)]
  have hden : 0 < (q : ℝ) ^ 2 * (d : ℝ) ^ 2 := by positivity
  have hgap := ford_distance_gap a c hq hd
  rw [← crossDet_cast_real] at hgap
  have hnonneg :
      0 ≤ (((crossDet a q c d : ℝ) ^ 2 - 1) /
        ((q : ℝ) ^ 2 * (d : ℝ) ^ 2)) :=
    div_nonneg (sub_nonneg.mpr hdetSq) hden.le
  linarith

/-! ## The Fibonacci Ford chain -/

/-- The Ford circle based at the Fibonacci convergent `Fₙ/Fₙ₊₁`. -/
def fibonacciFordCircle (n : ℕ) : Sphere ℂ :=
  fordCircle (Nat.fib n) (Nat.fib (n + 1))

/-- The radius of the Ford circle based at `Fₙ/Fₙ₊₁`. -/
def fibonacciFordRadius (n : ℕ) : ℝ :=
  fordRadius (Nat.fib (n + 1))

@[simp] theorem fibonacciFordCircle_center (n : ℕ) :
    (fibonacciFordCircle n).center = fordCenter (Nat.fib n) (Nat.fib (n + 1)) := rfl

@[simp] theorem fibonacciFordCircle_radius (n : ℕ) :
    (fibonacciFordCircle n).radius = fibonacciFordRadius n := rfl

/-- Consecutive Fibonacci numbers give reduced fractions. -/
theorem fibonacciFord_reduced (n : ℕ) :
    Nat.Coprime (Nat.fib n) (Nat.fib (n + 1)) :=
  Nat.fib_coprime_fib_succ n

/-- Cassini's identity is exactly the unimodularity condition for consecutive Fibonacci
convergents. -/
theorem fibonacci_crossDet_natAbs (n : ℕ) :
    (crossDet (Nat.fib n) (Nat.fib (n + 1))
      (Nat.fib (n + 1)) (Nat.fib (n + 2))).natAbs = 1 := by
  have hdet :
      crossDet (Nat.fib n) (Nat.fib (n + 1))
          (Nat.fib (n + 1)) (Nat.fib (n + 2)) = (-1 : ℤ) ^ (n + 1) := by
    simpa [crossDet, pow_two] using Brockian.Cassini.cassini n
  rw [hdet]
  simp

/-- **Fibonacci Ford chain.** Every Ford circle based at `Fₙ/Fₙ₊₁` is externally tangent to
the next one, based at `Fₙ₊₁/Fₙ₊₂`. -/
theorem fibonacciFord_isExtTangent_succ (n : ℕ) :
    (fibonacciFordCircle n).IsExtTangent (fibonacciFordCircle (n + 1)) := by
  have hq : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (by omega)
  have hd : 0 < Nat.fib (n + 2) := Nat.fib_pos.mpr (by omega)
  rw [fibonacciFordCircle, fibonacciFordCircle, show n + 1 + 1 = n + 2 by omega]
  exact (ford_isExtTangent_iff_crossDet_natAbs
    (Nat.fib n) (Nat.fib (n + 1)) hq hd).mpr (fibonacci_crossDet_natAbs n)

/-- The real coordinates of the Fibonacci Ford centers converge to `φ⁻¹`, the reciprocal of
the golden ratio. -/
theorem tendsto_fibonacciFordCenter_re :
    Tendsto (fun n : ℕ => (fibonacciFordCircle n).center.re) atTop
      (𝓝 (Real.goldenRatio⁻¹)) := by
  have h := tendsto_fib_div_fib_succ_atTop
  rw [← Real.inv_goldenRatio] at h
  simpa [fibonacciFordCircle, fordCircle, fordCenter] using h

/-- The radii in the Fibonacci Ford chain tend to zero. -/
theorem tendsto_fibonacciFordRadius_zero :
    Tendsto fibonacciFordRadius atTop (𝓝 0) := by
  have hfibNat : Tendsto (fun n : ℕ => Nat.fib (n + 1)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b, ?_⟩
    intro a ha
    have h := Nat.le_fib_add_one (a + 1)
    omega
  have hfibReal : Tendsto (fun n : ℕ => (Nat.fib (n + 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hfibNat
  have hsq : Tendsto (fun n : ℕ => (Nat.fib (n + 1) : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp hfibReal
  have hden : Tendsto (fun n : ℕ => 2 * (Nat.fib (n + 1) : ℝ) ^ 2) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) hsq
  unfold fibonacciFordRadius fordRadius
  convert hden.inv_tendsto_atTop using 1
  funext n
  simp [Pi.inv_apply]

/-- The Fibonacci Ford centers converge in the complex plane to the boundary point `φ⁻¹`. -/
theorem tendsto_fibonacciFordCenter :
    Tendsto (fun n : ℕ => (fibonacciFordCircle n).center) atTop
      (𝓝 (Complex.ofReal (Real.goldenRatio⁻¹))) := by
  have hre := tendsto_fibonacciFordCenter_re.ofReal
  have him := tendsto_fibonacciFordRadius_zero.ofReal
  have hcenter := hre.add (him.mul_const I)
  simpa [fibonacciFordCircle, fordCircle, fordCenter, fibonacciFordRadius] using hcenter

/-- Exact ratio between consecutive radii in the Fibonacci Ford chain. -/
theorem fibonacciFordRadius_succ_div (n : ℕ) :
    fibonacciFordRadius (n + 1) / fibonacciFordRadius n =
      ((Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)) ^ 2 := by
  have hq : (Nat.fib (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.fib_pos.mpr (by omega : 0 < n + 1))
  have hd : (Nat.fib (n + 2) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.fib_pos.mpr (by omega : 0 < n + 2))
  simp only [fibonacciFordRadius, fordRadius]
  field_simp

/-- The ratios of successive Ford radii converge to `φ⁻²`. -/
theorem tendsto_fibonacciFordRadius_ratio :
    Tendsto (fun n : ℕ => fibonacciFordRadius (n + 1) / fibonacciFordRadius n) atTop
      (𝓝 ((Real.goldenRatio⁻¹) ^ 2)) := by
  have h := tendsto_fib_div_fib_succ_atTop.comp (tendsto_add_atTop_nat 1)
  rw [← Real.inv_goldenRatio] at h
  have hsq := h.pow 2
  simpa only [Function.comp_apply, fibonacciFordRadius_succ_div] using hsq

end

end Brockian.FordCircles
