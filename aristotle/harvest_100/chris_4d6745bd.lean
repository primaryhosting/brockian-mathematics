import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
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

namespace Brockian

/-- The cosine coordinate of the `k`-th "isotypic" vector for the regular `n`-gon:
the function `m ↦ cos (2πkm/n)` on the vertices `m` of the `n`-gon. -/
noncomputable def ngonCos (n : ℕ) (k m : ℤ) : ℝ := Real.cos (2 * Real.pi * k * m / n)

/-- The sine coordinate of the `k`-th "isotypic" vector for the regular `n`-gon:
the function `m ↦ sin (2πkm/n)` on the vertices `m` of the `n`-gon. -/
noncomputable def ngonSin (n : ℕ) (k m : ℤ) : ℝ := Real.sin (2 * Real.pi * k * m / n)

section Basic

variable {n : ℕ} {k m : ℤ}

lemma ngonCos_succ (hn : n ≠ 0) :
    ngonCos n k (m + 1) =
      Real.cos (2 * Real.pi * k / n) * ngonCos n k m
        - Real.sin (2 * Real.pi * k / n) * ngonSin n k m := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have harg : 2 * Real.pi * (k : ℝ) * ((m : ℝ) + 1) / n
      = 2 * Real.pi * (k : ℝ) * m / n + 2 * Real.pi * (k : ℝ) / n := by
    field_simp
  simp only [ngonCos, ngonSin]
  push_cast
  rw [harg, Real.cos_add]
  ring

lemma ngonSin_succ (hn : n ≠ 0) :
    ngonSin n k (m + 1) =
      Real.cos (2 * Real.pi * k / n) * ngonSin n k m
        + Real.sin (2 * Real.pi * k / n) * ngonCos n k m := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have harg : 2 * Real.pi * (k : ℝ) * ((m : ℝ) + 1) / n
      = 2 * Real.pi * (k : ℝ) * m / n + 2 * Real.pi * (k : ℝ) / n := by
    field_simp
  simp only [ngonCos, ngonSin]
  push_cast
  rw [harg, Real.sin_add]
  ring

lemma ngonCos_neg : ngonCos n k (-m) = ngonCos n k m := by
  simp only [ngonCos]
  push_cast
  rw [show 2 * Real.pi * (k : ℝ) * (-(m : ℝ)) / n = -(2 * Real.pi * (k : ℝ) * m / n) by ring,
    Real.cos_neg]

lemma ngonSin_neg : ngonSin n k (-m) = -ngonSin n k m := by
  simp only [ngonSin]
  push_cast
  rw [show 2 * Real.pi * (k : ℝ) * (-(m : ℝ)) / n = -(2 * Real.pi * (k : ℝ) * m / n) by ring,
    Real.sin_neg]

lemma ngonCos_add_period (hn : n ≠ 0) : ngonCos n k (m + n) = ngonCos n k m := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have harg : 2 * Real.pi * (k : ℝ) * ((m : ℝ) + n) / n
      = 2 * Real.pi * (k : ℝ) * m / n + (k : ℝ) * (2 * Real.pi) := by
    field_simp
  simp only [ngonCos]
  push_cast
  rw [harg, Real.cos_add_int_mul_two_pi]

lemma ngonSin_add_period (hn : n ≠ 0) : ngonSin n k (m + n) = ngonSin n k m := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have harg : 2 * Real.pi * (k : ℝ) * ((m : ℝ) + n) / n
      = 2 * Real.pi * (k : ℝ) * m / n + (k : ℝ) * (2 * Real.pi) := by
    field_simp
  simp only [ngonSin]
  push_cast
  rw [harg, Real.sin_add_int_mul_two_pi]

lemma ngonCos_sq_add_ngonSin_sq : (ngonCos n k m) ^ 2 + (ngonSin n k m) ^ 2 = 1 := by
  simp only [ngonCos, ngonSin]
  exact Real.cos_sq_add_sin_sq _

end Basic

section Orthogonality

/-- The `n`-th root of unity attached to the frequency `k`. -/
noncomputable def ngonRoot (n : ℕ) (k : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * k / n)

lemma ngonRoot_pow (n : ℕ) (k : ℤ) (j : ℕ) (hn : n ≠ 0) :
    (ngonRoot n k) ^ j = Complex.exp (((2 * Real.pi * k * j / n : ℝ) : ℂ) * Complex.I) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [ngonRoot, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

lemma ngonRoot_ne_one (n : ℕ) (k : ℤ) (hn : n ≠ 0) (hk : ¬ ((n : ℤ) ∣ k)) :
    ngonRoot n k ≠ 1 := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  intro h
  rw [ngonRoot, Complex.exp_eq_one_iff] at h
  obtain ⟨j, hj⟩ := h
  rw [div_eq_iff hn'] at hj
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [hpi, Complex.I_ne_zero]
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ)
      = (2 * (Real.pi : ℂ) * Complex.I) * ((j : ℂ) * n) := by linear_combination hj
  have hkz : k = j * n := by exact_mod_cast mul_left_cancel₀ hne h2
  exact hk ⟨j, by rw [hkz]; ring⟩

lemma ngonRoot_pow_card (n : ℕ) (k : ℤ) (hn : n ≠ 0) : (ngonRoot n k) ^ n = 1 := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [ngonRoot, ← Complex.exp_nat_mul]
  have : (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * k / n) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    field_simp
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

/-- The full geometric sum of the `k`-th root of unity over the vertices of the `n`-gon
vanishes whenever the frequency `k` is not a multiple of `n`. -/
lemma sum_ngonRoot_pow_eq_zero (n : ℕ) (k : ℤ) (hn : n ≠ 0) (hk : ¬ ((n : ℤ) ∣ k)) :
    ∑ j ∈ Finset.range n, (ngonRoot n k) ^ j = 0 := by
  rw [geom_sum_eq (ngonRoot_ne_one n k hn hk), ngonRoot_pow_card n k hn]
  simp

lemma sum_ngonCos_eq_zero (n : ℕ) (k : ℤ) (hn : n ≠ 0) (hk : ¬ ((n : ℤ) ∣ k)) :
    ∑ j ∈ Finset.range n, ngonCos n k j = 0 := by
  have h := sum_ngonRoot_pow_eq_zero n k hn hk
  have h2 : (∑ j ∈ Finset.range n, (ngonRoot n k) ^ j).re = 0 := by rw [h]; simp
  rw [Complex.re_sum] at h2
  rw [← h2]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [ngonRoot_pow n k j hn, Complex.exp_ofReal_mul_I_re, ngonCos]
  norm_num

lemma sum_ngonSin_eq_zero (n : ℕ) (k : ℤ) (hn : n ≠ 0) (hk : ¬ ((n : ℤ) ∣ k)) :
    ∑ j ∈ Finset.range n, ngonSin n k j = 0 := by
  have h := sum_ngonRoot_pow_eq_zero n k hn hk
  have h2 : (∑ j ∈ Finset.range n, (ngonRoot n k) ^ j).im = 0 := by rw [h]; simp
  rw [Complex.im_sum] at h2
  rw [← h2]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [ngonRoot_pow n k j hn, Complex.exp_ofReal_mul_I_im, ngonSin]
  norm_num

end Orthogonality

/-- **Pentagon Pentagon Isotypic Higher N.**

The `D₅` pentagon picture generalizes to every regular `n`-gon with `n ≥ 3`.
For every frequency `k` the pair of vectors `(ngonCos n k, ngonSin n k)` indexed by the
vertices `m ∈ ℤ/n` spans a plane which is invariant under the dihedral action:
the rotation by one vertex acts on this plane as the planar rotation by the angle `2πk/n`
(items 1 and 2), the reflection `m ↦ -m` acts as the reflection fixing the cosine vector
and negating the sine vector (items 3 and 4), and both vectors are genuinely `n`-periodic,
i.e. well defined on the vertices of the `n`-gon (items 5 and 6).
Item 7 is the normalization `cos² + sin² = 1`, and item 8 says that for a frequency `k`
which is not a multiple of `n` this plane contains no trivial isotypic component:
both coordinate vectors sum to zero over the vertices. -/
theorem PentagonPentagonIsotypicHigherN (n : ℕ) (hn : 3 ≤ n) (k m : ℤ) :
    ngonCos n k (m + 1) =
        Real.cos (2 * Real.pi * k / n) * ngonCos n k m
          - Real.sin (2 * Real.pi * k / n) * ngonSin n k m ∧
      ngonSin n k (m + 1) =
        Real.cos (2 * Real.pi * k / n) * ngonSin n k m
          + Real.sin (2 * Real.pi * k / n) * ngonCos n k m ∧
      ngonCos n k (-m) = ngonCos n k m ∧
      ngonSin n k (-m) = -ngonSin n k m ∧
      ngonCos n k (m + n) = ngonCos n k m ∧
      ngonSin n k (m + n) = ngonSin n k m ∧
      (ngonCos n k m) ^ 2 + (ngonSin n k m) ^ 2 = 1 ∧
      (¬ ((n : ℤ) ∣ k) →
        (∑ j ∈ Finset.range n, ngonCos n k j = 0 ∧
          ∑ j ∈ Finset.range n, ngonSin n k j = 0)) := by
  have hn0 : n ≠ 0 := by omega
  refine ⟨ngonCos_succ hn0, ngonSin_succ hn0, ngonCos_neg, ngonSin_neg,
    ngonCos_add_period hn0, ngonSin_add_period hn0, ngonCos_sq_add_ngonSin_sq, ?_⟩
  intro hk
  exact ⟨sum_ngonCos_eq_zero n k hn0 hk, sum_ngonSin_eq_zero n k hn0 hk⟩

/-- The pentagon (`n = 5`, the `D₅` case) is the special case of the general statement. -/
theorem PentagonIsotypic (k m : ℤ) :
    ngonCos 5 k (m + 1) =
        Real.cos (2 * Real.pi * k / 5) * ngonCos 5 k m
          - Real.sin (2 * Real.pi * k / 5) * ngonSin 5 k m ∧
      ngonCos 5 k (m + 5) = ngonCos 5 k m ∧
      (¬ ((5 : ℤ) ∣ k) → ∑ j ∈ Finset.range 5, ngonCos 5 k j = 0) := by
  obtain ⟨h1, -, -, -, h5, -, -, h8⟩ := PentagonPentagonIsotypicHigherN 5 (by norm_num) k m
  refine ⟨by simpa using h1, by simpa using h5, ?_⟩
  intro hk
  exact (h8 (by simpa using hk)).1

end Brockian

