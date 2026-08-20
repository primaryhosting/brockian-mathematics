/-
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

/-- The cosine coordinate of the `k`-th Fourier mode on the vertices of a regular `n`-gon:
`ngonCos n k j = cos (2π k j / n)`. -/
noncomputable def ngonCos (n : ℕ) (k j : ℤ) : ℝ := Real.cos (2 * Real.pi * k * j / n)

/-- The sine coordinate of the `k`-th Fourier mode on the vertices of a regular `n`-gon:
`ngonSin n k j = sin (2π k j / n)`. -/
noncomputable def ngonSin (n : ℕ) (k j : ℤ) : ℝ := Real.sin (2 * Real.pi * k * j / n)

/-! ### Vanishing of the exponential sum -/

/-- If `n ∤ k` then the `n` powers of the root of unity `exp (2π i k / n)` sum to zero. -/
theorem sum_exp_eq_zero (n : ℕ) (k : ℤ) (hn : 0 < n) (hk : ¬ ((n : ℤ) ∣ k)) :
    ∑ j ∈ Finset.range n, Complex.exp (2 * Real.pi * Complex.I * k * j / n) = 0 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hz : Complex.exp (2 * Real.pi * Complex.I * k / n) ≠ 1 := by
    intro h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    field_simp at hm
    exact hk ⟨m, by exact_mod_cast hm⟩
  have key : ∀ j : ℕ, Complex.exp (2 * Real.pi * Complex.I * k * j / n)
      = (Complex.exp (2 * Real.pi * Complex.I * k / n)) ^ j := by
    intro j
    rw [← Complex.exp_nat_mul]
    ring_nf
  simp only [key]
  rw [geom_sum_eq hz]
  have hpow : (Complex.exp (2 * Real.pi * Complex.I * k / n)) ^ n = 1 := by
    rw [← Complex.exp_nat_mul]
    have harg : (n : ℂ) * (2 * Real.pi * Complex.I * k / n)
        = (k : ℂ) * (2 * Real.pi * Complex.I) := by field_simp
    rw [harg, Complex.exp_int_mul_two_pi_mul_I]
  rw [hpow]
  simp

private theorem exp_arg_eq (n : ℕ) (k : ℤ) (j : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * k * j / n)
      = Complex.exp (((2 * Real.pi * k * j / n : ℝ) : ℂ) * Complex.I) := by
  congr 1
  push_cast
  ring

/-- The `k`-th cosine mode sums to zero over the vertices of the `n`-gon when `n ∤ k`. -/
theorem sum_ngonCos_eq_zero (n : ℕ) (k : ℤ) (hn : 0 < n) (hk : ¬ ((n : ℤ) ∣ k)) :
    ∑ j ∈ Finset.range n, ngonCos n k j = 0 := by
  have h := sum_exp_eq_zero n k hn hk
  simp only [exp_arg_eq] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  simp only [Complex.exp_ofReal_mul_I_re, Complex.zero_re] at h2
  simpa only [ngonCos, Int.cast_natCast] using h2

/-- The `k`-th sine mode sums to zero over the vertices of the `n`-gon when `n ∤ k`. -/
theorem sum_ngonSin_eq_zero (n : ℕ) (k : ℤ) (hn : 0 < n) (hk : ¬ ((n : ℤ) ∣ k)) :
    ∑ j ∈ Finset.range n, ngonSin n k j = 0 := by
  have h := sum_exp_eq_zero n k hn hk
  simp only [exp_arg_eq] at h
  have h2 := congrArg Complex.im h
  rw [Complex.im_sum] at h2
  simp only [Complex.exp_ofReal_mul_I_im, Complex.zero_im] at h2
  simpa only [ngonSin, Int.cast_natCast] using h2

/-! ### Product-to-sum identities -/

private theorem arg_sub (n : ℕ) (k l j : ℤ) :
    (2 * Real.pi * ((k : ℝ) - l) * j / n)
      = 2 * Real.pi * k * j / n - 2 * Real.pi * l * j / n := by ring

private theorem arg_add (n : ℕ) (k l j : ℤ) :
    (2 * Real.pi * ((k : ℝ) + l) * j / n)
      = 2 * Real.pi * k * j / n + 2 * Real.pi * l * j / n := by ring

theorem ngonCos_mul_ngonCos (n : ℕ) (k l j : ℤ) :
    ngonCos n k j * ngonCos n l j
      = (ngonCos n (k - l) j + ngonCos n (k + l) j) / 2 := by
  simp only [ngonCos, Int.cast_sub, Int.cast_add, arg_sub, arg_add, Real.cos_sub, Real.cos_add]
  ring

theorem ngonSin_mul_ngonSin (n : ℕ) (k l j : ℤ) :
    ngonSin n k j * ngonSin n l j
      = (ngonCos n (k - l) j - ngonCos n (k + l) j) / 2 := by
  simp only [ngonCos, ngonSin, Int.cast_sub, Int.cast_add, arg_sub, arg_add,
    Real.cos_sub, Real.cos_add]
  ring

theorem ngonCos_mul_ngonSin (n : ℕ) (k l j : ℤ) :
    ngonCos n k j * ngonSin n l j
      = (ngonSin n (k + l) j - ngonSin n (k - l) j) / 2 := by
  simp only [ngonCos, ngonSin, Int.cast_sub, Int.cast_add, arg_sub, arg_add,
    Real.sin_sub, Real.sin_add]
  ring

theorem ngonCos_sq (n : ℕ) (k j : ℤ) :
    ngonCos n k j ^ 2 = 1 / 2 + ngonCos n (2 * k) j / 2 := by
  have h1 : (2 * Real.pi * ((2 : ℝ) * k) * j / n) = 2 * (2 * Real.pi * k * j / n) := by ring
  simp only [ngonCos, Int.cast_mul, Int.cast_ofNat, h1, Real.cos_sq]

theorem ngonSin_sq (n : ℕ) (k j : ℤ) :
    ngonSin n k j ^ 2 = 1 / 2 - ngonCos n (2 * k) j / 2 := by
  have h1 : (2 * Real.pi * ((2 : ℝ) * k) * j / n) = 2 * (2 * Real.pi * k * j / n) := by ring
  simp only [ngonSin, ngonCos, Int.cast_mul, Int.cast_ofNat, h1, Real.sin_sq, Real.cos_sq]
  ring

/-! ### Equivariance -/

theorem ngonCos_add_period (n : ℕ) (hn : 0 < n) (k j : ℤ) :
    ngonCos n k (j + n) = ngonCos n k j := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h1 : (2 * Real.pi * (k : ℝ) * ((j : ℝ) + n) / n)
      = 2 * Real.pi * k * j / n + (k : ℝ) * (2 * Real.pi) := by field_simp
  simp only [ngonCos, Int.cast_add, Int.cast_natCast, h1]
  exact Real.cos_add_int_mul_two_pi _ k

theorem ngonSin_add_period (n : ℕ) (hn : 0 < n) (k j : ℤ) :
    ngonSin n k (j + n) = ngonSin n k j := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h1 : (2 * Real.pi * (k : ℝ) * ((j : ℝ) + n) / n)
      = 2 * Real.pi * k * j / n + (k : ℝ) * (2 * Real.pi) := by field_simp
  simp only [ngonSin, Int.cast_add, Int.cast_natCast, h1]
  exact Real.sin_add_int_mul_two_pi _ k

theorem ngonCos_succ (n : ℕ) (k j : ℤ) :
    ngonCos n k (j + 1)
      = Real.cos (2 * Real.pi * k / n) * ngonCos n k j
        - Real.sin (2 * Real.pi * k / n) * ngonSin n k j := by
  have h1 : (2 * Real.pi * (k : ℝ) * ((j : ℝ) + 1) / n)
      = 2 * Real.pi * k * j / n + 2 * Real.pi * k / n := by ring
  simp only [ngonCos, ngonSin, Int.cast_add, Int.cast_one, h1, Real.cos_add]
  ring

theorem ngonSin_succ (n : ℕ) (k j : ℤ) :
    ngonSin n k (j + 1)
      = Real.sin (2 * Real.pi * k / n) * ngonCos n k j
        + Real.cos (2 * Real.pi * k / n) * ngonSin n k j := by
  have h1 : (2 * Real.pi * (k : ℝ) * ((j : ℝ) + 1) / n)
      = 2 * Real.pi * k * j / n + 2 * Real.pi * k / n := by ring
  simp only [ngonCos, ngonSin, Int.cast_add, Int.cast_one, h1, Real.sin_add]
  ring

theorem ngonCos_neg (n : ℕ) (k j : ℤ) : ngonCos n k (-j) = ngonCos n k j := by
  have h1 : (2 * Real.pi * (k : ℝ) * (-(j : ℝ)) / n) = -(2 * Real.pi * k * j / n) := by ring
  simp only [ngonCos, Int.cast_neg, h1, Real.cos_neg]

theorem ngonSin_neg (n : ℕ) (k j : ℤ) : ngonSin n k (-j) = - ngonSin n k j := by
  have h1 : (2 * Real.pi * (k : ℝ) * (-(j : ℝ)) / n) = -(2 * Real.pi * k * j / n) := by ring
  simp only [ngonSin, Int.cast_neg, h1, Real.sin_neg]

/-! ### The main theorem -/

/-- **Higher-`n` isotypic decomposition of the `n`-gon representation.**

For `n ≥ 3` and a frequency `k` not divisible by `n`, the pair of vectors
`(ngonCos n k ·, ngonSin n k ·)` indexed by the vertices of a regular `n`-gon spans a
two-dimensional subspace of `ℝ^n` on which the cyclic rotation of the `n`-gon acts as the
plane rotation by `2πk/n` and the reflection `j ↦ -j` acts diagonally; this subspace is
orthogonal to the trivial isotypic component, orthogonal to the isotypic components of all
other frequencies `l` (i.e. `n ∤ k - l` and `n ∤ k + l`), and, when `n ∤ 2k`, carries the
standard normalisation `‖·‖² = n/2` with the two coordinate vectors orthogonal.

Specialising to `n = 5` recovers the pentagon (`D₅`) statements. -/
theorem PentagonPentagonIsotypicHigherN (n : ℕ) (hn : 3 ≤ n) (k : ℤ)
    (hk : ¬ ((n : ℤ) ∣ k)) :
    -- periodicity in the vertex index
    (∀ j : ℤ, ngonCos n k (j + n) = ngonCos n k j) ∧
    (∀ j : ℤ, ngonSin n k (j + n) = ngonSin n k j) ∧
    -- the rotation `j ↦ j + 1` acts as the plane rotation by the angle `2πk/n`
    (∀ j : ℤ, ngonCos n k (j + 1)
        = Real.cos (2 * Real.pi * k / n) * ngonCos n k j
          - Real.sin (2 * Real.pi * k / n) * ngonSin n k j) ∧
    (∀ j : ℤ, ngonSin n k (j + 1)
        = Real.sin (2 * Real.pi * k / n) * ngonCos n k j
          + Real.cos (2 * Real.pi * k / n) * ngonSin n k j) ∧
    -- the reflection `j ↦ -j` acts diagonally
    (∀ j : ℤ, ngonCos n k (-j) = ngonCos n k j) ∧
    (∀ j : ℤ, ngonSin n k (-j) = - ngonSin n k j) ∧
    -- orthogonality to the trivial isotypic component
    (∑ j ∈ Finset.range n, ngonCos n k j = 0) ∧
    (∑ j ∈ Finset.range n, ngonSin n k j = 0) ∧
    -- orthogonality to every other isotypic component
    (∀ l : ℤ, ¬ ((n : ℤ) ∣ (k - l)) → ¬ ((n : ℤ) ∣ (k + l)) →
        (∑ j ∈ Finset.range n, ngonCos n k j * ngonCos n l j = 0) ∧
        (∑ j ∈ Finset.range n, ngonSin n k j * ngonSin n l j = 0) ∧
        (∑ j ∈ Finset.range n, ngonCos n k j * ngonSin n l j = 0)) ∧
    -- normalisation inside the `k`-th isotypic component
    (¬ ((n : ℤ) ∣ 2 * k) →
        (∑ j ∈ Finset.range n, ngonCos n k j ^ 2 = n / 2) ∧
        (∑ j ∈ Finset.range n, ngonSin n k j ^ 2 = n / 2) ∧
        (∑ j ∈ Finset.range n, ngonCos n k j * ngonSin n k j = 0)) := by
  have hn0 : 0 < n := by omega
  refine ⟨fun j => ngonCos_add_period n hn0 k j, fun j => ngonSin_add_period n hn0 k j,
    fun j => ngonCos_succ n k j, fun j => ngonSin_succ n k j,
    fun j => ngonCos_neg n k j, fun j => ngonSin_neg n k j,
    sum_ngonCos_eq_zero n k hn0 hk, sum_ngonSin_eq_zero n k hn0 hk, ?_, ?_⟩
  · intro l hsub hadd
    refine ⟨?_, ?_, ?_⟩
    · simp only [ngonCos_mul_ngonCos]
      rw [← Finset.sum_div, Finset.sum_add_distrib, sum_ngonCos_eq_zero n _ hn0 hsub,
        sum_ngonCos_eq_zero n _ hn0 hadd]
      norm_num
    · simp only [ngonSin_mul_ngonSin]
      rw [← Finset.sum_div, Finset.sum_sub_distrib, sum_ngonCos_eq_zero n _ hn0 hsub,
        sum_ngonCos_eq_zero n _ hn0 hadd]
      norm_num
    · simp only [ngonCos_mul_ngonSin]
      rw [← Finset.sum_div, Finset.sum_sub_distrib, sum_ngonSin_eq_zero n _ hn0 hsub,
        sum_ngonSin_eq_zero n _ hn0 hadd]
      norm_num
  · intro h2k
    have hzero : ∑ j ∈ Finset.range n, ngonCos n (2 * k) j = 0 :=
      sum_ngonCos_eq_zero n _ hn0 h2k
    have hsin : ∑ j ∈ Finset.range n, ngonSin n (2 * k) j = 0 :=
      sum_ngonSin_eq_zero n _ hn0 h2k
    have hhalf : ∑ j ∈ Finset.range n, ngonCos n (2 * k) j / 2 = 0 := by
      rw [← Finset.sum_div, hzero, zero_div]
    refine ⟨?_, ?_, ?_⟩
    · simp only [ngonCos_sq]
      rw [Finset.sum_add_distrib, hhalf, Finset.sum_const, Finset.card_range]
      ring
    · simp only [ngonSin_sq]
      rw [Finset.sum_sub_distrib, hhalf, Finset.sum_const, Finset.card_range]
      ring
    · have hcs : ∀ j : ℤ, ngonCos n k j * ngonSin n k j = ngonSin n (2 * k) j / 2 := by
        intro j
        rw [ngonCos_mul_ngonSin n k k j]
        have h1 : k - k = 0 := by ring
        have h2 : k + k = 2 * k := by ring
        rw [h1, h2]
        simp [ngonSin]
      simp only [hcs]
      rw [← Finset.sum_div, hsin]
      norm_num

/-! ### The pentagon (`D₅`) case, recovered from the higher-`n` statement -/

/-- Specialising the main theorem to `n = 5`: every nonzero frequency mod `5` gives a
two-dimensional isotypic component of the pentagon representation, orthogonal to the trivial
component and normalised by `5/2`. -/
theorem pentagon_isotypic (k : ℤ) (hk : ¬ ((5 : ℤ) ∣ k)) :
    (∑ j ∈ Finset.range 5, ngonCos 5 k j = 0) ∧
    (∑ j ∈ Finset.range 5, ngonSin 5 k j = 0) ∧
    (∑ j ∈ Finset.range 5, ngonCos 5 k j ^ 2 = 5 / 2) ∧
    (∑ j ∈ Finset.range 5, ngonSin 5 k j ^ 2 = 5 / 2) ∧
    (∑ j ∈ Finset.range 5, ngonCos 5 k j * ngonSin 5 k j = 0) := by
  have h5 : ¬ ((5 : ℤ) ∣ 2 * k) := by omega
  obtain ⟨-, -, -, -, -, -, hc, hs, -, hnorm⟩ :=
    PentagonPentagonIsotypicHigherN 5 (by norm_num) k (by exact_mod_cast hk)
  obtain ⟨hc2, hs2, hcs⟩ := hnorm (by exact_mod_cast h5)
  exact ⟨hc, hs, by exact_mod_cast hc2, by exact_mod_cast hs2, hcs⟩

/-- The five vertex-cosines of a regular pentagon sum to zero. -/
theorem pentagon_sum_cos_eq_zero :
    ∑ j ∈ Finset.range 5, Real.cos (2 * Real.pi * j / 5) = 0 := by
  have h := (pentagon_isotypic 1 (by norm_num)).1
  rw [← h]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [ngonCos]
  push_cast
  ring_nf

end Brockian

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

