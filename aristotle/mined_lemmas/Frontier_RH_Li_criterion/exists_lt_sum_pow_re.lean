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

/-!
# Li's criterion (finite / Bombieri–Lagarias core)

Li's criterion states that the Riemann Hypothesis is equivalent to the non-negativity of the
Li coefficients
`λ_n = ∑_ρ (1 - (1 - 1/ρ)^n)`,
the sum being over the non-trivial zeros of the Riemann zeta function (equivalently, the zeros
of the completed function `ξ`), counted with multiplicity.

This file formalises and proves the arithmetic-free *core* of the criterion: the equivalence
for an arbitrary **finite** family of non-zero complex numbers `ρ i` that is closed under the
functional-equation symmetry `ρ ↦ 1 - ρ`.  For such a family,

* every `ρ i` lies on the critical line `Re ρ = 1/2`

  if and only if

* all the Li coefficients `λ_n`, `n ≥ 1`, have non-negative real part.

This is exactly the statement of Li's criterion with the zero multiset of `ξ` replaced by a
finite symmetric multiset; the two ingredients that are special to `ξ` (the Hadamard product,
which produces the zero multiset and the convergence of the defining series) are not part of
this statement.

The mathematical content proved here is:

* the *Möbius dictionary* `‖1 - 1/ρ‖ = 1 ↔ Re ρ = 1/2` and `1 < ‖1 - 1/ρ‖ ↔ Re ρ < 1/2`
  (`Frontier.norm_one_sub_inv_eq_one_iff`, `Frontier.one_lt_norm_one_sub_inv_iff`);
* the easy direction, that a zero on the critical line contributes a non-negative real part
  to every `λ_n`;
* the hard direction, a Diophantine/recurrence argument (the finite analogue of the
  Bombieri–Lagarias argument): if some `‖z i‖ > 1`, then the power sums `∑ i, Re (z i ^ n)`
  are unbounded above, because arbitrarily large powers `n` can be chosen so that all the
  `z i ^ n` point in almost the same direction as the positive real axis.
-/

namespace Frontier

open Complex Filter

/-! ### The Möbius dictionary -/

/-- The basic identity behind Li's criterion: `‖1 - 1/ρ‖` compares with `1` exactly as
`Re ρ` compares with `1/2`. -/

theorem exists_lt_sum_pow_re {ι : Type*} [Fintype ι] (z : ι → ℂ) (i₀ : ι) (hi₀ : 1 < ‖z i₀‖)
    (C : ℝ) : ∃ n : ℕ, 1 ≤ n ∧ C < ∑ i, (z i ^ n).re := by
  classical
  set u : ι → ℂ := fun i => if z i = 0 then 1 else z i / (‖z i‖ : ℂ) with hu_def
  have hu : ∀ i, ‖u i‖ = 1 := by
    intro i
    by_cases h : z i = 0
    · simp [hu_def, h]
    · have hz : (‖z i‖ : ℝ) ≠ 0 := by simpa using h
      simp [hu_def, h, hz]
  have hfac : ∀ (i : ι) (n : ℕ), z i ^ n = ((‖z i‖ : ℂ)) ^ n * u i ^ n := by
    intro i n
    by_cases h : z i = 0
    · simp [hu_def, h]
    · have hz : ((‖z i‖ : ℂ)) ≠ 0 := by
        simpa [Complex.ofReal_eq_zero] using (norm_ne_zero_iff.2 h)
      rw [← mul_pow]
      congr 1
      simp only [hu_def, h, if_false]
      field_simp
  -- choose a threshold exponent
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, max C 0 * 2 < ‖z i₀‖ ^ N₀ := pow_unbounded_of_one_lt _ hi₀
  obtain ⟨n, hnN, hn1, hclose⟩ :=
    exists_large_pow_sub_one_norm_le u hu (δ := (1 : ℝ) / 2) (by norm_num) N₀
  refine ⟨n, hn1, ?_⟩
  -- each term has real part at least ‖z i‖ ^ n / 2
  have hterm : ∀ i, ‖z i‖ ^ n / 2 ≤ (z i ^ n).re := by
    intro i
    have h1 : (1 : ℝ) / 2 ≤ (u i ^ n).re := by
      have h2 : (1 - u i ^ n).re ≤ ‖1 - u i ^ n‖ := Complex.re_le_norm _
      have h3 : ‖1 - u i ^ n‖ = ‖u i ^ n - 1‖ := by rw [norm_sub_rev]
      have := hclose i
      simp only [Complex.sub_re, Complex.one_re] at h2
      linarith [h2, h3 ▸ (hclose i)]
    have h4 : (z i ^ n).re = ‖z i‖ ^ n * (u i ^ n).re := by
      rw [hfac i n, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    have h5 : (0 : ℝ) ≤ ‖z i‖ ^ n := by positivity
    rw [h4]
    nlinarith
  have hnonneg : ∀ i ∈ Finset.univ, 0 ≤ (z i ^ n).re := by
    intro i _
    have := hterm i
    have h5 : (0 : ℝ) ≤ ‖z i‖ ^ n := by positivity
    linarith
  have hsum : (z i₀ ^ n).re ≤ ∑ i, (z i ^ n).re :=
    Finset.single_le_sum hnonneg (Finset.mem_univ i₀)
  have hmono : ‖z i₀‖ ^ N₀ ≤ ‖z i₀‖ ^ n :=
    pow_le_pow_right₀ (le_of_lt hi₀) hnN
  have hCle : C ≤ max C 0 := le_max_left _ _
  have := hterm i₀
  nlinarith [le_max_right C (0:ℝ)]

/-! ### The Li coefficients and the criterion -/

/-- The `n`-th Li coefficient of a finite family of (non-zero) complex numbers `ρ`:
`λ_n = ∑_i (1 - (1 - 1/ρ i)^n)`. -/
