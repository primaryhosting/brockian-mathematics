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

import Brockian.RiemannScaffold
open Brockian.RiemannScaffold
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

/-!
# The completed zeta / Riemann ξ functional equation and the ζ ↔ ξ zero correspondence

This file wires Mathlib 4.32's *unconditional* completed-zeta functional equation
`completedRiemannZeta (1 - s) = completedRiemannZeta s` into the Brockian
`RiemannScaffold` ξ-normalization `ξ(s) = s (s-1) Λ(s)`, and then proves the full
zero correspondence between the completed function ξ and the Riemann zeta ζ.

## What is proved (all UNCONDITIONAL)

* `completedRiemannZeta_functional_equation` — Mathlib's `Λ(1-s) = Λ(s)`, restated
  at the Brockian import boundary.
* `riemannXi_apply` — the definitional connection `ξ(s) = s (s-1) Λ(s)` made an
  explicit lemma so downstream files never need to `unfold`.
* `riemannXi_functional_equation` — the classical **ξ functional equation**
  `ξ(1-s) = ξ(s)`, derived from Mathlib's completed-zeta symmetry plus the
  polynomial factor `s(s-1)` (which is itself invariant under `s ↦ 1-s`).
* `zeta_zero_of_riemannXi_zero` — the *converse* zero direction: a ξ-zero away from
  the explicit factor points `s = 0, 1` forces `ζ(s) = 0`.  (RiemannScaffold already
  supplies the forward direction `riemannXi_eq_zero_of_nontrivial_zeta_zero`.)
* `riemannXi_eq_zero_iff_zeta_zero_of_mem_critical_strip` — inside the open critical
  strip `0 < Re s < 1` the two zero sets coincide **exactly**: `ξ(s) = 0 ↔ ζ(s) = 0`.
  In the strip the trivial-zero lattice and the factor points `s = 0, 1` are all
  absent, so no artifacts intervene.
* `zeta_zero_one_sub_of_mem_critical_strip` — the reflection corollary: a nontrivial
  ζ-zero in the strip has its mirror `1-s` as a ζ-zero as well (also in the strip).

## What is NOT proved

* **Nothing conditional is claimed as unconditional.**  This file does not touch RH,
  the location of the nontrivial zeros, or the `BrockianSystem` Hilbert–Pólya schema
  of `RiemannScaffold` Part 2.  It supplies only the genuine (Mathlib-backed)
  functional equation and the exact ζ ↔ ξ zero dictionary in the critical strip.
* The correspondence is stated for the *open* strip `0 < Re s < 1`; the boundary
  lines `Re s ∈ {0, 1}` and the trivial-zero lattice are deliberately outside scope
  (there the factor `s(s-1)` and `Λ`'s poles produce the well-known artifacts, which
  `RiemannScaffold` already documents).
-/

namespace Brockian.XiFunctionalEquation

open Complex

/-- **Mathlib's completed-zeta functional equation, restated.**  `Λ(1-s) = Λ(s)`,
where `Λ = completedRiemannZeta`.  This is unconditional (`completedRiemannZeta_one_sub`). -/
theorem completedRiemannZeta_functional_equation (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

/-- **The definitional connection to Mathlib's completed zeta.**  The Brockian ξ is
`ξ(s) = s (s-1) Λ(s)`. -/
theorem riemannXi_apply (s : ℂ) :
    RiemannScaffold.riemannXi s = s * (s - 1) * completedRiemannZeta s :=
  rfl

/-- **The Riemann ξ functional equation (UNCONDITIONAL).**  `ξ(1-s) = ξ(s)`.
Combines Mathlib's `completedRiemannZeta_one_sub` with the invariance of the
polynomial factor `s(s-1)` under `s ↦ 1-s`. -/
theorem riemannXi_functional_equation (s : ℂ) :
    RiemannScaffold.riemannXi (1 - s) = RiemannScaffold.riemannXi s := by
  rw [riemannXi_apply, riemannXi_apply, completedRiemannZeta_one_sub]
  ring

/-- **Converse zero direction (UNCONDITIONAL).**  If `ξ(s) = 0` at a point that is
neither of the two explicit factor points `s = 0, 1`, then `ζ(s) = 0`.

Proof: `ξ(s) = s (s-1) Λ(s) = 0` with `s ≠ 0` and `s - 1 ≠ 0` forces `Λ(s) = 0`;
then `ζ(s) = Λ(s) / Gammaℝ s = 0 / Gammaℝ s = 0` (valid for `s ≠ 0`, and `0/x = 0`
regardless of whether the Γ-factor vanishes). -/
theorem zeta_zero_of_riemannXi_zero {s : ℂ}
    (h : RiemannScaffold.riemannXi s = 0) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannZeta s = 0 := by
  have hΛ : completedRiemannZeta s = 0 := by
    rw [riemannXi_apply] at h
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rcases mul_eq_zero.mp h with h' | hΛ
    · rcases mul_eq_zero.mp h' with h0 | h1
      · exact absurd h0 hs0
      · exact absurd h1 hs1'
    · exact hΛ
  rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]

/-- **Exact ζ ↔ ξ zero correspondence in the open critical strip (UNCONDITIONAL).**
For `0 < Re s < 1`, `ξ(s) = 0 ↔ ζ(s) = 0`.

Inside the strip the factor points `s = 0, 1` are absent (their real parts are `0`
and `1`), and the whole trivial-zero lattice `{-2(n+1)}` is absent (its real parts
are `≤ -2 < 0`), so the two directions
(`zeta_zero_of_riemannXi_zero` and RiemannScaffold's
`riemannXi_eq_zero_of_nontrivial_zeta_zero`) combine with no artifacts. -/
theorem riemannXi_eq_zero_iff_zeta_zero_of_mem_critical_strip {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    RiemannScaffold.riemannXi s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at h0
  have hs1 : s ≠ 1 := by rintro rfl; simp at h1
  have htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, rfl⟩
    have hre : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by
      simp [Complex.mul_re, Complex.add_re, Complex.add_im]
    rw [hre] at h0
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  constructor
  · intro h; exact zeta_zero_of_riemannXi_zero h hs0 hs1
  · intro h
    exact RiemannScaffold.riemannXi_eq_zero_of_nontrivial_zeta_zero h htriv hs1

/-- **Reflection of nontrivial ζ-zeros (UNCONDITIONAL).**  If `ζ(s) = 0` with
`0 < Re s < 1`, then `ζ(1-s) = 0` as well (and `1-s` lies in the strip too).
This is the functional equation acting on the zero set, transported through the
critical-strip correspondence. -/
theorem zeta_zero_one_sub_of_mem_critical_strip {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 := by
  have hr : (1 - s).re = 1 - s.re := by simp
  have hstrip0 : 0 < (1 - s).re := by rw [hr]; linarith
  have hstrip1 : (1 - s).re < 1 := by rw [hr]; linarith
  have hxi : RiemannScaffold.riemannXi s = 0 :=
    (riemannXi_eq_zero_iff_zeta_zero_of_mem_critical_strip h0 h1).mpr hz
  have hxi' : RiemannScaffold.riemannXi (1 - s) = 0 := by
    rw [riemannXi_functional_equation]; exact hxi
  exact (riemannXi_eq_zero_iff_zeta_zero_of_mem_critical_strip hstrip0 hstrip1).mp hxi'


theorem RiemannScaffold.riemannXi_eq_zero_of_nontrivial_zeta_zero {s : ℂ}
    (h : riemannZeta s = 0) (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) (hs1 : s ≠ 1) :
    RiemannScaffold.riemannXi s = 0 := by
  by_cases hs0 : s = 0
  · subst hs0; simp [RiemannScaffold.riemannXi]
  · rw [riemannZeta_def_of_ne_zero hs0] at h
    have hΛ : completedRiemannZeta s = 0 := by
      rcases div_eq_zero_iff.mp h with h' | h'
      · exact h'
      · exfalso
        obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h'
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · simp at hn; exact hs0 hn
        · refine htriv ⟨n - 1, ?_⟩
          have hle : (1 : ℕ) ≤ n := hpos
          rw [hn]
          push_cast [Nat.cast_sub hle]
          ring
    simp [RiemannScaffold.riemannXi, hΛ]


/-- On the half-plane of absolute convergence, `ζ` commutes with complex conjugation. -/
theorem riemannZeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) s)) = riemannZeta s := by
  have hs' : 1 < ((starRingEnd ℂ) s).re := by simpa using hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs', zeta_eq_tsum_one_div_nat_add_one_cpow hs,
    Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  have harg : ((n : ℂ) + 1).arg ≠ Real.pi := by
    have : ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.arg_ofReal_of_nonneg (by positivity)]
    exact fun h => Real.pi_ne_zero h.symm
  have hconj : (starRingEnd ℂ) ((n : ℂ) + 1) = (n : ℂ) + 1 := by
    simp
  have := Complex.conj_cpow ((n : ℂ) + 1) s harg
  rw [hconj] at this
  rw [map_div₀]
  simp only [map_one]
  rw [← this]


/-- `ζ` commutes with complex conjugation away from the pole. -/
theorem riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    riemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (riemannZeta s) := by
  set g : ℂ → ℂ := fun z => (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) z)) with hg
  have hUopen : IsOpen ({(1 : ℂ)}ᶜ) := isOpen_compl_singleton
  have hUconn : IsPreconnected ({(1 : ℂ)}ᶜ) :=
    (isConnected_compl_singleton_of_one_lt_rank (E := ℂ)
      (by simp [Complex.rank_real_complex]) 1).isPreconnected
  have hzeta : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    exact (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hgan : AnalyticOnNhd ℂ g ({(1 : ℂ)}ᶜ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    have hz' : (starRingEnd ℂ) z ≠ 1 := by
      intro h
      apply hz
      have := congrArg (starRingEnd ℂ) h
      simpa using this
    have hd : DifferentiableAt ℂ riemannZeta ((starRingEnd ℂ) z) :=
      differentiableAt_riemannZeta hz'
    have := hd.conj_conj
    rw [Complex.conj_conj] at this
    exact this.differentiableWithinAt
  have hev : riemannZeta =ᶠ[nhds (2 : ℂ)] g := by
    have hmem : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) := by
      refine (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_
      norm_num
    filter_upwards [hmem] with z hz
    exact (riemannZeta_conj_of_one_lt_re hz).symm
  have h2 : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have : (2 : ℂ).re = (1 : ℂ).re := by rw [h]
    norm_num at this
  have := hzeta.eqOn_of_preconnected_of_eventuallyEq hgan hUconn h2 hev
  have hval := this (Set.mem_compl_singleton_iff.mpr hs)
  rw [hg] at hval
  simp only at hval
  rw [hval, Complex.conj_conj]


theorem zeta_zero_quartet_of_mem_critical_strip {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : riemannZeta s = 0) :
    riemannZeta s = 0 ∧ riemannZeta (1 - s) = 0 ∧
      riemannZeta (starRingEnd ℂ s) = 0 ∧
      riemannZeta (1 - starRingEnd ℂ s) = 0 := by
  have hs1 : s ≠ 1 := by rintro rfl; simp at h1
  have hconj : riemannZeta (starRingEnd ℂ s) = 0 := by
    rw [riemannZeta_conj hs1, hz, map_zero]
  have hcre : ((starRingEnd ℂ) s).re = s.re := Complex.conj_re s
  refine ⟨hz, zeta_zero_one_sub_of_mem_critical_strip h0 h1 hz, hconj, ?_⟩
  refine zeta_zero_one_sub_of_mem_critical_strip (by rw [hcre]; exact h0)
    (by rw [hcre]; exact h1) hconj


/-- A nontrivial zero of `ζ` (i.e. one which is neither a trivial zero nor the point `s = 1`)
is a zero of `ξ`. -/
theorem riemannXi_eq_zero_of_nontrivial_zeta_zero {s : ℂ}
    (h : riemannZeta s = 0) (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) (hs1 : s ≠ 1) :
    riemannXi s = 0 := by
  by_cases hs0 : s = 0
  · subst hs0; simp [riemannXi]
  · rw [riemannZeta_def_of_ne_zero hs0] at h
    have hΛ : completedRiemannZeta s = 0 := by
      rcases div_eq_zero_iff.mp h with h' | h'
      · exact h'
      · exfalso
        obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h'
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · simp at hn; exact hs0 hn
        · refine htriv ⟨n - 1, ?_⟩
          have hle : (1 : ℕ) ≤ n := hpos
          rw [hn]
          push_cast [Nat.cast_sub hle]
          ring
    simp [riemannXi, hΛ]


/-- The archimedean factor `Gammaℝ` commutes with complex conjugation. -/
theorem Gammaℝ_conj (s : ℂ) :
    Complex.Gammaℝ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Complex.Gammaℝ s) := by
  have hpi : ((Real.pi : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact fun h => Real.pi_ne_zero h.symm
  have hcpow : ((Real.pi : ℂ)) ^ ((starRingEnd ℂ) (-s / 2))
      = (starRingEnd ℂ) (((Real.pi : ℂ)) ^ (-s / 2)) := by
    have := Complex.cpow_conj ((Real.pi : ℂ)) (-s / 2) hpi
    rwa [Complex.conj_ofReal] at this
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul, ← Complex.Gamma_conj]
  congr 1
  · rw [← hcpow]
    congr 1
    simp [map_div₀, Complex.conj_ofNat]
  · congr 1
    simp [map_div₀, Complex.conj_ofNat]


/-- On the half-plane of absolute convergence, the completed zeta `Λ` commutes with
complex conjugation. -/
theorem completedRiemannZeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (completedRiemannZeta s) := by
  have hs' : 1 < ((starRingEnd ℂ) s).re := by simpa using hs
  have key : ∀ z : ℂ, 1 < z.re →
      completedRiemannZeta z = riemannZeta z * Complex.Gammaℝ z := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h; rw [h] at hz; simp at hz; linarith
    have hΓ : Complex.Gammaℝ z ≠ 0 := by
      intro h
      obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
      have : z.re = -(2 * (n : ℝ)) := by rw [hn]; simp
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [this] at hz
      linarith
    rw [riemannZeta_def_of_ne_zero hz0, div_mul_cancel₀ _ hΓ]
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs
  rw [key _ hs', key _ hs, riemannZeta_conj hs1, Gammaℝ_conj, ← map_mul]


/-- The entire function `Λ₀` commutes with complex conjugation. -/
theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (completedRiemannZeta₀ s) := by
  set g : ℂ → ℂ := fun z => (starRingEnd ℂ) (completedRiemannZeta₀ ((starRingEnd ℂ) z)) with hg
  have hf : AnalyticOnNhd ℂ completedRiemannZeta₀ Set.univ :=
    (differentiable_completedZeta₀.differentiableOn).analyticOnNhd isOpen_univ
  have hgan : AnalyticOnNhd ℂ g Set.univ := by
    refine DifferentiableOn.analyticOnNhd (fun z _ => ?_) isOpen_univ
    have hd : DifferentiableAt ℂ completedRiemannZeta₀ ((starRingEnd ℂ) z) :=
      differentiable_completedZeta₀ _
    have := hd.conj_conj
    rw [Complex.conj_conj] at this
    exact this.differentiableWithinAt
  have hev : completedRiemannZeta₀ =ᶠ[nhds (2 : ℂ)] g := by
    have hmem : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) := by
      refine (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_
      norm_num
    filter_upwards [hmem] with z hz
    have hz' : 1 < ((starRingEnd ℂ) z).re := by simpa using hz
    have hΛ : completedRiemannZeta ((starRingEnd ℂ) z)
        = (starRingEnd ℂ) (completedRiemannZeta z) :=
      completedRiemannZeta_conj_of_one_lt_re hz
    have hz0 : z ≠ 0 := by
      intro h; rw [h] at hz; simp at hz; linarith
    have hz1 : (1 : ℂ) - z ≠ 0 := by
      intro h
      have : z = 1 := by linear_combination -h
      rw [this] at hz; simp at hz
    have e1 : completedRiemannZeta₀ z
        = completedRiemannZeta z + 1 / z + 1 / (1 - z) := by
      rw [completedRiemannZeta_eq]; ring
    have e2 : completedRiemannZeta₀ ((starRingEnd ℂ) z)
        = completedRiemannZeta ((starRingEnd ℂ) z) + 1 / ((starRingEnd ℂ) z)
          + 1 / (1 - (starRingEnd ℂ) z) := by
      rw [completedRiemannZeta_eq]; ring
    show completedRiemannZeta₀ z = (starRingEnd ℂ) (completedRiemannZeta₀ ((starRingEnd ℂ) z))
    rw [e2, e1, hΛ]
    simp only [map_add, map_div₀, map_one, map_sub, Complex.conj_conj]
  have := hf.eqOn_of_preconnected_of_eventuallyEq hgan isPreconnected_univ (Set.mem_univ 2) hev
  have hval := this (Set.mem_univ s)
  rw [hg] at hval
  simp only at hval
  rw [hval, Complex.conj_conj]


/-- The completed zeta function `Λ` commutes with complex conjugation. -/
theorem completedRiemannZeta_conj (s : ℂ) :
    completedRiemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (completedRiemannZeta s) := by
  rw [completedRiemannZeta_eq, completedRiemannZeta_eq, completedRiemannZeta₀_conj]
  simp only [map_sub, map_div₀, map_one]


/-- **The ξ-function commutes with complex conjugation.** -/
theorem riemannXi_conj (s : ℂ) :
    riemannXi (starRingEnd ℂ s) = starRingEnd ℂ (riemannXi s) := by
  rw [riemannXi_apply, riemannXi_apply, completedRiemannZeta_conj]
  simp only [map_mul, map_sub, map_one]


/-- **The ξ zero set is stable under `s ↦ 1 - s` and under complex conjugation
(UNCONDITIONAL).** -/
theorem riemannXi_zero_reflect {s : ℂ} (hs : riemannXi s = 0) :
    riemannXi (1 - s) = 0 ∧ riemannXi (starRingEnd ℂ s) = 0 := by
  refine ⟨by rw [riemannXi_functional_equation]; exact hs, ?_⟩
  by_cases hreal : (starRingEnd ℂ) s = s
  · rw [hreal]; exact hs
  by_cases hs0 : s = 0
  · exact absurd (by rw [hs0]; simp) hreal
  by_cases hs1 : s = 1
  · exact absurd (by rw [hs1]; simp) hreal
  have hz : riemannZeta s = 0 := zeta_zero_of_riemannXi_zero hs hs0 hs1
  have hzc : riemannZeta ((starRingEnd ℂ) s) = 0 := by
    rw [riemannZeta_conj hs1, hz, map_zero]
  refine Brockian.RiemannScaffold.riemannXi_eq_zero_of_nontrivial_zeta_zero hzc ?_ ?_
  · rintro ⟨n, hn⟩
    refine absurd ?_ hreal
    have hsval : s = -2 * ((n : ℂ) + 1) := by
      have h' := congrArg (starRingEnd ℂ) hn
      rw [Complex.conj_conj] at h'
      rw [h']
      simp [Complex.ext_iff]
    rw [hn, hsval]
  · intro h
    exact hs1 (by
      have := congrArg (starRingEnd ℂ) h
      simpa using this)


/-- **The Γ-factor is nonvanishing away from `0` and the trivial-zero lattice.**
`Gammaℝ s = π^(-s/2) Γ(s/2)`; the `cpow` factor is never zero, and `Γ(s/2) ≠ 0`
exactly when `s/2 ∉ {0, -1, -2, …}`, i.e. `s ∉ {0, -2, -4, …}`.  We exclude `s = 0`
and the trivial-zero lattice `{-2(n+1) : n ∈ ℕ}` and get `Gammaℝ s ≠ 0`. -/
theorem Gammaℝ_ne_zero_of_nontrivial {s : ℂ} (hs0 : s ≠ 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) : s.Gammaℝ ≠ 0 := by
  rw [Complex.Gammaℝ_def]
  refine mul_ne_zero ?_ ?_
  · rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (by exact_mod_cast Real.pi_ne_zero)
  · apply Complex.Gamma_ne_zero
    intro m hm
    -- hm : s / 2 = -↑m  ⇒  s = -2 * m
    have hs : s = -2 * (m : ℂ) := by linear_combination 2 * hm
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      simp only [Nat.cast_zero, mul_zero] at hs
      exact hs0 hs
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
      exact htriv ⟨k, by push_cast at hs ⊢; linear_combination hs⟩


/-- **The ξ-bridge (UNCONDITIONAL).**  If every zero of `ξ` other than the two
lattice artifacts `s = 0, 1` (which come from the explicit `s (s-1)` factor over
`ℂ`, not from `Λ`) lies on the critical line, then the Riemann Hypothesis holds
as Mathlib states it.

The hypothesis is the honest ξ-form of RH: it is NOT assumed, and it is not
vacuous — it is exactly the (open) assertion that the nontrivial zeros lie on the
line.  The implication does real work through
`riemannXi_eq_zero_of_nontrivial_zeta_zero`. -/
theorem RiemannHypothesis_of_forall_xi_zero
    (h : ∀ s : ℂ, riemannXi s = 0 → s ≠ 0 → s ≠ 1 → s.re = 1 / 2) :
    RiemannHypothesis := by
  intro s hz htriv hs1
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hz
    norm_num at hz
  exact h s (riemannXi_eq_zero_of_nontrivial_zeta_zero hz htriv hs1) hs0 hs1

/-! ## Part 2 — The Brockian conditional chain (CONDITIONAL, rung OPEN)

This part formalizes the *Hilbert–Pólya shape* of the Brockian program: a
densely-defined **symmetric** (formal self-adjoint) operator on a Hilbert space
whose point spectrum realizes the nontrivial zeros through `t = -i(s - 1/2)`.
The implication `BrockianSystem → RiemannHypothesis` is proved for real; but
**no `BrockianSystem` is constructed** — constructing one is RH-strength
(Gate-0, see the note at the end). -/


/-- **Symmetric operators have real eigenvalues (UNCONDITIONAL).**  For a formal
self-adjoint (symmetric) `LinearPMap` `T`, any eigenvalue `μ` attached to a
nonzero eigenvector is real.  Proof: `⟪T v, v⟫ = ⟪v, T v⟫` (symmetry) becomes
`conj μ · ⟪v,v⟫ = μ · ⟪v,v⟫`; cancel `⟪v,v⟫ ≠ 0` to get `conj μ = μ`.

This is the theorem that *grounds* the `spectrum_real` obligation of a
`BrockianSystem`: a genuine symmetric operator discharges it on its point
spectrum.  Reality is therefore not an ex-falso gadget — it is the real spectral
content of symmetry. -/
theorem symmetric_eigenvalue_im_zero {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {T : H →ₗ.[ℂ] H} (hsymm : T.IsFormalAdjoint T)
    {μ : ℂ} {v : T.domain} (hv : (v : H) ≠ 0)
    (heig : (T v : H) = μ • (v : H)) : μ.im = 0 := by
  have hkey := hsymm v v
  rw [heig, inner_smul_left, inner_smul_right] at hkey
  have hvv : inner ℂ (v : H) (v : H) ≠ 0 := inner_self_ne_zero.mpr hv
  have hconj : (starRingEnd ℂ) μ = μ := mul_right_cancel₀ hvv hkey
  exact Complex.conj_eq_iff_im.mp hconj

/-- **A `BrockianSystem`** — the Hilbert–Pólya operator-theoretic hypothesis, made
into an honest bundle of obligations over a Hilbert space `H`.

Fields:
* `T` — a **densely-defined, unbounded** operator, modelled as a partial linear
  map `H →ₗ.[ℂ] H` (a `LinearPMap`, *not* a bounded `H →L[ℂ] H`; the bounded
  route is spectrally vacuous for this problem).
* `dense_domain` — `T` is densely defined.
* `symm` — `T` is **symmetric** (formal self-adjoint, `T.IsFormalAdjoint T`).
* `spectrum_real` — the **explicit spectral-reality obligation**: every eigenvalue
  of `T` (nonzero eigenvector) is real.  (Grounded by `symm` via
  `symmetric_eigenvalue_im_zero`; carried as an explicit field so the obligation
  is visible.)
* `eigen_of_zero` — the **zeros ↔ spectrum** correspondence: every nontrivial
  zero `s` of `ζ` is realized as an eigenvalue `t = -i(s - 1/2)` of `T`.

No such system is exhibited here; see the Gate-0 note. -/
structure BrockianSystem (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- the densely-defined unbounded operator (partial linear map, not bounded). -/
  T : H →ₗ.[ℂ] H
  /-- `T` is densely defined. -/
  dense_domain : Dense (T.domain : Set H)
  /-- `T` is symmetric (formal self-adjoint). -/
  symm : T.IsFormalAdjoint T
  /-- **Spectral-reality obligation**: eigenvalues of `T` are real. -/
  spectrum_real : ∀ (μ : ℂ) (v : T.domain),
    (v : H) ≠ 0 → (T v : H) = μ • (v : H) → μ.im = 0
  /-- **Zeros ↔ spectrum**: each nontrivial `ζ`-zero `s` is an eigenvalue
  `t = -i(s - 1/2)` of `T`, on a nonzero eigenvector. -/
  eigen_of_zero : ∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) →
    s ≠ 1 → ∃ v : T.domain, (v : H) ≠ 0 ∧
      (T v : H) = (-Complex.I * (s - 1 / 2)) • (v : H)


/-- **`RH_of_BrockianSystem` — the Brockian conditional (CONDITIONAL, rung OPEN).**
If a `BrockianSystem` exists on some Hilbert space, then the Riemann Hypothesis
holds (as Mathlib states it).

The implication does genuine work: for a nontrivial zero `s`, the correspondence
`eigen_of_zero` produces an eigenvector at eigenvalue `t = -i(s - 1/2)`;
`spectrum_real` forces `t` real, i.e. `t.im = 0`; and the complex algebra of
`t = -i(s - 1/2)` turns `t.im = 0` into `s.re = 1/2`.

This is a *conditional* result.  `BrockianSystem` is **not shown instantiable**
(Gate-0). -/
theorem RH_of_BrockianSystem {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : BrockianSystem H) : RiemannHypothesis := by
  intro s hz htriv hs1
  obtain ⟨v, hv, heig⟩ := B.eigen_of_zero s hz htriv hs1
  -- the eigenvalue realizing the zero
  have him : (-Complex.I * (s - 1 / 2)).im = 0 := B.spectrum_real _ v hv heig
  -- turn `t = -i(s - 1/2)`, `t.im = 0` into `Re s = 1/2`
  have h2 : ((1 : ℂ) / 2).im = 0 := by simp
  have h3 : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.sub_re, Complex.sub_im, h2, h3] at him
  linarith

/-! ### Gate-0 note (honesty register)

`BrockianSystem` is **NOT shown instantiable** in this file: no term of type
`BrockianSystem H` is constructed for any `H`.  This is deliberate and is the
crux of the honesty contract — exhibiting such a symmetric operator whose point
spectrum encodes the nontrivial zeros *is itself of Riemann-Hypothesis strength*
(indeed `RH_of_BrockianSystem` shows any instance would prove RH outright).

Concretely, the contrapositive of `RH_of_BrockianSystem` says: **if RH is false,
then no Hilbert space carries a `BrockianSystem`.**  So the type is at least as
hard to inhabit as RH is to prove.  We therefore leave it as an OPEN schema and
claim only the *conditional* `RH_of_BrockianSystem` and the *unconditional*
ξ-bridge of Part 1.  RH itself is **not** claimed. -/


/-- **`ξ` is nonvanishing on the half-plane of absolute convergence `Re s > 1`.**
There `s ≠ 0`, `s ≠ 1`, and `Λ(s) = ζ(s) · Gammaℝ s ≠ 0` since `ζ(s) ≠ 0`. -/
theorem riemannXi_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannXi s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have hEq : s = 1 := by linear_combination h
    rw [hEq] at hs
    simp at hs
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hΛ : completedRiemannZeta s ≠ 0 := by
    intro h
    exact hz (by rw [riemannZeta_def_of_ne_zero hs0, h, zero_div])
  rw [riemannXi_apply]
  exact mul_ne_zero (mul_ne_zero hs0 hs1) hΛ


/-- **`ξ` has no zeros in the left half-plane `Re s < 0` (UNCONDITIONAL).**

Proof: for `Re s < 0` the reflected point `z = 1 - s` satisfies `Re z > 1`, where
`ζ(z) ≠ 0` (Mathlib's `riemannZeta_ne_zero_of_one_lt_re`), hence `Λ(z) ≠ 0` since
`ζ(z) = Λ(z) / Gammaℝ z`.  The functional equation `Λ(1 - s) = Λ(s)` transports
this to `Λ(s) ≠ 0`, and the polynomial factor `s (s - 1)` is nonzero because
`s ≠ 0` and `s ≠ 1`. -/
theorem riemannXi_ne_zero_of_re_lt_zero {s : ℂ} (hs : s.re < 0) :
    riemannXi s ≠ 0 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have h1 : s = 1 := by linear_combination h
    rw [h1] at hs; simp at hs; linarith
  set z := 1 - s with hzdef
  have hzre : 1 < z.re := by simp [hzdef]; linarith
  have hz0 : z ≠ 0 := by intro h; rw [h] at hzre; simp at hzre; linarith
  have hzeta : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hzre
  have hΛz : completedRiemannZeta z ≠ 0 := by
    rw [riemannZeta_def_of_ne_zero hz0] at hzeta
    exact fun h => hzeta (by rw [h, zero_div])
  have hΛ : completedRiemannZeta s ≠ 0 := by
    rw [← completedRiemannZeta_one_sub s]
    exact hΛz
  rw [riemannXi_apply]
  exact mul_ne_zero (mul_ne_zero hs0 hs1) hΛ


/-- **`ξ` is real on the critical line (UNCONDITIONAL).**  If `Re s = 1/2`, then
`conj s = 1 - s`, so combining the functional equation `ξ(1-s) = ξ(s)` with the
conjugation symmetry `ξ(conj s) = conj (ξ s)` gives `conj (ξ s) = ξ s`, i.e. `ξ s`
is real. -/
theorem riemannXi_im_eq_zero_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) :
    (riemannXi s).im = 0 := by
  have hconj : (starRingEnd ℂ) s = 1 - s := by
    refine Complex.ext ?_ ?_
    · simp [hs]; norm_num
    · simp
  have h1 : riemannXi ((starRingEnd ℂ) s) = riemannXi s := by
    rw [hconj, riemannXi_functional_equation]
  rw [riemannXi_conj] at h1
  exact Complex.conj_eq_iff_im.mp h1


/-- **`ξ` is fixed by complex conjugation on the critical line (UNCONDITIONAL).**
Immediate from `riemannXi_im_eq_zero_of_re_eq_half`: a complex number with
vanishing imaginary part is its own conjugate. -/
theorem riemannXi_conj_self_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) :
    (starRingEnd ℂ) (riemannXi s) = riemannXi s :=
  Complex.conj_eq_iff_im.mpr (riemannXi_im_eq_zero_of_re_eq_half hs)


/-- **Every zero of `ξ` lies in the closed critical strip `0 ≤ Re s ≤ 1`
(UNCONDITIONAL).**  Immediate from the two half-plane nonvanishing results. -/
theorem riemannXi_zero_mem_critical_strip {s : ℂ} (hs : riemannXi s = 0) :
    0 ≤ s.re ∧ s.re ≤ 1 := by
  constructor
  · by_contra h
    exact riemannXi_ne_zero_of_re_lt_zero (not_le.mp h) hs
  · by_contra h
    exact riemannXi_ne_zero_of_one_lt_re (not_le.mp h) hs

/-- **The zero set of `ξ` comes in quartets (UNCONDITIONAL).**  If `ξ(s) = 0` then
`ξ` also vanishes at `1 - s`, at `conj s`, at `1 - conj s`, and at `conj (1 - s)`.
Obtained by iterating `riemannXi_zero_reflect`, which supplies both the reflection
`s ↦ 1 - s` (functional equation) and the conjugation symmetry. -/
theorem riemannXi_zeroSet_quartet {s : ℂ} (hs : riemannXi s = 0) :
    riemannXi (1 - s) = 0 ∧ riemannXi ((starRingEnd ℂ) s) = 0 ∧
      riemannXi (1 - (starRingEnd ℂ) s) = 0 ∧ riemannXi ((starRingEnd ℂ) (1 - s)) = 0 := by
  obtain ⟨h1, h2⟩ := riemannXi_zero_reflect hs
  obtain ⟨h3, -⟩ := riemannXi_zero_reflect h2
  obtain ⟨-, h4⟩ := riemannXi_zero_reflect h1
  exact ⟨h1, h2, h3, h4⟩

end Brockian.XiFunctionalEquation

import Mathlib

namespace Brockian.RiemannScaffold

open Complex

/-! ## Part 1 — The ξ-bridge (UNCONDITIONAL, genuinely proved) -/

/-- **The Riemann ξ-function** in the classical normalization
`ξ(s) = s (s-1) Λ(s)`, where `Λ = completedRiemannZeta` is Mathlib's completed
zeta `π^(-s/2) Γ(s/2) ζ(s)`.  The `s (s-1)` factor is the classical one that (over
`ℂ`) cancels the simple poles of `Λ` at `s = 0, 1`. -/
noncomputable def riemannXi (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta s

/-- **The Γ-factor is nonvanishing away from `0` and the trivial-zero lattice.**
`Gammaℝ s = π^(-s/2) Γ(s/2)`; the `cpow` factor is never zero, and `Γ(s/2) ≠ 0`
exactly when `s/2 ∉ {0, -1, -2, …}`, i.e. `s ∉ {0, -2, -4, …}`.  We exclude `s = 0`
and the trivial-zero lattice `{-2(n+1) : n ∈ ℕ}` and get `Gammaℝ s ≠ 0`. -/
theorem Gammaℝ_ne_zero_of_nontrivial {s : ℂ} (hs0 : s ≠ 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) : s.Gammaℝ ≠ 0 := by
  rw [Complex.Gammaℝ_def]
  refine mul_ne_zero ?_ ?_
  · rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (by exact_mod_cast Real.pi_ne_zero)
  · apply Complex.Gamma_ne_zero
    intro m hm
    -- hm : s / 2 = -↑m  ⇒  s = -2 * m
    have hs : s = -2 * (m : ℂ) := by linear_combination 2 * hm
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      simp only [Nat.cast_zero, mul_zero] at hs
      exact hs0 hs
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
      exact htriv ⟨k, by push_cast at hs ⊢; linear_combination hs⟩

/-- **Nontrivial ζ-zero ⇒ ξ-zero (UNCONDITIONAL).**  If `ζ(s) = 0` at a point that
is not the trivial-zero lattice and not `s = 1`, then `ξ(s) = 0`.  The real work:
`s ≠ 0` (since `ζ(0) = -1/2`), the Γ-factor is nonvanishing there, and
`ζ = Λ / Gammaℝ` forces `Λ(s) = 0`, hence `ξ(s) = s (s-1) · 0 = 0`. -/
theorem riemannXi_eq_zero_of_nontrivial_zeta_zero {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (_hs1 : s ≠ 1) : riemannXi s = 0 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hz
    norm_num at hz
  have hΓ : s.Gammaℝ ≠ 0 := Gammaℝ_ne_zero_of_nontrivial hs0 htriv
  have hΛ : completedRiemannZeta s = 0 := by
    have hdef : riemannZeta s = completedRiemannZeta s / s.Gammaℝ :=
      riemannZeta_def_of_ne_zero hs0
    rw [hz] at hdef
    exact (div_eq_zero_iff.mp hdef.symm).resolve_right hΓ
  unfold riemannXi
  rw [hΛ]
  ring

/-- **The ξ-bridge (UNCONDITIONAL).**  If every zero of `ξ` other than the two
lattice artifacts `s = 0, 1` (which come from the explicit `s (s-1)` factor over
`ℂ`, not from `Λ`) lies on the critical line, then the Riemann Hypothesis holds
as Mathlib states it.

The hypothesis is the honest ξ-form of RH: it is NOT assumed, and it is not
vacuous — it is exactly the (open) assertion that the nontrivial zeros lie on the
line.  The implication does real work through
`riemannXi_eq_zero_of_nontrivial_zeta_zero`. -/
theorem RiemannHypothesis_of_forall_xi_zero
    (h : ∀ s : ℂ, riemannXi s = 0 → s ≠ 0 → s ≠ 1 → s.re = 1 / 2) :
    RiemannHypothesis := by
  intro s hz htriv hs1
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hz
    norm_num at hz
  exact h s (riemannXi_eq_zero_of_nontrivial_zeta_zero hz htriv hs1) hs0 hs1

/-! ## Part 2 — The Brockian conditional chain (CONDITIONAL, rung OPEN)

This part formalizes the *Hilbert–Pólya shape* of the Brockian program: a
densely-defined **symmetric** (formal self-adjoint) operator on a Hilbert space
whose point spectrum realizes the nontrivial zeros through `t = -i(s - 1/2)`.
The implication `BrockianSystem → RiemannHypothesis` is proved for real; but
**no `BrockianSystem` is constructed** — constructing one is RH-strength
(Gate-0, see the note at the end). -/

/-- **Symmetric operators have real eigenvalues (UNCONDITIONAL).**  For a formal
self-adjoint (symmetric) `LinearPMap` `T`, any eigenvalue `μ` attached to a
nonzero eigenvector is real.  Proof: `⟪T v, v⟫ = ⟪v, T v⟫` (symmetry) becomes
`conj μ · ⟪v,v⟫ = μ · ⟪v,v⟫`; cancel `⟪v,v⟫ ≠ 0` to get `conj μ = μ`.

This is the theorem that *grounds* the `spectrum_real` obligation of a
`BrockianSystem`: a genuine symmetric operator discharges it on its point
spectrum.  Reality is therefore not an ex-falso gadget — it is the real spectral
content of symmetry. -/
theorem symmetric_eigenvalue_im_zero {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {T : H →ₗ.[ℂ] H} (hsymm : T.IsFormalAdjoint T)
    {μ : ℂ} {v : T.domain} (hv : (v : H) ≠ 0)
    (heig : (T v : H) = μ • (v : H)) : μ.im = 0 := by
  have hkey := hsymm v v
  rw [heig, inner_smul_left, inner_smul_right] at hkey
  have hvv : inner ℂ (v : H) (v : H) ≠ 0 := inner_self_ne_zero.mpr hv
  have hconj : (starRingEnd ℂ) μ = μ := mul_right_cancel₀ hvv hkey
  exact Complex.conj_eq_iff_im.mp hconj

/-- **A `BrockianSystem`** — the Hilbert–Pólya operator-theoretic hypothesis, made
into an honest bundle of obligations over a Hilbert space `H`.

Fields:
* `T` — a **densely-defined, unbounded** operator, modelled as a partial linear
  map `H →ₗ.[ℂ] H` (a `LinearPMap`, *not* a bounded `H →L[ℂ] H`; the bounded
  route is spectrally vacuous for this problem).
* `dense_domain` — `T` is densely defined.
* `symm` — `T` is **symmetric** (formal self-adjoint, `T.IsFormalAdjoint T`).
* `spectrum_real` — the **explicit spectral-reality obligation**: every eigenvalue
  of `T` (nonzero eigenvector) is real.  (Grounded by `symm` via
  `symmetric_eigenvalue_im_zero`; carried as an explicit field so the obligation
  is visible.)
* `eigen_of_zero` — the **zeros ↔ spectrum** correspondence: every nontrivial
  zero `s` of `ζ` is realized as an eigenvalue `t = -i(s - 1/2)` of `T`.

No such system is exhibited here; see the Gate-0 note. -/
structure BrockianSystem (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- the densely-defined unbounded operator (partial linear map, not bounded). -/
  T : H →ₗ.[ℂ] H
  /-- `T` is densely defined. -/
  dense_domain : Dense (T.domain : Set H)
  /-- `T` is symmetric (formal self-adjoint). -/
  symm : T.IsFormalAdjoint T
  /-- **Spectral-reality obligation**: eigenvalues of `T` are real. -/
  spectrum_real : ∀ (μ : ℂ) (v : T.domain),
    (v : H) ≠ 0 → (T v : H) = μ • (v : H) → μ.im = 0
  /-- **Zeros ↔ spectrum**: each nontrivial `ζ`-zero `s` is an eigenvalue
  `t = -i(s - 1/2)` of `T`, on a nonzero eigenvector. -/
  eigen_of_zero : ∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) →
    s ≠ 1 → ∃ v : T.domain, (v : H) ≠ 0 ∧
      (T v : H) = (-Complex.I * (s - 1 / 2)) • (v : H)

/-- **`RH_of_BrockianSystem` — the Brockian conditional (CONDITIONAL, rung OPEN).**
If a `BrockianSystem` exists on some Hilbert space, then the Riemann Hypothesis
holds (as Mathlib states it).

The implication does genuine work: for a nontrivial zero `s`, the correspondence
`eigen_of_zero` produces an eigenvector at eigenvalue `t = -i(s - 1/2)`;
`spectrum_real` forces `t` real, i.e. `t.im = 0`; and the complex algebra of
`t = -i(s - 1/2)` turns `t.im = 0` into `s.re = 1/2`.

This is a *conditional* result.  `BrockianSystem` is **not shown instantiable**
(Gate-0). -/
theorem RH_of_BrockianSystem {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : BrockianSystem H) : RiemannHypothesis := by
  intro s hz htriv hs1
  obtain ⟨v, hv, heig⟩ := B.eigen_of_zero s hz htriv hs1
  -- the eigenvalue realizing the zero
  have him : (-Complex.I * (s - 1 / 2)).im = 0 := B.spectrum_real _ v hv heig
  -- turn `t = -i(s - 1/2)`, `t.im = 0` into `Re s = 1/2`
  have h2 : ((1 : ℂ) / 2).im = 0 := by simp
  have h3 : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.sub_re, Complex.sub_im, h2, h3] at him
  linarith

/-! ### Gate-0 note (honesty register)

`BrockianSystem` is **NOT shown instantiable** in this file: no term of type
`BrockianSystem H` is constructed for any `H`.  This is deliberate and is the
crux of the honesty contract — exhibiting such a symmetric operator whose point
spectrum encodes the nontrivial zeros *is itself of Riemann-Hypothesis strength*
(indeed `RH_of_BrockianSystem` shows any instance would prove RH outright).

Concretely, the contrapositive of `RH_of_BrockianSystem` says: **if RH is false,
then no Hilbert space carries a `BrockianSystem`.**  So the type is at least as
hard to inhabit as RH is to prove.  We therefore leave it as an OPEN schema and
claim only the *conditional* `RH_of_BrockianSystem` and the *unconditional*
ξ-bridge of Part 1.  RH itself is **not** claimed. -/

end Brockian.RiemannScaffold

