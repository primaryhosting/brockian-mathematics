import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Frontier

open Set

/-!
## Quadratic-like maps

Following Douady–Hubbard and McMullen (*Complex Dynamics and Renormalization*),
a **quadratic-like map** is a holomorphic proper degree-two branched covering
`f : V → U` between topological disks with `V ⋐ U`, whose unique critical point we
normalise to be `0`.

The structure below records the data and the properties that are used in the
statements proved here: `V ⊆ U` open subsets of `ℂ`, `f` analytic on a neighbourhood
of each point of `V`, `f` maps `V` into `U` and *onto* `U` (properness/surjectivity),
every fibre over `U` has at most two points (degree `≤ 2`), and `0 ∈ V` is a
critical point of `f`.
-/

/-- A quadratic-like map, presented as the data of the two domains `V ⊆ U ⊆ ℂ` and the
holomorphic map `f : V → U`, which is surjective, has fibres of cardinality at most two
and has a critical point at the origin. -/
structure QuadraticLike where
  /-- The map. -/
  f : ℂ → ℂ
  /-- The target (range) disk. -/
  U : Set ℂ
  /-- The source disk, compactly contained in `U` in the classical definition. -/
  V : Set ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  subset_UV : V ⊆ U
  mapsTo : Set.MapsTo f V U
  surjOn : U ⊆ f '' V
  analytic : AnalyticOnNhd ℂ f V
  crit_mem : (0 : ℂ) ∈ V
  deriv_crit : deriv f 0 = 0
  fiber_encard_le_two : ∀ w ∈ U, {z ∈ V | f z = w}.encard ≤ 2

/-- `R` is a **renormalization of period `n`** of the quadratic-like map `Q`: `R` is itself
a quadratic-like map, its underlying map is the `n`-th iterate of `Q`, and its domains are
contained in those of `Q`.  (This is the combinatorial skeleton of McMullen's definition:
`Q.f^[n] : R.V → R.U` is again quadratic-like around the critical point.) -/

theorem no_quadraticLike_pow_four (R : QuadraticLike) (hR : R.f = fun z : ℂ => z ^ 4) :
    False := by
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.mp R.isOpen_V 0 R.crit_mem
  set t : ℂ := ((e / 2 : ℝ) : ℂ) with ht_def
  have hnorm : ‖t‖ = e / 2 := by
    rw [ht_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    linarith
  have hmemV : ∀ u : ℂ, ‖u‖ = e / 2 → u ∈ R.V := by
    intro u hu
    refine hball ?_
    simp only [Metric.mem_ball, dist_zero_right, hu]
    linarith
  have htV : t ∈ R.V := hmemV t hnorm
  have hmtV : -t ∈ R.V := hmemV (-t) (by rw [norm_neg]; exact hnorm)
  have hitV : Complex.I * t ∈ R.V := hmemV _ (by simp [hnorm])
  have hwU : R.f t ∈ R.U := R.mapsTo htV
  have hsub : ({t, -t, Complex.I * t} : Set ℂ) ⊆ {z ∈ R.V | R.f z = R.f t} := by
    rintro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨htV, rfl⟩
    · refine ⟨hmtV, ?_⟩
      rw [hR]; ring
    · refine ⟨hitV, ?_⟩
      rw [hR]
      simp only [mul_pow, Complex.I_pow_four, one_mul]
  have h1 : t ≠ -t := by
    intro h; exact ht0 (by linear_combination h / 2)
  have h2 : t ≠ Complex.I * t := by
    intro h
    have hz : (1 - Complex.I) * t = 0 := by linear_combination h
    rcases mul_eq_zero.mp hz with h' | h'
    · have : Complex.I = 1 := by linear_combination -h'
      simp [Complex.ext_iff] at this
    · exact ht0 h'
  have h3 : -t ≠ Complex.I * t := by
    intro h
    have hz : (1 + Complex.I) * t = 0 := by linear_combination -h
    rcases mul_eq_zero.mp hz with h' | h'
    · have : Complex.I = -1 := by linear_combination h'
      simp [Complex.ext_iff] at this
    · exact ht0 h'
  have hcard : ({t, -t, Complex.I * t} : Set ℂ).encard = 3 := by
    rw [Set.encard_insert_of_notMem (by simp [h1, h2]), Set.encard_pair h3]
    rfl
  have hle : (3 : ℕ∞) ≤ 2 := by
    calc (3 : ℕ∞) = ({t, -t, Complex.I * t} : Set ℂ).encard := hcard.symm
      _ ≤ {z ∈ R.V | R.f z = R.f t}.encard := Set.encard_le_encard hsub
      _ ≤ 2 := R.fiber_encard_le_two _ hwU
  norm_num at hle

