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

lemma eqOn_zero_of_vanishes_on_reals {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f ({0}ᶜ : Set ℂ))
    (hzero : ∀ t : ℝ, t ≠ 0 → f (t : ℂ) = 0) :
    Set.EqOn f 0 ({0}ᶜ : Set ℂ) := by
  have h1 : (1 : ℂ) ∈ ({0}ᶜ : Set ℂ) := by simp
  refine hf.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_compl_zero h1 ?_
  -- the reals near `1` are all nonzero, so `f` vanishes frequently near `1`
  have hcoe : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin 1 {(1 : ℝ)}ᶜ)
      (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto 1).comp nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa [Complex.ofReal_eq_one] using ht
  have hfreq : ∃ᶠ t : ℝ in nhdsWithin 1 {(1 : ℝ)}ᶜ, f (t : ℂ) = 0 := by
    have hev : ∀ᶠ t : ℝ in nhdsWithin 1 {(1 : ℝ)}ᶜ, f (t : ℂ) = 0 := by
      have : ∀ᶠ t : ℝ in nhds (1 : ℝ), t ≠ 0 := by
        have : ∀ᶠ t : ℝ in nhds (1 : ℝ), (0 : ℝ) < t :=
          eventually_gt_nhds (by norm_num)
        filter_upwards [this] with t ht using ne_of_gt ht
      filter_upwards [nhdsWithin_le_nhds this] with t ht using hzero t ht
    exact hev.frequently
  exact hcoe.frequently hfreq

/-! ## The spin–statistics theorem -/

/-- **Spin–statistics connection.**

For a relativistic quantum field satisfying the Wightman hypotheses packaged in
`Frontier.RelativisticQuantumField` — microcausality at spacelike separation,
Lorentz covariance in the Bargmann–Hall–Wightman form, analyticity of the
Wightman function, and nontriviality — the statistics sign is determined by the
spin:

`stat = (-1) ^ (2j)`,

i.e. fields of integer spin obey Bose statistics and fields of half-integer spin
obey Fermi statistics.  The wrong pairing is impossible: it forces the two-point
function to vanish at all spacelike separations, hence — by analytic
continuation — identically, so that the field is trivial. -/
