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

import Mathlib

/-!
# Reduction of equidistribution to bounded–variation test functions

Let `x : ℕ → ℝ` be a sequence.  We say that the *bounded variation averages of `x`
converge* if for every real function `f` of bounded variation on `[0,1]` the Birkhoff-type
averages of `f` along the fractional parts of `x` converge to `∫_0^1 f`.

The main result, `Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform`,
says that this hypothesis on `x` forces `x` to be uniformly distributed mod `1`:
the proportion of the first `N` fractional parts falling into a subinterval `[a,b) ⊆ [0,1]`
tends to its length `b - a`.

The point of the reduction is that indicator functions of intervals are of bounded
variation; this is proved here from scratch (`Brockian.EquidistributionBVReduction.boundedVariationOn_indicator_Ico`),
via a subadditivity estimate for `eVariationOn` and the fact that the two half-line
indicators `1_{[a,∞)}` and `1_{[b,∞)}` are monotone.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- A sequence `x : ℕ → ℝ` is *uniformly distributed mod 1* if for every subinterval
`[a,b) ⊆ [0,1]`, the proportion of `n < N` with `Int.fract (x n) ∈ [a, b)` tends to `b - a`. -/

theorem eVariationOn_sub_le {α : Type*} [LinearOrder α] (f g : α → ℝ) (s : Set α) :
    eVariationOn (fun t => f t - g t) s ≤ eVariationOn f s + eVariationOn g s := by
  refine iSup_le ?_
  rintro ⟨n, ⟨u, hu, us⟩⟩
  have key : ∀ i : ℕ,
      edist (f (u (i + 1)) - g (u (i + 1))) (f (u i) - g (u i)) ≤
        edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i)) := by
    intro i
    simp only [edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc |f (u (i + 1)) - g (u (i + 1)) - (f (u i) - g (u i))|
        = |(f (u (i + 1)) - f (u i)) - (g (u (i + 1)) - g (u i))| := by ring_nf
      _ ≤ |f (u (i + 1)) - f (u i)| + |g (u (i + 1)) - g (u i)| := abs_sub _ _
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) - g (u (i + 1))) (f (u i) - g (u i))
      ≤ ∑ i ∈ Finset.range n,
          (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
        Finset.sum_le_sum fun i _ => key i
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))
          + ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le f n hu us) (eVariationOn.sum_le g n hu us)

/-- The indicator of a half line `[c, ∞)` has bounded variation on `[0,1]`. -/
