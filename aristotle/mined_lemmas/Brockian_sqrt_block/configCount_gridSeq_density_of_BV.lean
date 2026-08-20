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

import Brockian.EquidistributionBVReduction

/-!
# Existence of an equidistributed sequence

This file exhibits an explicit sequence which is equidistributed mod one in the sense of
`Brockian.EquidistributionBVReduction.Equidistributed`, so that the hypotheses of
`Brockian.EquidistributionBVReduction.configCount_density_of_BV` are satisfiable.

The sequence is the concatenation of the uniform grids of odd sizes: the `k`-th block consists
of the `2k+1` points `0/(2k+1), 1/(2k+1), …, 2k/(2k+1)`, and it occupies the indices
`k² ≤ n < (k+1)²`.  Since `Nat.sqrt n = k` exactly on that range of indices, the sequence has the
closed form `gridSeq n = (n - (sqrt n)²) / (2 * sqrt n + 1)`.
-/

open scoped BigOperators
open scoped Classical
open Filter Set

namespace Brockian
namespace EquidistributionBVReduction

/-- The concatenation of the uniform grids of odd sizes: the block of indices
`k² ≤ n < (k+1)²` runs through the `2k+1` points `j / (2k+1)`. -/

theorem configCount_gridSeq_density_of_BV {w : ℝ → ℝ}
    (hw : BoundedVariationOn w (Set.Icc 0 1)) :
    Tendsto (fun N : ℕ => configCount w gridSeq N / N) atTop (nhds (∫ t in (0:ℝ)..1, w t)) :=
  configCount_density_of_BV equidistributed_gridSeq hw

end EquidistributionBVReduction
end Brockian

import Mathlib

/-!
# Equidistribution: reduction to functions of bounded variation

Let `x : ℕ → ℝ` be a sequence.  We say `x` is *equidistributed* (mod one) when, for every
window `[a, b) ⊆ [0, 1]`, the proportion of the first `N` terms whose fractional part lies in
the window converges to the length `b - a` of the window.

The main result of this file, `Brockian.EquidistributionBVReduction.configCount_density_of_BV`,
upgrades this defining property from windows to arbitrary weights of bounded variation:
if `x` is equidistributed and `w : ℝ → ℝ` has bounded variation on `[0, 1]`, then the weighted
configuration counts `∑_{n < N} w (fract (x n))` have density `∫₀¹ w`.

The proof is the classical one: a function of bounded variation is a difference of two monotone
functions, and a monotone function is squeezed between the two step functions attached to a
uniform partition of `[0,1]`, whose averages are controlled directly by equidistribution.
-/

open scoped BigOperators
open scoped Classical
open Filter Set MeasureTheory

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of indices `n < N` for which the fractional part of `x n` lies in the
window `[a, b)`. -/
