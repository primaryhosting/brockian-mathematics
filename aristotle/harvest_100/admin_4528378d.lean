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

/-
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology

namespace Brockian.EquidistributionBVReduction

/-!
In the Bombieri–Vinogradov style reduction of an equidistribution statement one
splits a counting function `total` into a `main` term plus an `error` term,
shows that the main term grows without bound, and that the error term is
negligible compared with the main term.  The conclusion used downstream is that
the ratio `total / main` converges to `1`.

Previously this conclusion was carried around as a named hypothesis; the lemma
below discharges it from the two structural inputs, making it unconditional.
-/

/-- **Total over main tends to one.**

If a counting function `total` splits as `main + error`, the main term tends to
infinity, and the relative error `error / main` tends to `0`, then
`total / main` tends to `1`.

The proof is elementary: eventually `main N ≠ 0`, so
`total N / main N = 1 + error N / main N`, and one concludes with
`Filter.Tendsto.add` (applied to `tendsto_const_nhds` and the error hypothesis)
together with `Filter.Tendsto.congr'`. -/
theorem total_over_main_tendsto
    (total main error : ℕ → ℝ)
    (hsplit : ∀ N, total N = main N + error N)
    (hmain : Tendsto main atTop atTop)
    (herror : Tendsto (fun N => error N / main N) atTop (𝓝 0)) :
    Tendsto (fun N => total N / main N) atTop (𝓝 1) := by
  have key : Tendsto (fun N => 1 + error N / main N) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add herror
  rw [add_zero] at key
  refine key.congr' ?_
  filter_upwards [hmain.eventually_gt_atTop 0] with N hN
  have hne : main N ≠ 0 := ne_of_gt hN
  rw [hsplit N, add_div, div_self hne]

/-- A variant with the relative-error hypothesis phrased via `Asymptotics.IsLittleO`:
`error =o[atTop] main` together with `main → ∞` gives `total / main → 1`. -/
theorem total_over_main_tendsto_of_isLittleO
    (total main error : ℕ → ℝ)
    (hsplit : ∀ N, total N = main N + error N)
    (hmain : Tendsto main atTop atTop)
    (herror : Asymptotics.IsLittleO atTop error main) :
    Tendsto (fun N => total N / main N) atTop (𝓝 1) := by
  refine total_over_main_tendsto total main error hsplit hmain ?_
  have hne : ∀ᶠ N in atTop, main N ≠ 0 := by
    filter_upwards [hmain.eventually_gt_atTop 0] with N hN using ne_of_gt hN
  have h := (Asymptotics.isLittleO_iff_tendsto' (hne.mono fun _ h hm => absurd hm h)).1 herror
  simpa using h

/-- Sanity check that the hypotheses of `total_over_main_tendsto` are satisfiable:
with `main N = N`, `error N = √N` and `total N = N + √N` the conclusion holds. -/
example :
    Tendsto (fun N : ℕ => ((N : ℝ) + Real.sqrt N) / (N : ℝ)) atTop (𝓝 1) := by
  refine total_over_main_tendsto _ (fun N => (N : ℝ)) (fun N => Real.sqrt N)
    (fun _ => rfl) tendsto_natCast_atTop_atTop ?_
  have h : (fun N : ℕ => Real.sqrt N / (N : ℝ)) =ᶠ[atTop] fun N : ℕ => 1 / Real.sqrt N :=
    Eventually.of_forall fun _ => Real.sqrt_div_self'
  refine Tendsto.congr' h.symm ?_
  exact tendsto_const_nhds.div_atTop
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

end Brockian.EquidistributionBVReduction

