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
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Asymptotics

namespace Brockian
namespace EquidistributionBVReduction

/-- The *total* quantity in a main-term/error-term decomposition: `total main err n`
is the main term `main n` corrected by the error term `err n`. -/
def total (main err : ℕ → ℝ) : ℕ → ℝ := fun n => main n + err n

@[simp]
theorem total_apply (main err : ℕ → ℝ) (n : ℕ) :
    total main err n = main n + err n := rfl

/-- **Total over main tends to one.**

If the main term is eventually nonzero and the error term is eventually negligible
relative to it (i.e. `err n / main n → 0`), then the ratio of the total quantity to
the main term tends to `1`.  This is the standard "main term dominates" step used to
turn an asymptotic expansion `total = main + err` into the asymptotic equivalence
`total ∼ main`. -/
theorem total_over_main_tendsto (main err : ℕ → ℝ)
    (hmain : ∀ᶠ n in atTop, main n ≠ 0)
    (herr : Tendsto (fun n => err n / main n) atTop (𝓝 0)) :
    Tendsto (fun n => total main err n / main n) atTop (𝓝 1) := by
  have hlim : Tendsto (fun n => 1 + err n / main n) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add herr
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hmain] with n hn
  simp only [total_apply]
  field_simp

/-- Little-o form of `total_over_main_tendsto`: if `err = o(main)` along `atTop` and
`main` is eventually nonzero, then `total / main → 1`.
Uses `Asymptotics.IsLittleO.tendsto_div_nhds_zero` from Mathlib. -/
theorem total_over_main_tendsto_of_isLittleO (main err : ℕ → ℝ)
    (hmain : ∀ᶠ n in atTop, main n ≠ 0)
    (herr : err =o[atTop] main) :
    Tendsto (fun n => total main err n / main n) atTop (𝓝 1) :=
  total_over_main_tendsto main err hmain herr.tendsto_div_nhds_zero

/-- Consequence: the total quantity is asymptotically equivalent to the main term. -/
theorem total_isEquivalent_main (main err : ℕ → ℝ) (herr : err =o[atTop] main) :
    (total main err) ~[atTop] main := by
  have h : total main err - main = err := by funext n; simp [total]
  simpa [Asymptotics.IsEquivalent, h] using herr

end EquidistributionBVReduction
end Brockian

