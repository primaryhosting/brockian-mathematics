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
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`counting S Λ` is the number of points of `S` that are `≤ Λ`.
(For a set with infinitely many points below `Λ` this is `0`, by the convention for
`Set.ncard`; the `Discrete` hypothesis below rules out that degenerate case.) -/

lemma natSpectrum_weylLawMatch : WeylLawMatch (Set.range ((↑) : ℕ → ℝ)) 1 1 := by
  refine ⟨one_pos, one_pos, ?_⟩
  have hlow : ∀ᶠ L : ℝ in atTop,
      (1 : ℝ) ≤ (counting (Set.range ((↑) : ℕ → ℝ)) L : ℝ) / (1 * L ^ (1 : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [natSpectrum_counting L hL.le, Real.rpow_one, one_mul, le_div_iff₀ hL]
    push_cast
    have := Nat.lt_floor_add_one L
    linarith
  have hup : ∀ᶠ L : ℝ in atTop,
      (counting (Set.range ((↑) : ℕ → ℝ)) L : ℝ) / (1 * L ^ (1 : ℝ)) ≤ 1 + 1 / L := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [natSpectrum_counting L hL.le, Real.rpow_one, one_mul, div_le_iff₀ hL]
    push_cast
    have := Nat.floor_le hL.le
    field_simp
    linarith
  have h1 : Tendsto (fun L : ℝ => 1 + 1 / L) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℝ))).add
      tendsto_inv_atTop_zero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 hlow hup

/-- Instance of the main theorem on the model spectrum `ℕ ⊆ ℝ`. -/
example : Tendsto (fun L : ℝ => (counting (Set.range ((↑) : ℕ → ℝ)) L : ℝ)) atTop atTop :=
  counting_diverges_of_discrete_and_WeylLawMatch _ 1 1 natSpectrum_discrete
    natSpectrum_weylLawMatch

end Brockian.Weyl.WeylLawTarget

