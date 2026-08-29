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
# Counting Diverges Of Candidate
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_candidate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open Filter Set
open scoped Topology

namespace Brockian.Weyl.WeylLawTarget

/-- A *candidate spectrum* is a nondecreasing sequence of real numbers tending to `+∞`.
This is the abstract shape of the eigenvalue sequence appearing in a Weyl law:
eigenvalues listed in nondecreasing order and accumulating only at infinity. -/
structure IsCandidateSpectrum (mu : ℕ → ℝ) : Prop where
  mono : Monotone mu
  tendsto : Filter.Tendsto mu Filter.atTop Filter.atTop

/-- The eigenvalue counting function of a candidate spectrum:
`countingFunction mu L` is the number of indices `n` with `mu n ≤ L`. -/
noncomputable def countingFunction (mu : ℕ → ℝ) (L : ℝ) : ℕ := {n : ℕ | mu n ≤ L}.ncard

/-- For a sequence tending to `+∞`, only finitely many terms lie below any given level. -/
theorem finite_setOf_le_of_tendsto {mu : ℕ → ℝ}
    (h : Filter.Tendsto mu Filter.atTop Filter.atTop) (L : ℝ) :
    {n : ℕ | mu n ≤ L}.Finite := by
  obtain ⟨N, hN⟩ := (Filter.tendsto_atTop.mp h (L + 1)).exists_forall_of_atTop
  refine Set.Finite.subset (Set.finite_Iio N) ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  by_contra hcon
  exact absurd (hN n (not_lt.mp hcon)) (by linarith)

/-- The counting function is monotone in the level. -/
theorem countingFunction_mono {mu : ℕ → ℝ}
    (h : Filter.Tendsto mu Filter.atTop Filter.atTop) :
    Monotone (countingFunction mu) := fun _ _ hL =>
  Set.ncard_le_ncard (fun _ hn => le_trans hn hL) (finite_setOf_le_of_tendsto h _)

/-- **Target.** The eigenvalue counting function of a candidate spectrum diverges:
`countingFunction mu L → ∞` as `L → ∞`. -/
theorem counting_diverges_of_candidate {mu : ℕ → ℝ} (h : IsCandidateSpectrum mu) :
    Filter.Tendsto (countingFunction mu) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.mpr ?_
  intro M
  refine ⟨mu M, fun L hL => ?_⟩
  have hsub : Set.Iic M ⊆ {n : ℕ | mu n ≤ L} := fun n hn =>
    le_trans (h.mono (Set.mem_Iic.mp hn)) hL
  have hcard : (Set.Iic M).ncard = M + 1 := by simp [Set.ncard_eq_toFinset_card']
  have hle := Set.ncard_le_ncard hsub (finite_setOf_le_of_tendsto h.tendsto L)
  rw [hcard] at hle
  exact le_trans (Nat.le_succ M) hle

end Brockian.Weyl.WeylLawTarget

