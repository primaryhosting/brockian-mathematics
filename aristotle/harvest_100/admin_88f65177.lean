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
# Counting Diverges Of Exists
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Counting Diverges Of Exists
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter
open scoped Topology

namespace Brockian.Weyl.WeylLawTarget

/-- The Weyl counting function of a set of eigenvalues `S ⊆ ℝ`:
`countingFn S t` is the number of elements of `S` that are `≤ t`. -/
noncomputable def countingFn (S : Set ℝ) (t : ℝ) : ℕ := {x ∈ S | x ≤ t}.ncard

/-- Under the local finiteness hypothesis, the counting function is monotone. -/
theorem countingFn_mono (S : Set ℝ) (hloc : ∀ t : ℝ, {x ∈ S | x ≤ t}.Finite) :
    Monotone (countingFn S) := by
  intro s t hst
  refine Set.ncard_le_ncard ?_ (hloc t)
  rintro x ⟨hxS, hxs⟩
  exact ⟨hxS, hxs.trans hst⟩

/-- If a finite set `F` of eigenvalues sits inside `S`, then the counting function is at
least `F.card` from the maximum of `F` on. -/
theorem card_le_countingFn (S : Set ℝ) (hloc : ∀ t : ℝ, {x ∈ S | x ≤ t}.Finite)
    (F : Finset ℝ) (hFS : ↑F ⊆ S) {t : ℝ} (ht : ∀ x ∈ F, x ≤ t) :
    F.card ≤ countingFn S t := by
  have hsub : (↑F : Set ℝ) ⊆ {x ∈ S | x ≤ t} := by
    intro x hx
    exact ⟨hFS hx, ht x (by simpa using hx)⟩
  have := Set.ncard_le_ncard hsub (hloc t)
  simpa [countingFn, Set.ncard_coe_finset] using this

/-- **Weyl-law counting divergence.**  If the eigenvalue set `S ⊆ ℝ` has finite sublevel sets
(local finiteness / discreteness of the spectrum below any energy) and contains arbitrarily
large finite subsets (i.e. there exist arbitrarily many eigenvalues), then the counting
function `t ↦ #{x ∈ S | x ≤ t}` diverges to `+∞`.

This is the unconditional form: the conclusion is obtained from the mere existence
statement `hex`, with no further assumptions. -/
theorem counting_diverges_of_exists (S : Set ℝ)
    (hloc : ∀ t : ℝ, {x ∈ S | x ≤ t}.Finite)
    (hex : ∀ n : ℕ, ∃ F : Finset ℝ, ↑F ⊆ S ∧ n ≤ F.card) :
    Tendsto (countingFn S) atTop atTop := by
  refine tendsto_atTop.2 fun n => ?_
  obtain ⟨F, hFS, hFcard⟩ := hex n
  obtain ⟨M, hM⟩ := F.exists_le
  filter_upwards [eventually_ge_atTop M] with t ht
  refine hFcard.trans (card_le_countingFn S hloc F hFS ?_)
  exact fun x hx => (hM x hx).trans ht

/-- Reformulation for a set that is merely infinite: an infinite spectrum with finite
sublevel sets has divergent counting function. -/
theorem counting_diverges_of_infinite (S : Set ℝ)
    (hloc : ∀ t : ℝ, {x ∈ S | x ≤ t}.Finite) (hS : S.Infinite) :
    Tendsto (countingFn S) atTop atTop := by
  refine counting_diverges_of_exists S hloc fun n => ?_
  obtain ⟨F, hFS, hFcard⟩ := hS.exists_subset_card_eq n
  exact ⟨F, hFS, hFcard.ge⟩

end Brockian.Weyl.WeylLawTarget

