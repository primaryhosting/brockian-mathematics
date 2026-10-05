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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Brockian.Weyl.WeylLawTarget

open Filter Set

/-- The eigenvalue counting function of a family of eigenvalues `lam : ι → ℝ`:
`counting lam t` is the number of indices `i` with `lam i ≤ t`. -/
noncomputable def counting {ι : Type*} (lam : ι → ℝ) (t : ℝ) : ℕ :=
  {i : ι | lam i ≤ t}.ncard

/-- If a finite set of indices all have eigenvalue `≤ t` and the sublevel set at `t`
is finite, then that finite set is counted by `counting lam t`. -/
theorem card_le_counting {ι : Type*} (lam : ι → ℝ) (t : ℝ)
    (hfin : {i : ι | lam i ≤ t}.Finite) (s : Finset ι) (hs : ∀ i ∈ s, lam i ≤ t) :
    s.card ≤ counting lam t := by
  have hsub : (↑s : Set ι) ⊆ {i : ι | lam i ≤ t} := fun i hi => hs i (by simpa using hi)
  have h := Set.ncard_le_ncard hsub hfin
  simpa [counting, Set.ncard_coe_finset] using h

/-- Any finite set of indices has a common upper bound for its eigenvalues. -/
theorem exists_bound_of_finset {ι : Type*} (lam : ι → ℝ) (s : Finset ι) :
    ∃ T : ℝ, ∀ i ∈ s, lam i ≤ T := by
  obtain ⟨T, hT⟩ := (s.finite_toSet.image lam).bddAbove
  exact ⟨T, fun i hi => hT ⟨i, by simpa using hi, rfl⟩⟩

/-- **Weyl law counting divergence.**
If there exist infinitely many eigenstates (`Infinite ι`) and every eigenvalue
sublevel set is finite, then the eigenvalue counting function diverges to `+∞`. -/
theorem counting_diverges_of_exists {ι : Type*} [Infinite ι] (lam : ι → ℝ)
    (hfin : ∀ t : ℝ, {i : ι | lam i ≤ t}.Finite) :
    Filter.Tendsto (counting lam) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro m
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq ι m
  obtain ⟨T, hT⟩ := exists_bound_of_finset lam s
  filter_upwards [Filter.eventually_ge_atTop T] with t ht
  have := card_le_counting lam t (hfin t) s (fun i hi => (hT i hi).trans ht)
  simpa [hs] using this

/-- The counting function never exceeds the total number of states. -/
theorem counting_le_natCard {ι : Type*} [Finite ι] (lam : ι → ℝ) (t : ℝ) :
    counting lam t ≤ Nat.card ι := by
  have h := Set.ncard_le_ncard (Set.subset_univ {i : ι | lam i ≤ t}) Set.finite_univ
  simpa [counting, Set.ncard_univ] using h

/-- Contrapositive companion: with only finitely many states the counting function is
bounded, hence cannot diverge. -/
theorem not_counting_diverges_of_finite {ι : Type*} [Finite ι] (lam : ι → ℝ) :
    ¬ Filter.Tendsto (counting lam) Filter.atTop Filter.atTop := by
  intro h
  have h' := (Filter.tendsto_atTop.1 h (Nat.card ι + 1)).exists
  obtain ⟨t, ht⟩ := h'
  exact absurd (ht.trans (counting_le_natCard lam t)) (by omega)

/-- Divergence of the counting function is *equivalent* to the existence of infinitely
many eigenstates, once all sublevel sets are finite. -/
theorem counting_diverges_iff_infinite {ι : Type*} (lam : ι → ℝ)
    (hfin : ∀ t : ℝ, {i : ι | lam i ≤ t}.Finite) :
    Filter.Tendsto (counting lam) Filter.atTop Filter.atTop ↔ Infinite ι := by
  constructor
  · intro h
    rw [← not_finite_iff_infinite]
    intro hfinite
    exact not_counting_diverges_of_finite lam h
  · intro h
    exact counting_diverges_of_exists lam hfin

/-- Non-vacuity: the Dirichlet eigenvalues `(n+1)^2` of the Laplacian on `(0, π)`
satisfy the hypotheses, so their counting function diverges. -/
theorem counting_diverges_dirichlet_interval :
    Filter.Tendsto (counting (fun n : ℕ => ((n : ℝ) + 1) ^ 2)) Filter.atTop Filter.atTop := by
  refine counting_diverges_of_exists _ (fun t => ?_)
  apply Set.Finite.subset (Set.finite_Iic ⌈t⌉₊)
  intro n hn
  have hn' : ((n : ℝ) + 1) ^ 2 ≤ t := hn
  have h1 : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have h2 : (n : ℝ) ≤ t := by linarith
  exact Set.mem_Iic.2 (Nat.cast_le.mp (h2.trans (Nat.le_ceil t)))

end Brockian.Weyl.WeylLawTarget

