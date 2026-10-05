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
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.Weyl.WeylLawTarget

open Filter

/-- The eigenvalue counting function of a sequence `lam : ℕ → ℝ` of eigenvalues
(listed with multiplicity): `counting lam t` is the number of indices `n` with
`lam n ≤ t`. -/
noncomputable def counting (lam : ℕ → ℝ) (t : ℝ) : ℕ := {n : ℕ | lam n ≤ t}.ncard

/-- The counting function is monotone in the spectral parameter. -/
theorem counting_mono (lam : ℕ → ℝ) (hfin : ∀ t : ℝ, {n : ℕ | lam n ≤ t}.Finite) :
    Monotone (counting lam) := by
  intro s t hst
  exact Set.ncard_le_ncard (fun n hn => le_trans hn hst) (hfin t)

/-- For every `N` there is a spectral parameter at which at least `N` eigenvalues
have been counted: the sublevel set at `t = max_{n < N} lam n` contains `Finset.range N`.
This is the existence statement that the main theorem used to assume. -/
theorem exists_counting_ge (lam : ℕ → ℝ) (hfin : ∀ t : ℝ, {n : ℕ | lam n ≤ t}.Finite)
    (N : ℕ) : ∃ t : ℝ, N ≤ counting lam t := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : ℝ, ∀ n ∈ Finset.range N, lam n ≤ t := by
    refine ⟨∑ k ∈ Finset.range N, |lam k|, ?_⟩
    intro n hn
    refine le_trans (le_abs_self (lam n)) ?_
    exact Finset.single_le_sum (f := fun k => |lam k|) (fun k _ => abs_nonneg _) hn
  refine ⟨t, ?_⟩
  have hsub : (↑(Finset.range N) : Set ℕ) ⊆ {n : ℕ | lam n ≤ t} := by
    intro n hn
    exact ht n (by simpa using hn)
  have := Set.ncard_le_ncard hsub (hfin t)
  simpa [counting, Set.ncard_coe_finset] using this

/-- **Weyl-law counting divergence.**  If every sublevel set of the eigenvalue
sequence `lam : ℕ → ℝ` is finite (i.e. the eigenvalues have no finite accumulation
from below and each is of finite multiplicity), then the eigenvalue counting function
`counting lam` tends to infinity as the spectral parameter tends to infinity.

The previously assumed existence hypothesis `∀ N, ∃ t, N ≤ counting lam t` is
discharged here by `exists_counting_ge`, so the statement is unconditional. -/
theorem counting_diverges_of_exists (lam : ℕ → ℝ)
    (hfin : ∀ t : ℝ, {n : ℕ | lam n ≤ t}.Finite) :
    Filter.Tendsto (counting lam) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.2 ?_
  intro N
  obtain ⟨t, ht⟩ := exists_counting_ge lam hfin N
  exact ⟨t, fun s hs => le_trans ht (counting_mono lam hfin hs)⟩

/-- Sanity check: the finiteness hypothesis of `counting_diverges_of_exists` is satisfiable,
so the theorem is not vacuous. -/
theorem counting_diverges_natCast :
    Filter.Tendsto (counting (fun n : ℕ => (n : ℝ))) Filter.atTop Filter.atTop := by
  refine counting_diverges_of_exists _ (fun t => ?_)
  refine Set.Finite.subset (Set.finite_Iio (⌊t⌋₊ + 1)) ?_
  intro n hn
  have hn' : (n : ℝ) ≤ t := hn
  exact Nat.lt_succ_of_le (Nat.le_floor hn')

end Brockian.Weyl.WeylLawTarget

