import Brockian.Weyl.WeylLawTarget

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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.Weyl.WeylLawTarget

/-- A *candidate spectrum* for a Weyl-law statement: a nondecreasing sequence of real
eigenvalue candidates `lam 0 ≤ lam 1 ≤ ⋯` which is unbounded above.  This is the
combinatorial data underlying the eigenvalue counting function of a Weyl law. -/
structure Candidate where
  /-- The candidate eigenvalues, listed with multiplicity in nondecreasing order. -/
  lam : ℕ → ℝ
  /-- The listing is nondecreasing. -/
  mono : Monotone lam
  /-- The listing is unbounded: only finitely many candidates lie below any threshold. -/
  unbounded : Filter.Tendsto lam Filter.atTop Filter.atTop

namespace Candidate

variable (C : Candidate)

/-- Below any threshold `t` only finitely many candidate eigenvalues occur. -/
theorem finite_below (t : ℝ) : {n : ℕ | C.lam n ≤ t}.Finite := by
  obtain ⟨N, hN⟩ := (C.unbounded.eventually_gt_atTop t).exists_forall_of_atTop
  refine Set.Finite.subset (Set.finite_Iio N) ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  by_contra hlt
  exact absurd hn (not_le.2 (hN n (not_lt.1 hlt)))

/-- The eigenvalue counting function `N(t) = #{n : lam n ≤ t}`. -/
noncomputable def counting (t : ℝ) : ℕ := {n : ℕ | C.lam n ≤ t}.ncard

/-- If the `k`-th candidate eigenvalue is at most `t`, then at least `k + 1` candidates
are counted by `N(t)`. -/
theorem succ_le_counting {k : ℕ} {t : ℝ} (hk : C.lam k ≤ t) : k + 1 ≤ C.counting t := by
  have hsub : Set.Iic k ⊆ {n : ℕ | C.lam n ≤ t} := fun n hn =>
    le_trans (C.mono (Set.mem_Iic.1 hn)) hk
  have := Set.ncard_le_ncard hsub (C.finite_below t)
  simpa [counting, Nat.card_Iic] using this

end Candidate

/-- **Divergence of the counting function of a candidate spectrum.**
For any candidate spectrum, the eigenvalue counting function
`N(t) = #{n : lam n ≤ t}` tends to infinity as `t → ∞`.  This discharges the
hypothesis that the Weyl counting function of a candidate is unbounded. -/
theorem counting_diverges_of_candidate (C : Candidate) :
    Filter.Tendsto (fun t : ℝ => C.counting t) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun k => ?_
  filter_upwards [Filter.eventually_ge_atTop (C.lam k)] with t ht
  exact le_trans (Nat.le_succ k) (C.succ_le_counting ht)

/-- The hypothesis class is nonvacuous: `lam n = n` is a candidate spectrum. -/
example : Candidate where
  lam := fun n => (n : ℝ)
  mono := fun _ _ h => by simpa using Nat.cast_le.2 h
  unbounded := tendsto_natCast_atTop_atTop

end Brockian.Weyl.WeylLawTarget

