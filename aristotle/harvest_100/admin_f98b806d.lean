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
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.Weyl.WeylLawTarget

/-- A *candidate spectrum* for a Weyl-law problem: an eigenvalue sequence
`lam`, listed with multiplicity, whose sublevel sets are finite — i.e. the
spectrum is discrete with finite multiplicities and does not accumulate at any
finite level. -/
structure Candidate where
  /-- The eigenvalue sequence, listed with multiplicity. -/
  lam : ℕ → ℝ
  /-- Discreteness: only finitely many indices have eigenvalue below a given level. -/
  discrete : ∀ t : ℝ, {n : ℕ | lam n ≤ t}.Finite

/-- The eigenvalue counting function `N(t) = #{n : λₙ ≤ t}` of a candidate. -/
noncomputable def counting (C : Candidate) (t : ℝ) : ℕ := {n : ℕ | C.lam n ≤ t}.ncard

/-- If the first `m + 1` eigenvalues of a candidate all lie below `t`, then the
counting function at `t` is at least `m + 1`. -/
lemma succ_le_counting (C : Candidate) (m : ℕ) (t : ℝ) (h : ∀ n ≤ m, C.lam n ≤ t) :
    m + 1 ≤ counting C t := by
  have hsub : (↑(Finset.range (m + 1)) : Set ℕ) ⊆ {n : ℕ | C.lam n ≤ t} := by
    intro n hn
    simp only [Finset.coe_range, Set.mem_Iio] at hn
    exact h n (Nat.lt_succ_iff.mp hn)
  have := Set.ncard_le_ncard hsub (C.discrete t)
  simpa [counting, Set.ncard_coe_finset] using this

/-- **Weyl-law target.** For any candidate spectrum, the eigenvalue counting
function diverges: `N(t) → ∞` as `t → ∞`. -/
theorem counting_diverges_of_candidate (C : Candidate) :
    Filter.Tendsto (counting C) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun m => ?_
  have hne : (Finset.range (m + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos m)⟩
  refine ⟨(Finset.range (m + 1)).sup' hne C.lam, fun t ht => ?_⟩
  refine le_trans (Nat.le_succ m) (succ_le_counting C m t fun n hn => ?_)
  exact le_trans (Finset.le_sup' C.lam (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))) ht

/-- Non-vacuity check: the sequence `λₙ = n` is a candidate spectrum. -/
example : Candidate where
  lam := fun n => (n : ℝ)
  discrete := by
    intro t
    refine Set.Finite.subset (Set.finite_Iio ⌈t⌉₊.succ) ?_
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    have hle : n ≤ ⌈t⌉₊ := by simpa using Nat.ceil_le_ceil hn
    exact Set.mem_Iio.mpr (Nat.lt_succ_of_le hle)

end Brockian.Weyl.WeylLawTarget

