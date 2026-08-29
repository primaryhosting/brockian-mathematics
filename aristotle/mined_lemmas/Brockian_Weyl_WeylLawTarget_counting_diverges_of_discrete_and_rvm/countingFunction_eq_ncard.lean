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

/-!
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Brockian.Weyl.WeylLawTarget

variable {α : Type u}

/-- `countingFunction lam L K` is the number of indices `n < K` whose eigenvalue `lam n`
lies at or below the threshold `L`.  For a discrete spectrum this stabilises as `K → ∞`
and its limiting value is the Weyl counting function `N(L) = #{n | lam n ≤ L}`. -/

theorem countingFunction_eq_ncard (lam : ℕ → ℝ) (Λ : ℝ)
    {K : ℕ} (hK : ∀ n : ℕ, K ≤ n → ¬ lam n ≤ Λ) :
    countingFunction lam Λ K = {n : ℕ | lam n ≤ Λ}.ncard := by
  rw [countingFunction_eq_card]
  have hset : {n : ℕ | lam n ≤ Λ} = ↑((Finset.range K).filter (fun n => lam n ≤ Λ)) := by
    ext n
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    constructor
    · intro hn
      exact ⟨by by_contra hc; exact hK n (Nat.le_of_not_lt hc) hn, hn⟩
    · exact fun hn => hn.2
  rw [hset, Set.ncard_coe_finset]

/-- **The Weyl counting function of a discrete spectrum diverges.**
If only finitely many eigenvalues lie below each threshold, then
`N(Λ) = #{n | lam n ≤ Λ} → ∞` as `Λ → ∞`. -/
