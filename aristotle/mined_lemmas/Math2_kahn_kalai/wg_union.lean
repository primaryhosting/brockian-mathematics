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
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Basic definitions for the Kahn–Kalai theorem (Park–Pham proof):
the Bernoulli product measure on subsets of a finite ground set, covers,
`p`-smallness, up-sets, and the parameters `q(F)`, `p_c(F)`, `ℓ(F)`.
-/

namespace Math2

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Bernoulli(`p`) product weight of a subset `A` inside the ground set `g`. -/

lemma wg_union (s t : ℝ) (g : Finset α) : ∀ f : Finset α → ℝ,
    ∑ A ∈ g.powerset, ∑ B ∈ g.powerset, wg g s A * (wg g t B * f (A ∪ B))
      = ∑ C ∈ g.powerset, wg g (s + t - s * t) C * f C := by
  induction g using Finset.induction_on with
  | empty => intro f; simp [wg]
  | insert x g₀ hx ih =>
      intro f
      have hL : ∑ A ∈ (insert x g₀).powerset, ∑ B ∈ (insert x g₀).powerset,
            wg (insert x g₀) s A * (wg (insert x g₀) t B * f (A ∪ B))
          = (1 - s) * (1 - t) *
              (∑ A ∈ g₀.powerset, ∑ B ∈ g₀.powerset, wg g₀ s A * (wg g₀ t B * f (A ∪ B)))
            + (s + t - s * t) *
              (∑ A ∈ g₀.powerset, ∑ B ∈ g₀.powerset,
                wg g₀ s A * (wg g₀ t B * f (insert x (A ∪ B)))) := by
        simp only [Finset.sum_powerset_insert hx, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun A hA => ?_
        rw [Finset.mem_powerset] at hA
        refine Finset.sum_congr rfl fun B hB => ?_
        rw [Finset.mem_powerset] at hB
        simp only [wg_insert_notMem hx hA, wg_insert_mem hx hA, wg_insert_notMem hx hB,
          wg_insert_mem hx hB, Finset.union_insert, Finset.insert_union, Finset.insert_idem]
        ring
      rw [hL, ih f, ih (fun C => f (insert x C))]
      rw [Finset.sum_powerset_insert hx, Finset.mul_sum, Finset.mul_sum]
      refine congrArg₂ (· + ·) ?_ ?_ <;>
        refine Finset.sum_congr rfl fun C hC => ?_ <;> rw [Finset.mem_powerset] at hC
      · rw [wg_insert_notMem hx hC]; ring_nf
      · rw [wg_insert_mem hx hC]; ring

