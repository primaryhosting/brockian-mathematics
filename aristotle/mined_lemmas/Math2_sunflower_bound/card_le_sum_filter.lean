/-
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- `IsSunflower T c` says that the family `T` is a *sunflower* with *core* `c`:
any two distinct members of `T` intersect exactly in `c`.  (The members of `T`
minus the core are the *petals*, and they are pairwise disjoint.) -/

theorem card_le_sum_filter {F : Finset (Finset α)} {Y : Finset α}
    (h : ∀ A ∈ F, (A ∩ Y).Nonempty) :
    F.card ≤ ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card := by
  classical
  have key : ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card
      = ∑ A ∈ F, (Y.filter (fun y => y ∈ A)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [key]
  calc F.card = ∑ _A ∈ F, 1 := by simp
    _ ≤ ∑ A ∈ F, (Y.filter (fun y => y ∈ A)).card := by
        refine Finset.sum_le_sum ?_
        intro A hA
        obtain ⟨y, hy⟩ := h A hA
        rw [Finset.mem_inter] at hy
        exact Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hy.2, hy.1⟩⟩

/-- **Erdős–Rado sunflower lemma.**  A family of more than `w ! * (r-1)^w` sets, each of
size `w`, contains a sunflower with `r` petals. -/
