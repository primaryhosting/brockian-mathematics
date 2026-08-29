import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
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

namespace Frontier

/-- A finite set `Y` of positive integers is *relatively large* when its least element is at
most its cardinality. -/

lemma exists_good {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) (F : Finset ℕ) :
    ∃ x, Good n c F x := by
  have hle : (hyperfilter ℕ : Filter ℕ) ≤ atTop := Nat.hyperfilter_le_atTop
  have h1 : ∀ᶠ x in (hyperfilter ℕ : Filter ℕ), 0 < x := hle (eventually_gt_atTop 0)
  have h2 : ∀ᶠ x in (hyperfilter ℕ : Filter ℕ), ∀ y ∈ F, y < x := by
    rw [eventually_all_finset]
    intro y _
    exact hle (eventually_gt_atTop y)
  have h3 : ∀ᶠ x in (hyperfilter ℕ : Filter ℕ), ∀ s ∈ F.powerset, s.card < n →
      G c (n - s.card - 1) (insert x s) = G c (n - s.card) s := by
    rw [eventually_all_finset]
    intro s _
    by_cases hs : s.card < n
    · filter_upwards [G_succ_spec c (n - s.card - 1) s] with x hx _
      rw [hx]
      congr 1
      omega
    · filter_upwards with x hx
      exact absurd hx hs
  exact (h1.and (h2.and h3)).exists

/-- The next element of the homogeneous chain built after the finite set `F`. -/
