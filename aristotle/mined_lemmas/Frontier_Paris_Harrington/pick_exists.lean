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

set_option grind.warning false

namespace Frontier

namespace ParisHarrington

open Filter

/-- A fixed ultrafilter on `ℕ` refining the filter `atTop`; in particular every cofinite
set belongs to it. -/

lemma pick_exists (c : Finset ℕ → Fin k) (n : ℕ) (A : Finset ℕ) :
    ∃ x, (∀ y ∈ A, y < x) ∧
      ∀ t ∈ A.powerset, ∀ q ≤ n, D c q (insert x t) = D c (q + 1) t := by
  have h1 : {x : ℕ | ∀ y ∈ A, y < x} ∈ Ultra := by
    refine mem_Ultra_of_mem_atTop ?_
    filter_upwards [eventually_ge_atTop (A.sup id + 1)] with x hx y hy
    have : y ≤ A.sup id := Finset.le_sup (f := id) hy
    omega
  have h2 : (⋂ t ∈ A.powerset, ⋂ q ∈ Finset.range (n + 1),
      {x : ℕ | D c q (insert x t) = D c (q + 1) t}) ∈ Ultra :=
    (Filter.biInter_finset_mem _).2 fun t _ =>
      (Filter.biInter_finset_mem _).2 fun q _ => good_mem_Ultra c q t
  obtain ⟨x, hx1, hx2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem h1 h2)
  refine ⟨x, hx1, fun t ht q hq => ?_⟩
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hx2
  exact hx2 t ht q (Finset.mem_range.2 (by omega))

/-- A choice of a next element of the homogeneous set, given the finite set `A` of already
chosen elements. -/
