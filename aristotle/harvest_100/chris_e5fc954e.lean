/-
# Hales Jewett
Category: Frontier Math
Target: Math2.hales_jewett
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Math2

/-- The **Hales–Jewett theorem**, stated in elementary terms.

For every alphabet size `k > 0` and every number of colours `r`, there is a dimension `N`
such that every `r`-colouring `C` of the combinatorial cube `Fin N → Fin k` admits a
monochromatic combinatorial line: a nonempty set `S` of "wildcard" coordinates together with
a word `v` fixing the remaining coordinates, such that all `k` points
`fun i => if i ∈ S then a else v i` (for `a : Fin k`) receive the same colour `c`. -/
theorem hales_jewett (k r : ℕ) (hk : 0 < k) :
    ∃ N : ℕ, ∀ C : (Fin N → Fin k) → Fin r,
      ∃ S : Finset (Fin N), S.Nonempty ∧ ∃ v : Fin N → Fin k, ∃ c : Fin r,
        ∀ a : Fin k, C (fun i => if i ∈ S then a else v i) = c := by
  obtain ⟨ι, _, hι⟩ :=
    Combinatorics.Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  classical
  refine ⟨Fintype.card ι, fun C => ?_⟩
  -- transport the colouring along an equivalence `Fin (card ι) ≃ ι`
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  obtain ⟨l, c, hc⟩ := hι (fun x => C (fun i => x (e i)))
  refine ⟨Finset.univ.filter (fun i => l.idxFun (e i) = none), ?_,
    fun i => (l.idxFun (e i)).getD ⟨0, hk⟩, c, fun a => ?_⟩
  · obtain ⟨j, hj⟩ := l.proper
    exact ⟨e.symm j, by simp [hj]⟩
  · have := hc a
    refine Eq.trans ?_ this
    congr 1
    funext i
    cases h : l.idxFun (e i) <;> simp [h]

end Math2

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

