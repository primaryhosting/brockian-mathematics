/-
# Hales Jewett
Category: Frontier Math
Target: Math2.hales_jewett
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math2

/-- The point of the combinatorial line determined by the (nonempty) set of *moving*
coordinates `S` and the *fixed* pattern `f`, at the value `x` of the alphabet:
coordinates in `S` all take the value `x`, the others follow `f`. -/
def linePoint {N a : ℕ} (S : Finset (Fin N)) (f : Fin N → Fin a) (x : Fin a) :
    Fin N → Fin a :=
  fun i => if i ∈ S then x else f i

/-- **The Hales–Jewett theorem.**
For every (nonempty) alphabet size `a` and every number of colours `k`, there is a dimension
`N` such that any `k`-colouring `C` of the combinatorial cube `Fin N → Fin a` admits a
monochromatic combinatorial line: there is a nonempty set `S` of moving coordinates and a
fixed pattern `f` outside of `S` such that all `a` points `linePoint S f x` (`x : Fin a`)
receive the same colour `c`. -/
theorem hales_jewett (a k : ℕ) (ha : 0 < a) :
    ∃ N : ℕ, ∀ C : (Fin N → Fin a) → Fin k,
      ∃ (S : Finset (Fin N)) (f : Fin N → Fin a) (c : Fin k),
        S.Nonempty ∧ ∀ x : Fin a, C (linePoint S f x) = c := by
  classical
  obtain ⟨ι, ιfin, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin a) (Fin k)
  obtain ⟨e⟩ : Nonempty (Fin (Fintype.card ι) ≃ ι) :=
    ⟨(Fintype.equivFin ι).symm⟩
  refine ⟨Fintype.card ι, fun C => ?_⟩
  obtain ⟨l, c, hc⟩ := hι (fun v => C (fun i => v (e i)))
  refine ⟨Finset.univ.filter (fun i => l.idxFun (e i) = none),
    fun i => (l.idxFun (e i)).getD ⟨0, ha⟩, c, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := l.proper
    refine ⟨e.symm j, ?_⟩
    simp [hj]
  · intro x
    rw [← hc x]
    congr 1
    funext i
    simp only [linePoint, Finset.mem_filter, Finset.mem_univ, true_and,
      Combinatorics.Line.coe_apply]
    rcases hj : l.idxFun (e i) with _ | b
    · simp
    · simp

end Math2

#print axioms Math2.hales_jewett

