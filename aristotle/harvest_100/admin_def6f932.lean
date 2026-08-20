/-
# Hales Jewett
Category: Frontier Math
Target: Math2.hales_jewett
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hales Jewett
Category: Frontier Math
Target: Math2.hales_jewett
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

set_option grind.warning false

namespace Math2

/-- **The Hales–Jewett theorem** (combinatorial lines), in an explicit numerical form.

For every alphabet size `a > 0` and every number of colours `k`, there is a dimension `n` such
that every colouring `C : (Fin n → Fin a) → Fin k` of the hypercube `Fin n → Fin a` admits a
*monochromatic combinatorial line*: a nonempty set `S` of "moving" coordinates together with a
word `w` fixing the remaining coordinates, such that all `a` points
`fun i => if i ∈ S then x else w i` (for `x : Fin a`) get the same colour.

The proof is a transfer along a cardinality equivalence from Mathlib's
`Combinatorics.Line.exists_mono_in_high_dimension`. -/
theorem hales_jewett (a k : ℕ) (ha : 0 < a) :
    ∃ n : ℕ, ∀ C : (Fin n → Fin a) → Fin k,
      ∃ (S : Finset (Fin n)) (w : Fin n → Fin a) (c : Fin k),
        S.Nonempty ∧ ∀ x : Fin a, C (fun i => if i ∈ S then x else w i) = c := by
  obtain ⟨ι, ιfin, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin a) (Fin k)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun C => ?_⟩
  obtain ⟨l, c, hc⟩ := hι (fun v => C (fun i => v (e.symm i)))
  classical
  refine ⟨Finset.univ.filter (fun i => l.idxFun (e.symm i) = none),
    fun i => (l.idxFun (e.symm i)).getD ⟨0, ha⟩, c, ?_, fun x => ?_⟩
  · obtain ⟨i, hi⟩ := l.proper
    exact ⟨e i, by simp [hi]⟩
  · rw [← hc x]
    congr 1
    funext i
    cases hv : l.idxFun (e.symm i) with
    | none => simp [hv]
    | some v => simp [hv]

end Math2

