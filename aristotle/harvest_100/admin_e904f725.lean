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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

/-- The point of the combinatorial line with wildcard set `S`, base point `v`,
and wildcard value `t`: coordinates in `S` take the value `t`, the others follow `v`. -/
def linePoint {N k : ℕ} (S : Finset (Fin N)) (v : Fin N → Fin k) (t : Fin k) :
    Fin N → Fin k :=
  fun i => if i ∈ S then t else v i

/-- **The Hales–Jewett theorem** (finitary form, on combinatorial lines).

For every alphabet size `k > 0` and every number of colors `r`, there is a dimension `N`
such that every `r`-coloring `C` of the hypercube `(Fin N → Fin k)` admits a monochromatic
combinatorial line: a nonempty set `S` of wildcard coordinates and a base point `v` such
that all `k` points `linePoint S v t`, `t : Fin k`, receive the same color `c`. -/
theorem hales_jewett (k r : ℕ) (hk : 0 < k) :
    ∃ N : ℕ, ∀ C : (Fin N → Fin k) → Fin r,
      ∃ (S : Finset (Fin N)) (v : Fin N → Fin k) (c : Fin r),
        S.Nonempty ∧ ∀ t : Fin k, C (linePoint S v t) = c := by
  classical
  obtain ⟨ι, hιfin, hHJ⟩ :=
    Combinatorics.Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  refine ⟨Fintype.card ι, fun C => ?_⟩
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  obtain ⟨l, c, hc⟩ := hHJ (fun x => C (fun j => x (e j)))
  refine ⟨Finset.univ.filter (fun j => l.idxFun (e j) = none),
    (fun j => (l.idxFun (e j)).getD ⟨0, hk⟩), c, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := l.proper
    exact ⟨e.symm i, by simp [hi]⟩
  · intro t
    have hpt : linePoint (Finset.univ.filter (fun j => l.idxFun (e j) = none))
        (fun j => (l.idxFun (e j)).getD ⟨0, hk⟩) t = fun j => l t (e j) := by
      funext j
      simp only [linePoint, Finset.mem_filter, Finset.mem_univ, true_and,
        Combinatorics.Line.coe_apply]
      cases l.idxFun (e j) with
      | none => simp
      | some a => simp
    rw [hpt]
    exact hc t

end Math2

#print axioms Math2.hales_jewett

