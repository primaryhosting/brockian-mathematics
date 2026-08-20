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

namespace Math2

/-- The point of the combinatorial line determined by a nonempty set of "wildcard" coordinates
`S ⊆ Fin N` and a base point `b : Fin N → Fin k`, at parameter `x : Fin k`: the coordinates in
`S` all take the value `x`, and the remaining coordinates keep the value given by `b`. -/
def linePoint {N k : ℕ} (S : Finset (Fin N)) (b : Fin N → Fin k) (x : Fin k) : Fin N → Fin k :=
  fun i => if i ∈ S then x else b i

/-- A combinatorial line, given by wildcard set `S` and base point `b`, is monochromatic for the
coloring `C` if all of its `k` points get the same color. -/
def IsMonoLine {N k r : ℕ} (C : (Fin N → Fin k) → Fin r) (S : Finset (Fin N))
    (b : Fin N → Fin k) : Prop :=
  ∃ c : Fin r, ∀ x : Fin k, C (linePoint S b x) = c

/-- **The Hales–Jewett theorem.** For every alphabet size `k > 0` and every number of colors `r`,
there is a dimension `N > 0` such that every `r`-coloring of the combinatorial hypercube
`[k]^N = (Fin N → Fin k)` admits a monochromatic combinatorial line: a nonempty set `S` of
wildcard coordinates and a base point `b` off `S` such that the `k` points
`fun i => if i ∈ S then x else b i`, for `x : Fin k`, all receive the same color. -/
theorem hales_jewett (k r : ℕ) (hk : 0 < k) :
    ∃ N : ℕ, 0 < N ∧ ∀ C : (Fin N → Fin k) → Fin r,
      ∃ (S : Finset (Fin N)) (b : Fin N → Fin k), S.Nonempty ∧ IsMonoLine C S b := by
  classical
  rcases Nat.eq_zero_or_pos r with hr | hr
  · -- With no colors available there is no coloring at all, so the statement is vacuous.
    subst hr
    exact ⟨1, one_pos, fun C => (C fun _ => ⟨0, hk⟩).elim0⟩
  obtain ⟨ι, hι, H⟩ :=
    Combinatorics.Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  refine ⟨Fintype.card ι, ?_, ?_⟩
  · -- the dimension is positive, since a line needs at least one wildcard coordinate
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
    · exfalso
      have : IsEmpty ι := Fintype.card_eq_zero_iff.mp h
      obtain ⟨l, -⟩ := H (fun _ => ⟨0, hr⟩)
      obtain ⟨i, -⟩ := l.proper
      exact this.elim i
    · exact h
  · intro C
    set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with he
    obtain ⟨l, c, hc⟩ := H (fun v => C (v ∘ e))
    refine ⟨Finset.univ.filter (fun j => l.idxFun (e j) = none),
      fun j => (l.idxFun (e j)).getD ⟨0, hk⟩, ?_, c, ?_⟩
    · obtain ⟨i, hi⟩ := l.proper
      exact ⟨e.symm i, by simp [hi]⟩
    · intro x
      have : linePoint (Finset.univ.filter (fun j => l.idxFun (e j) = none))
          (fun j => (l.idxFun (e j)).getD ⟨0, hk⟩) x = (l x) ∘ e := by
        funext j
        simp only [linePoint, Function.comp_apply, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases h : l.idxFun (e j) with _ | a
        · simp [h]
        · simp [h]
      rw [this]
      exact hc x

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

