/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean requires `import` lines to precede every command, including a
module docstring `/-! ... -/`, so this header is a plain comment and the
module docstring below repeats it after the imports.)
-/

import Mathlib
import Archive.Sensitivity

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
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

/-- Two points of the discrete hypercube `Fin n → Bool` are neighbours when they
differ in exactly one coordinate. -/
def IsNeighbour {n : ℕ} (p q : Fin n → Bool) : Prop :=
  (Finset.univ.filter fun i : Fin n => p i ≠ q i).card = 1

/-- Being a neighbour in the hypercube is the same as being adjacent in the sense
of the hypercube graph (`∃! i, p i ≠ q i`). -/
theorem isNeighbour_iff_adjacent {n : ℕ} (p q : Fin n → Bool) :
    IsNeighbour p q ↔ q ∈ Sensitivity.Q.adjacent (n := n) p := by
  classical
  unfold IsNeighbour Sensitivity.Q.adjacent
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 h
    refine ⟨i, ?_, ?_⟩
    · have : i ∈ (Finset.univ.filter fun i : Fin n => p i ≠ q i) := by
        rw [hi]; exact Finset.mem_singleton_self i
      simpa using this
    · intro j hj
      have : j ∈ (Finset.univ.filter fun i : Fin n => p i ≠ q i) := by
        simp [hj]
      rw [hi] at this
      simpa using this
  · rintro ⟨i, hi, huniq⟩
    refine Finset.card_eq_one.2 ⟨i, ?_⟩
    apply Finset.eq_singleton_iff_unique_mem.2
    refine ⟨by simp [hi], ?_⟩
    intro j hj
    exact huniq j (by simpa using hj)

/-- **Huang's sensitivity theorem** (the Huang degree theorem, 2019).

If more than half of the vertices of the `(n+1)`-dimensional hypercube
`Fin (n+1) → Bool` are selected, then some selected vertex has at least
`√(n+1)` selected neighbours (neighbours being the points differing in exactly
one coordinate).

This is the combinatorial heart of Huang's proof that the sensitivity of a
Boolean function is polynomially related to its degree.  The proof is obtained
from the formalization of Huang's theorem in `Archive.Sensitivity`
(`Sensitivity.huang_degree_theorem`). -/
theorem huang_sensitivity {n : ℕ} (H : Finset (Fin (n + 1) → Bool))
    (hH : 2 ^ n < H.card) :
    ∃ q ∈ H, Real.sqrt (n + 1) ≤ (H.filter fun q' => IsNeighbour q q').card := by
  obtain ⟨q, hqH, hq⟩ :=
    Sensitivity.huang_degree_theorem (m := n) (H := (H : Set (Fin (n + 1) → Bool)))
      (by rw [Set.toFinset_card]; simpa using hH)
  refine ⟨q, by simpa using hqH,
    hq.trans (Nat.cast_le.2 (Finset.card_le_card ?_))⟩
  intro x hx
  simp only [Set.mem_toFinset, Set.mem_inter_iff, Finset.mem_coe] at hx
  exact Finset.mem_filter.2 ⟨hx.1, (isNeighbour_iff_adjacent q x).2 hx.2⟩

/-- Huang's sensitivity theorem, phrased for a hypercube of any positive
dimension `n`: colouring more than half (`2 ^ (n - 1)`) of the `2 ^ n` vertices
of `Fin n → Bool` forces some coloured vertex to have at least `√n` coloured
neighbours. -/
theorem huang_sensitivity' {n : ℕ} (hn : 1 ≤ n) (H : Finset (Fin n → Bool))
    (hH : 2 ^ (n - 1) < H.card) :
    ∃ q ∈ H, Real.sqrt n ≤ (H.filter fun q' => IsNeighbour q q').card := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  simpa using huang_sensitivity (n := m) H (by simpa using hH)

end Frontier

