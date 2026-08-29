import Mathlib
/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
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

namespace Frontier.Spectral

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`
(there are `2 ^ k` of them). -/
abbrev Cube (k : ℕ) : Type := Fin k → ZMod 2


theorem sum_chi {k : ℕ} (z : Cube k) :
    ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset, chi S z = if z = 0 then (2 ^ k : ℝ) else 0 := by
  have key : ∏ i : Fin k, (eps (z i) + 1)
      = ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset, chi S z := by
    rw [Finset.prod_add]
    exact Finset.sum_congr rfl fun S _ => by simp [chi]
  rw [← key]
  by_cases hz : z = 0
  · subst hz
    simp only [Pi.zero_apply, eps_zero]
    norm_num
  · rw [if_neg hz]
    obtain ⟨i, hi⟩ : ∃ i : Fin k, z i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hz (funext hc)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have hzi : z i = 1 := by
      have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      rcases h (z i) with h' | h'
      · exact absurd h' hi
      · exact h'
    rw [hzi, eps_one]; ring

/-- The Laplacian is symmetric for the standard inner product. -/
