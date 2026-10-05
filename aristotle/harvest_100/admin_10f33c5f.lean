import Mathlib

/-!
# Kervaire Invariant
Category: Frontier Math
Target: Math2.kervaire_invariant
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

/-- The dimensions permitted by the Hill–Hopkins–Ravenel theorem (together with the classical
low-dimensional constructions): a natural number `n` is a *Kervaire dimension* if it is of the
form `2 ^ (j + 1) - 2` for some index `1 ≤ j ≤ 6`, i.e. `n` is the dimension in which the
Kervaire invariant one element `θ_j` can live. -/
def KervaireDimension (n : ℕ) : Prop := ∃ j : ℕ, 1 ≤ j ∧ j ≤ 6 ∧ n + 2 = 2 ^ (j + 1)

/--
**Kervaire invariant: the admissible dimensions.**

This is the statement-level (arithmetic) content of the Hill–Hopkins–Ravenel theorem.
The deep homotopy-theoretic input is *not* assumed as an axiom anywhere; instead it appears
as explicit hypotheses on an abstract predicate `K` in the second conjunct.

* The first conjunct computes the list of admissible dimensions: `n` is of the form
  `2 ^ (j + 1) - 2` with `1 ≤ j ≤ 6` if and only if `n ∈ {2, 6, 14, 30, 62, 126}`.

* The second conjunct is the contrapositive-style reformulation. Let `K n` mean
  "there is a framed manifold of dimension `n` with Kervaire invariant one". Given
  * (Browder) every such `n` has the form `2 ^ (j + 1) - 2`, and
  * (Hill–Hopkins–Ravenel) the index `j` satisfies `1 ≤ j ≤ 6`,

  it follows that the Kervaire invariant is nonzero only in dimensions
  `2, 6, 14, 30, 62, 126`.
-/
theorem kervaire_invariant :
    (∀ n : ℕ, KervaireDimension n ↔ n ∈ ({2, 6, 14, 30, 62, 126} : Finset ℕ)) ∧
    (∀ K : ℕ → Prop,
      (∀ n, K n → ∃ j : ℕ, n + 2 = 2 ^ (j + 1)) →
      (∀ j : ℕ, K (2 ^ (j + 1) - 2) → 1 ≤ j ∧ j ≤ 6) →
      ∀ n, K n → n ∈ ({2, 6, 14, 30, 62, 126} : Finset ℕ)) := by
  have key : ∀ n j : ℕ, 1 ≤ j → j ≤ 6 → n + 2 = 2 ^ (j + 1) →
      n ∈ ({2, 6, 14, 30, 62, 126} : Finset ℕ) := by
    intro n j h1 h6 hn
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases j <;> norm_num at hn <;> omega
  refine ⟨fun n => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨j, h1, h6, hn⟩
    exact key n j h1 h6 hn
  · intro hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with h | h | h | h | h | h <;> subst h
    · exact ⟨1, by norm_num⟩
    · exact ⟨2, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨4, by norm_num⟩
    · exact ⟨5, by norm_num⟩
    · exact ⟨6, by norm_num⟩
  · intro K hform hbound n hn
    obtain ⟨j, hj⟩ := hform n hn
    have hn' : n = 2 ^ (j + 1) - 2 := by omega
    obtain ⟨h1, h6⟩ := hbound j (hn' ▸ hn)
    exact key n j h1 h6 hj

end Math2

