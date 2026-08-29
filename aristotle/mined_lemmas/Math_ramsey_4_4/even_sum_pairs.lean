/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The two-colour Ramsey number `R(4,4)` equals `18`.

Mathlib (at the pinned revision) contains no theory of Ramsey numbers, so the whole
argument is developed here:

* the classical upper bound `R(p+1,q+1) ≤ R(p,q+1) + R(p+1,q)` (`Math.arrow_step`),
* `R(3,3) ≤ 6` and, via the parity/degree argument, `R(3,4) ≤ 9`
  (`Math.arrow_three_three`, `Math.arrow_three_four`), giving `R(4,4) ≤ 18`,
* the Paley graph on 17 vertices, which has neither a 4-clique nor a 4-element
  independent set, giving `R(4,4) > 17`.
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open Finset

/-! ## A relation-theoretic formulation of Ramsey's theorem for two colours -/

variable {V : Type*}

/-- A finite set `t` is homogeneous for the relation `r` if all distinct pairs of elements
of `t` are related by `r`. -/

lemma even_sum_pairs (f : V → V → ℕ) (hf : ∀ a b, f a b = f b a) (hd : ∀ a, f a a = 0)
    (S : Finset V) : Even (∑ v ∈ S, ∑ u ∈ S, f v u) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have h1 : ∀ v : V, ∑ u ∈ insert a s, f v u = f v a + ∑ u ∈ s, f v u := by
        intro v; rw [Finset.sum_insert ha]
      rw [Finset.sum_insert ha, h1]
      simp only [h1]
      rw [Finset.sum_add_distrib, hd a]
      have h2 : ∑ v ∈ s, f v a = ∑ u ∈ s, f a u := Finset.sum_congr rfl fun v _ => hf v a
      rw [h2]
      obtain ⟨k, hk⟩ := ih
      exact ⟨∑ u ∈ s, f a u + k, by omega⟩

/-- `R(3,4) ≤ 9`, for a set of exactly nine vertices.

If there is no homogeneous triple and no anti-homogeneous quadruple, then every vertex has
exactly three neighbours, so the sum of the degrees is `27`, contradicting the handshake
parity. -/
