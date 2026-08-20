/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- The radical of `n`: the product of the distinct prime factors of `n`.
By convention `rad 0 = rad 1 = 1`. -/

def rad (n : ℕ) : ℕ := n.primeFactors.prod id

/-- The set of *exceptional* `abc`-triples for a given `ε`: positive coprime `a, b`
with `a + b = c` and `c > rad (a * b * c) ^ (1 + ε)`. -/

def abcExceptional (eps : ℝ) : Set (ℕ × ℕ × ℕ) :=
  {t | 0 < t.1 ∧ 0 < t.2.1 ∧ Nat.Coprime t.1 t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧
        ((rad (t.1 * t.2.1 * t.2.2) : ℝ)) ^ (1 + eps) < (t.2.2 : ℝ)}

/-- The `abc` conjecture: for every `ε > 0` there are only finitely many coprime triples
`a + b = c` of positive integers with `c > rad (a * b * c) ^ (1 + ε)`. -/

def abcConjecture : Prop := ∀ eps : ℝ, 0 < eps → (abcExceptional eps).Finite

/-- `rad 72 = 6`, since `72 = 2 ^ 3 * 3 ^ 2`. -/

theorem abcExceptional_finite_of_bounded {eps : ℝ} {C : ℕ}
    (h : ∀ t ∈ abcExceptional eps, t.2.2 ≤ C) : (abcExceptional eps).Finite := by
  apply Set.Finite.subset
    (((Set.finite_Iic C).prod ((Set.finite_Iic C).prod (Set.finite_Iic C))))
  intro t ht
  have hc := h t ht
  obtain ⟨ha, hb, -, hsum, -⟩ := ht
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Set.mem_Iic] <;> omega

/-- If the exceptional set for `ε` is finite, then `c` is bounded on it. -/

theorem abcExceptional_bounded_of_finite {eps : ℝ} (h : (abcExceptional eps).Finite) :
    ∃ C : ℕ, ∀ t ∈ abcExceptional eps, t.2.2 ≤ C := by
  obtain ⟨C, hC⟩ := (h.image (fun t => t.2.2)).bddAbove
  exact ⟨C, fun t ht => hC ⟨t, ht, rfl⟩⟩

/-- **Reduction of the `abc` conjecture to a boundedness statement.**

The `abc` conjecture (for every `ε > 0`, only finitely many coprime triples `a + b = c`
of positive integers satisfy `rad (a * b * c) ^ (1 + ε) < c`) is equivalent to the
statement that for every `ε > 0` the value of `c` is bounded along such triples. -/

theorem abc_statement :
    abcConjecture ↔ ∀ eps : ℝ, 0 < eps → ∃ C : ℕ, ∀ t ∈ abcExceptional eps, t.2.2 ≤ C := by
  constructor
  · intro h eps heps
    exact abcExceptional_bounded_of_finite (h eps heps)
  · intro h eps heps
    obtain ⟨C, hC⟩ := h eps heps
    exact abcExceptional_finite_of_bounded hC

end Frontier

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
