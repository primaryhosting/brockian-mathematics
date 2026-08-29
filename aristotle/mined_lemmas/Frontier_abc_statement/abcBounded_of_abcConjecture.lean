/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
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

/-- The radical of a natural number: the product of its distinct prime divisors. -/

theorem abcBounded_of_abcConjecture (h : ABCConjecture) : ABCBounded := by
  intro ε hε
  have hfin := h ε hε
  set S : Finset (ℕ × ℕ × ℕ) := hfin.toFinset with hSdef
  refine ⟨1 + ∑ t ∈ S, (t.2.2 : ℝ), ?_, ?_⟩
  · have : (0 : ℝ) ≤ ∑ t ∈ S, (t.2.2 : ℝ) :=
      Finset.sum_nonneg fun t _ => by positivity
    linarith
  · intro a b c ha hb hab hsum
    set K : ℝ := 1 + ∑ t ∈ S, (t.2.2 : ℝ) with hKdef
    have hsum0 : (0 : ℝ) ≤ ∑ t ∈ S, (t.2.2 : ℝ) :=
      Finset.sum_nonneg fun t _ => by positivity
    have hK1 : (1 : ℝ) ≤ K := by rw [hKdef]; linarith
    have hrad1 : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) := by
      apply Real.one_le_rpow (one_le_rad_real _)
      linarith
    by_cases hmem : (a, b, c) ∈ abcExceptions ε
    · have hcS : (a, b, c) ∈ S := by rw [hSdef]; simpa using hmem
      have : (c : ℝ) ≤ ∑ t ∈ S, (t.2.2 : ℝ) := by
        have := Finset.single_le_sum (f := fun t : ℕ × ℕ × ℕ => (t.2.2 : ℝ))
          (fun t _ => by positivity) hcS
        simpa using this
      have hcK : (c : ℝ) ≤ K := by rw [hKdef]; linarith
      calc (c : ℝ) ≤ K := hcK
        _ = K * 1 := by ring
        _ ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε) := by
            exact mul_le_mul_of_nonneg_left hrad1 (by linarith)
    · have hnot : ¬ ((rad (a * b * c) : ℝ) ^ (1 + ε) < (c : ℝ)) := by
        intro hlt
        exact hmem ⟨ha, hb, hab, hsum, by simpa using hlt⟩
      have hle : (c : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) := not_lt.1 hnot
      calc (c : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) := hle
        _ = 1 * (rad (a * b * c) : ℝ) ^ (1 + ε) := by ring
        _ ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε) := by
            apply mul_le_mul_of_nonneg_right hK1
            linarith

/-- **Statement of the abc conjecture, with a Lean-checked reduction.**

The finiteness form of the abc conjecture (`ABCConjecture`: for every `ε > 0` only finitely many
triples of positive coprime `a, b` with `a + b = c` satisfy `rad (a*b*c) ^ (1+ε) < c`) is
equivalent to the explicit-constant form (`ABCBounded`: for every `ε > 0` there is `K_ε > 0`
with `c ≤ K_ε * rad (a*b*c) ^ (1+ε)` for all such triples). -/
