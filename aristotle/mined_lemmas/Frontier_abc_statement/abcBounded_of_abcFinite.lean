/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
Mathlib does not state the `abc` conjecture. The closest existing material is
`UniqueFactorizationMonoid.radical` (`Mathlib/RingTheory/Radical.lean`), a general radical
of an element of a UFM, and the Mason–Stothers theorem
(`Mathlib/NumberTheory/FLT/MasonStothers.lean`), the polynomial analogue of `abc`.
Neither closes the statement below, so the radical for `ℕ` and both formulations of the
conjecture are set up here from scratch.
-/

namespace Frontier

open scoped BigOperators

/-- The radical of a natural number: the product of its distinct prime factors.
By convention `rad 0 = rad 1 = 1`. -/

lemma abcBounded_of_abcFinite (h : ABCFinite) : ABCBounded := by
  intro ε hε
  obtain hfin := h ε hε
  classical
  set T := hfin.toFinset with hT
  refine ⟨1 + ∑ t ∈ T, (t.2.2 : ℝ), by positivity, ?_⟩
  intro a b c ha hb hab habc
  have hr : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) :=
    Real.one_le_rpow (one_le_rad_real _) (by linarith)
  have hsum : (0 : ℝ) ≤ ∑ t ∈ T, (t.2.2 : ℝ) :=
    Finset.sum_nonneg fun t _ => by positivity
  by_cases hc : (rad (a * b * c) : ℝ) ^ (1 + ε) < (c : ℝ)
  · have hmem : ((a, b, c) : ℕ × ℕ × ℕ) ∈ T := by
      simp only [hT, Set.Finite.mem_toFinset, abcTriples, Set.mem_setOf_eq]
      exact ⟨ha, hb, hab, habc, hc⟩
    have h1 : (c : ℝ) ≤ ∑ t ∈ T, (t.2.2 : ℝ) :=
      Finset.single_le_sum (f := fun t : ℕ × ℕ × ℕ => (t.2.2 : ℝ))
        (fun i _ => by positivity) hmem
    calc (c : ℝ) ≤ 1 + ∑ t ∈ T, (t.2.2 : ℝ) := by linarith
      _ ≤ (1 + ∑ t ∈ T, (t.2.2 : ℝ)) * (rad (a * b * c) : ℝ) ^ (1 + ε) :=
          le_mul_of_one_le_right (by linarith) hr
  · push_neg at hc
    calc (c : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) := hc
      _ ≤ (1 + ∑ t ∈ T, (t.2.2 : ℝ)) * (rad (a * b * c) : ℝ) ^ (1 + ε) := by nlinarith

/-- From the effective-constant form one gets finiteness: applying the bound with `ε/2`
forces the radical, hence `c`, to be bounded on the exceptional set for `ε`. -/
