/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring; the required header is
-- reproduced verbatim as the module docstring immediately below the import.)

import RequestProject.Math2.Canonical

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Statement

For a smooth projective curve, described here through its function field `F / K` with its
family of places `P` (see `Math2.PreCurve` and `Math2.PreCurve.IsCurve`), there exists a
*canonical divisor* `W` such that for every divisor `D`

  `ℓ(D) - ℓ(W - D) = deg D + 1 - g`,

where `ℓ(D) = dim_K L(D)` is the dimension of the Riemann-Roch space of `D`, `deg D` is the
degree of `D` and `g` is the genus of the curve.  The canonical divisor moreover satisfies
`ℓ(W) = g` and `deg W = 2g - 2`.
-/

namespace Math2

open PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]

/-- **Riemann-Roch for a smooth projective curve.**

There is a canonical divisor `W` (of degree `2g - 2` and with `ℓ(W) = g`) such that for every
divisor `D` on the curve,
`ℓ(D) - ℓ(W - D) = deg D + 1 - g`. -/

lemma exists_finset_approx (f : FinPlace K → RatFunc K) (T : Finset (FinPlace K)) :
    ∃ y : RatFunc K, (∀ q ∈ T, f q - y ∈ (projectiveLine K).valSub (some q) 0) ∧
      (∀ q ∉ T, y ∈ (projectiveLine K).valSub (some q) 0) := by
  classical
  induction T using Finset.induction with
  | empty => exact ⟨0, by simp, fun q _ => Submodule.zero_mem _⟩
  | insert q₀ T' hq₀ ih =>
    obtain ⟨y', hy'1, hy'2⟩ := ih
    obtain ⟨w, hw1, hw2⟩ := exists_local_approx q₀ (f q₀ - y')
    refine ⟨y' + w, ?_, ?_⟩
    · intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hq'
      · simpa [sub_add_eq_sub_sub] using hw1
      · have h1 := hy'1 q hq'
        have hne : q ≠ q₀ := by rintro rfl; exact hq₀ hq'
        have h2 := hw2 q hne
        have : f q - (y' + w) = (f q - y') - w := by ring
        rw [this]
        exact Submodule.sub_mem _ h1 h2
    · intro q hq
      have hq' : q ∉ T' := fun h => hq (Finset.mem_insert_of_mem h)
      have hne : q ≠ q₀ := by rintro rfl; exact hq (Finset.mem_insert_self _ _)
      exact Submodule.add_mem _ (hy'2 q hq') (hw2 q hne)

/-- Approximation at the place at infinity by a polynomial. -/
