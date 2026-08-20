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

lemma AD_sup_le (C : PreCurve K F P) (A B : P →₀ ℤ) :
    C.AD (A ⊔ B) ≤ C.AD A ⊔ C.AD B := by
  classical
  intro α hα
  have hsup : ∀ p : P, (A ⊔ B) p = max (A p) (B p) := by
    intro p; rw [Finsupp.sup_apply]
  have hmem : (fun p => if B p ≤ A p then α.val p else 0) ∈ C.AdeleF := by
    obtain ⟨S, hS⟩ := α.val_mem
    refine ⟨S, fun p hp => ?_⟩
    by_cases h : B p ≤ A p
    · simpa [h] using hS p hp
    · simp [h]
  set β : C.Adele := Adele.mk C (fun p => if B p ≤ A p then α.val p else 0) hmem with hβ
  have hβA : β ∈ C.AD A := by
    intro p
    have h := hα p
    rw [hsup p] at h
    by_cases hc : B p ≤ A p
    · have : max (A p) (B p) = A p := max_eq_left hc
      rw [this] at h
      simpa [hβ, hc] using h
    · simp [hβ, hc]
  have hγB : α - β ∈ C.AD B := by
    intro p
    have h := hα p
    rw [hsup p] at h
    by_cases hc : B p ≤ A p
    · have : (α - β).val p = 0 := by simp [hβ, hc]
      rw [this]
      simp
    · have hBA : max (A p) (B p) = B p := max_eq_right (le_of_lt (lt_of_not_ge hc))
      rw [hBA] at h
      have hval : (α - β).val p = α.val p := by simp [hβ, hc]
      rw [hval]
      exact h
  have : α = β + (α - β) := by abel
  rw [this]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hβA) (Submodule.mem_sup_right hγB)

