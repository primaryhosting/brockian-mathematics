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

lemma exists_mem_AD (α : C.Adele) (D₀ : P →₀ ℤ) : ∃ D : P →₀ ℤ, D₀ ≤ D ∧ α ∈ C.AD D := by
  classical
  obtain ⟨S, hS⟩ := α.val_mem
  set f : P → ℤ := fun p => max (D₀ p) (max 0 (- C.ordZ p (α.val p))) with hf
  have hordnn : ∀ p ∉ S, 0 ≤ C.ordZ p (α.val p) := by
    intro p hpS
    rcases eq_or_ne (α.val p) 0 with h0 | h0
    · simp [ordZ, h0]
    · have h := hS p hpS
      rw [C.ord_eq_ordZ h0] at h
      exact_mod_cast h
  have hsupp : ∀ p ∉ (S ∪ D₀.support), f p = 0 := by
    intro p hp
    simp only [Finset.mem_union, not_or] at hp
    obtain ⟨hpS, hpD⟩ := hp
    have h1 : D₀ p = 0 := by simpa using hpD
    have h2 := hordnn p hpS
    simp only [hf, h1]
    omega
  refine ⟨Finsupp.onFinset (S ∪ D₀.support) f
    (fun p hp => by by_contra h; exact hp (hsupp p h)), ?_, ?_⟩
  · intro p
    simp only [Finsupp.onFinset_apply, hf]
    exact le_max_left _ _
  · intro p
    rcases eq_or_ne (α.val p) 0 with h0 | h0
    · simp [h0]
    · rw [C.ord_eq_ordZ h0]
      have hfp : - (f p) ≤ C.ordZ p (α.val p) := by
        simp only [hf]
        omega
      have hle : -((Finsupp.onFinset (S ∪ D₀.support) f
          (fun p hp => by by_contra h; exact hp (hsupp p h))) p) ≤ C.ordZ p (α.val p) := by
        simpa [Finsupp.onFinset_apply] using hfp
      exact_mod_cast hle

end PreCurve

end Math2

/-
The Euler characteristic `ell - i` and its behaviour under adding a place.
-/
import RequestProject.Math2.Step

namespace Math2

open Module Submodule

namespace PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]
variable (C : PreCurve K F P)

/-- The dimension of the first cohomology group of a divisor. -/
