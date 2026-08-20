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

def AdeleF : Submodule K (P → F) where
  carrier := {α : P → F | ∃ S : Finset P, ∀ p ∉ S, (0 : Zt) ≤ C.ord p (α p)}
  zero_mem' := ⟨∅, by simp⟩
  add_mem' := by
    rintro α β ⟨S, hS⟩ ⟨T, hT⟩
    refine ⟨S ∪ T, fun p hp => ?_⟩
    have h1 := hS p fun h => hp (Finset.mem_union_left _ h)
    have h2 := hT p fun h => hp (Finset.mem_union_right _ h)
    exact le_trans (le_min h1 h2) (AddValuation.map_add _ _ _)
  smul_mem' := by
    rintro c α ⟨S, hS⟩
    rcases eq_or_ne c 0 with rfl | hc
    · exact ⟨∅, by simp⟩
    refine ⟨S, fun p hp => ?_⟩
    have h1 := hS p hp
    have h2 : C.ord p (c • α p) = C.ord p (α p) := C.ord_smul p c _ hc
    simpa [h2] using h1

