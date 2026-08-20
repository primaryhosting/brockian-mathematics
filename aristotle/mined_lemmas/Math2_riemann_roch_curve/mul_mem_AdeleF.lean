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

lemma mul_mem_AdeleF (x : F) {α : P → F} (hα : α ∈ C.AdeleF) :
    (fun p => x * α p) ∈ C.AdeleF := by
  obtain ⟨S, hS⟩ := hα
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨∅, by simp⟩
  obtain ⟨T, hT⟩ := C.ord_support x hx
  refine ⟨S ∪ T, fun p hp => ?_⟩
  have h1 := hS p fun h => hp (Finset.mem_union_left _ h)
  have h2 := hT p fun h => hp (Finset.mem_union_right _ h)
  have h3 : C.ord p (x * α p) = C.ord p x + C.ord p (α p) := C.ord_mul p _ _
  simp only [h3, h2, zero_add]
  exact h1

/-- The adele space of the curve, as a type. -/
