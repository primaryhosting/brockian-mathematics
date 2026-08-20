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

lemma map_mkQ_eq_range_psi (D : P →₀ ℤ) (p : P) :
    Submodule.map (C.AD D ⊔ C.FSub).mkQ (C.AD (D + Finsupp.single p 1) ⊔ C.FSub) =
      LinearMap.range (C.psi D (D + Finsupp.single p 1)) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    simp only [SetLike.mem_coe] at hz
    rw [Submodule.mem_sup] at hz
    obtain ⟨a, ha, f, hf, rfl⟩ := hz
    refine ⟨⟨a, ha⟩, ?_⟩
    simp only [psi, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    have hneg : a - (a + f) = -f := by abel
    rw [hneg]
    exact Submodule.neg_mem _ (Submodule.mem_sup_right hf)
  · rintro ⟨z, rfl⟩
    exact ⟨(z : C.Adele), Submodule.mem_sup_left z.2, rfl⟩

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- `H¹(D) / range ψ ≅ H¹(D + p)`. -/
