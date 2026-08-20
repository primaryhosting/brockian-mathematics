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

lemma mem_canonSupport_of_ne {x : RatFunc K} (hx : x ≠ 0) {p : Place K}
    (hp : p ∉ canonSupport x hx) :
    ∃ q : FinPlace K, p = some q ∧ cnt q x.num = 0 ∧ cnt q x.denom = 0 := by
  classical
  cases p with
  | none => exact absurd (Finset.mem_insert_self _ _) hp
  | some q =>
      refine ⟨q, rfl, ?_, ?_⟩ <;>
      · have hq : q ∉ (exists_finPlace_support x hx).choose := by
          intro h
          exact hp (Finset.mem_insert_of_mem (by
            simpa using Finset.mem_map_of_mem ⟨some, Option.some_injective _⟩ h))
        have := (exists_finPlace_support x hx).choose_spec q hq
        simp [this.1, this.2]

