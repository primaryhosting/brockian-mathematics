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

lemma AD_zero_sup_FSub_eq_top :
    (projectiveLine K).AD 0 ⊔ (projectiveLine K).FSub = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro α -
  obtain ⟨S, hS⟩ := α.val_mem
  set T : Finset (FinPlace K) := S.preimage some (Option.some_injective _).injOn with hT
  obtain ⟨y, hy1, hy2⟩ := exists_finset_approx (fun q => α.val (some q)) T
  have hfin : ∀ q : FinPlace K,
      α.val (some q) - y ∈ (projectiveLine K).valSub (some q) 0 := by
    intro q
    by_cases hq : q ∈ T
    · exact hy1 q hq
    · have hnot : (some q : Place K) ∉ S := by
        intro h
        exact hq (Finset.mem_preimage.2 h)
      have h1 : α.val (some q) ∈ (projectiveLine K).valSub (some q) 0 := by
        have := hS (some q) hnot
        rw [PreCurve.mem_valSub_iff]
        simpa using this
      exact Submodule.sub_mem _ h1 (hy2 q hq)
  obtain ⟨g, hg⟩ := exists_poly_approx_inf (α.val none - y)
  refine Submodule.mem_sup.2
    ⟨α - (projectiveLine K).diagLin (y + algebraMap K[X] (RatFunc K) g), ?_,
      (projectiveLine K).diagLin (y + algebraMap K[X] (RatFunc K) g), ⟨_, rfl⟩, by ring⟩
  rw [PreCurve.mem_AD_iff]
  intro p
  have hmem : α.val p - (y + algebraMap K[X] (RatFunc K) g)
      ∈ (projectiveLine K).valSub p 0 := by
    cases p with
    | none =>
      have : α.val none - (y + algebraMap K[X] (RatFunc K) g)
          = (α.val none - y) - algebraMap K[X] (RatFunc K) g := by ring
      rw [this]
      exact hg
    | some q =>
      have : α.val (some q) - (y + algebraMap K[X] (RatFunc K) g)
          = (α.val (some q) - y) - algebraMap K[X] (RatFunc K) g := by ring
      rw [this]
      exact Submodule.sub_mem _ (hfin q) (algebraMap_mem_valSub_zero q g)
  rw [PreCurve.mem_valSub_iff] at hmem
  simpa using hmem

end P1

end Math2

/-
The projective line as a `PreCurve`.
-/
import RequestProject.P1.OrdInf
import RequestProject.Math2.Setup

namespace Math2

namespace P1

open Polynomial RatFunc

universe u

variable {K : Type u} [Field K]

/-- A place of the projective line over `K`: either a finite place (a monic irreducible
polynomial) or the place at infinity. -/
abbrev Place (K : Type u) [Field K] := Option (FinPlace K)

/-- The valuation attached to a place. -/
