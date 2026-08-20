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

lemma finrank_resField_some :
    finrank K ((projectiveLine K).resField (some q)) = q.poly.natDegree := by
  classical
  set n := q.poly.natDegree with hn
  have hmonic := q.monic
  -- the restriction of `polyToRes` to polynomials of degree `< n` is bijective
  set f : ↥(Polynomial.degreeLT K n) →ₗ[K] (projectiveLine K).resField (some q) :=
    (polyToRes q).comp (Polynomial.degreeLT K n).subtype with hf
  have hinj : Function.Injective f := by
    intro a b hab
    have h0 : polyToRes q ((a : K[X]) - b) = 0 := by
      rw [map_sub]
      simpa [hf] using sub_eq_zero.2 hab
    have hdvd : q.poly ∣ ((a : K[X]) - b) := (polyToRes_eq_zero_iff q _).1 h0
    have hdeg : ((a : K[X]) - b).degree < q.poly.degree := by
      have ha := a.2
      have hb := b.2
      rw [Polynomial.mem_degreeLT] at ha hb
      have := lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ha hb)
      rwa [Polynomial.degree_eq_natDegree q.ne_zero, ← hn]
    have : (a : K[X]) - b = 0 := by
      by_contra hne
      exact absurd (Polynomial.degree_le_of_dvd hdvd hne) (not_le.2 hdeg)
    exact Subtype.ext (sub_eq_zero.1 this)
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := polyToRes_surjective q y
    refine ⟨⟨a %ₘ q.poly, ?_⟩, ?_⟩
    · rw [Polynomial.mem_degreeLT]
      have := Polynomial.degree_modByMonic_lt a hmonic
      rwa [Polynomial.degree_eq_natDegree q.ne_zero] at this
    · have hsub : a - a %ₘ q.poly = q.poly * (a /ₘ q.poly) := by
        have := Polynomial.modByMonic_add_div a hmonic
        linear_combination -this
      have : polyToRes q (a - a %ₘ q.poly) = 0 := by
        rw [polyToRes_eq_zero_iff, hsub]
        exact Dvd.intro _ rfl
      rw [map_sub, sub_eq_zero] at this
      simpa [hf] using this.symm
  have hiso := (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq
  rw [← hiso, (Polynomial.degreeLTEquiv K n).finrank_eq, Module.finrank_pi]
  simp

/-! ### The residue field at infinity -/

