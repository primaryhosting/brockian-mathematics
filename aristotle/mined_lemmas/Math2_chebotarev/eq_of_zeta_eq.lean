import Mathlib

/-!
# Dirichlet density of primes in an invertible residue class

This file proves a quantitative form of Dirichlet's theorem on primes in arithmetic
progressions, in the logarithmic (Dirichlet) sense: if `a` is a unit of `ZMod q`, then

`(x - 1) * ∑' p prime, p ≡ a [q], log p / p ^ x → 1 / φ(q)`   as `x → 1⁺`.

This is the analytic input for the density form of the Chebotarev theorem for cyclotomic
extensions proved in `RequestProject.Main`.

The proof combines the results of `Mathlib.NumberTheory.LSeries.PrimesInAP`: the L-series of
the von Mangoldt function restricted to the residue class `a` has a simple pole at `s = 1`
with residue `1/φ(q)`, and the contribution of the proper prime powers is bounded.
-/

open scoped Classical

open ArithmeticFunction ArithmeticFunction.vonMangoldt Filter Topology Complex

namespace Math2

/-- The Dirichlet-density statement for primes in the residue class `a` mod `q`, in the form
of the logarithmically weighted prime sum: as `x → 1⁺`,
`(x - 1) * ∑_{p ≡ a (q)} (log p) p ^ (-x) → 1 / φ(q)`. -/

theorem eq_of_zeta_eq {σ τ : L ≃ₐ[ℚ] L} (h : σ (zeta (n := n) L) = τ (zeta (n := n) L)) :
    σ = τ := by
  have hζ := isPrimitiveRoot_zeta (n := n) L
  have hvals : ((IsPrimitiveRoot.autToPow ℚ hζ) σ : ZMod n).val =
      ((IsPrimitiveRoot.autToPow ℚ hζ) τ : ZMod n).val := by
    refine hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) ?_
    rw [hζ.autToPow_spec ℚ σ, hζ.autToPow_spec ℚ τ, h]
  exact hζ.autToPow_injective ℚ (Units.ext (ZMod.val_injective n hvals))

/-- **Key step, one direction.** If `σ` is the Frobenius at a prime `Q` above a prime `p` that
does not divide `n`, then `σ` raises `ζₙ` to the `p`-th power. -/
