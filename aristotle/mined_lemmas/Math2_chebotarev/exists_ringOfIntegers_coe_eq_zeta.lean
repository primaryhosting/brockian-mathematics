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

theorem exists_ringOfIntegers_coe_eq_zeta :
    ∃ ξ : 𝓞 L, (ξ : L) = zeta (n := n) L ∧ ξ ^ n = 1 := by
  have hζ := isPrimitiveRoot_zeta (n := n) L
  refine ⟨⟨zeta (n := n) L, hζ.isIntegral (NeZero.pos n)⟩, rfl, ?_⟩
  have : (((⟨zeta (n := n) L, hζ.isIntegral (NeZero.pos n)⟩ : 𝓞 L) ^ n : 𝓞 L) : L) =
      ((1 : 𝓞 L) : L) := by
    push_cast [hζ.pow_eq_one]
    rfl
  exact Subtype.ext this

/-- The unit of `ZMod n` attached to a Galois automorphism `σ` of `ℚ(ζₙ)`, characterised by
`σ ζₙ = ζₙ ^ a`.  This is the standard isomorphism `Gal(ℚ(ζₙ)/ℚ) ≃ (ZMod n)ˣ`. -/
