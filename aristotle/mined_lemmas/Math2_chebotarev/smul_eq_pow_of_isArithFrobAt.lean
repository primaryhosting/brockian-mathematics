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

theorem smul_eq_pow_of_isArithFrobAt (L : Type) [Field L] [NumberField L] {p : ℕ}
    {Q : Ideal (𝓞 L)} (hQp : Ideal.under ℤ Q = Ideal.span {(p : ℤ)}) {σ : L ≃ₐ[ℚ] L}
    (H : IsArithFrobAt ℤ σ Q) {n : ℕ} {ξ : 𝓞 L} (hξ : ξ ^ n = 1) (hn : (n : 𝓞 L) ∉ Q) :
    σ • ξ = ξ ^ p := by
  have hcard : Nat.card (ℤ ⧸ Ideal.under ℤ Q) = p := by
    rw [hQp, Nat.card_congr (Int.quotientSpanEquivZMod (p : ℤ)).toEquiv]
    simp
  have h := H.apply_of_pow_eq_one hξ hn
  rwa [hcard] at h

/-- If `x ^ n = 1` then the powers of `x` only depend on the exponent modulo `n`. -/
