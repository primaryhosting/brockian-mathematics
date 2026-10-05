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

theorem isArithFrobAt_of_zeta_pow (σ : L ≃ₐ[ℚ] L) {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n)
    (hσ : σ (zeta (n := n) L) = zeta (n := n) L ^ p)
    (Q : Ideal (𝓞 L)) (hQprime : Q.IsPrime)
    (hQp : Ideal.under ℤ Q = Ideal.span {(p : ℤ)}) :
    IsArithFrobAt ℤ σ Q := by
  haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  haveI := hQprime
  haveI : Finite (𝓞 L ⧸ Q) := finite_quotient_of_under_eq_span L hp hQp
  set τ : L ≃ₐ[ℚ] L := arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q with hτdef
  have hτ : IsArithFrobAt ℤ τ Q :=
    IsArithFrobAt.arithFrobAt (R := ℤ) (G := L ≃ₐ[ℚ] L) (S := 𝓞 L) Q
  have hτζ : τ (zeta (n := n) L) = zeta (n := n) L ^ p :=
    apply_zeta_eq_pow_of_isArithFrobAt L hQp hpn hτ
  have hτσ : τ = σ := eq_of_zeta_eq L (by rw [hτζ, hσ])
  rwa [hτσ] at hτ

/-- **Frobenius criterion.** For a prime `p` not dividing `n` and a prime `Q` of `𝓞 L` above
`p`, the automorphism `σ` is the Frobenius at `Q` if and only if the class of `p` in `ZMod n`
is the unit attached to `σ`. In particular the Frobenius depends only on `p`, not on `Q`. -/
