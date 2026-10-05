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

theorem apply_zeta_eq_pow_of_isArithFrobAt {p : ℕ} {Q : Ideal (𝓞 L)}
    (hQp : Ideal.under ℤ Q = Ideal.span {(p : ℤ)}) (hpn : ¬ p ∣ n) {σ : L ≃ₐ[ℚ] L}
    (H : IsArithFrobAt ℤ σ Q) :
    σ (zeta (n := n) L) = zeta (n := n) L ^ p := by
  obtain ⟨ξ, hξc, hξpow⟩ := exists_ringOfIntegers_coe_eq_zeta (n := n) L
  have hnQ : (n : 𝓞 L) ∉ Q := cast_not_mem_of_not_dvd L hQp hpn
  have hsmul : σ • ξ = ξ ^ p := smul_eq_pow_of_isArithFrobAt L hQp H hξpow hnQ
  have h : ((σ • ξ : 𝓞 L) : L) = ((ξ ^ p : 𝓞 L) : L) := congrArg (fun y : 𝓞 L => (y : L)) hsmul
  have hl : ((σ • ξ : 𝓞 L) : L) = σ (zeta (n := n) L) := by rw [← hξc]; rfl
  rw [hl] at h
  simpa [hξc] using h

/-- **Key step, other direction.** Let `σ` be an automorphism of `L = ℚ(ζₙ)` sending `ζₙ` to
`ζₙ ^ p`, where `p` is a prime not dividing `n`. Then `σ` is the Frobenius element at *every*
prime `Q` of `𝓞 L` lying over `p`, i.e. `σ x ≡ x ^ p (mod Q)` for all `x : 𝓞 L`. -/
