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

theorem exists_isArithFrobAt_iff (σ : L ≃ₐ[ℚ] L) {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) :
    (∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Ideal.under ℤ Q = Ideal.span {(p : ℤ)} ∧
      IsArithFrobAt ℤ σ Q) ↔ (p : ZMod n) = (cycloUnit (n := n) L σ : ZMod n) := by
  obtain ⟨Q₀, hQ₀prime, hQ₀p, -⟩ := exists_isPrime_under_eq_span L p hp
  constructor
  · rintro ⟨Q, hQprime, hQp, H⟩
    exact (isArithFrobAt_iff L σ hp hpn Q hQprime hQp).mp H
  · intro h
    exact ⟨Q₀, hQ₀prime, hQ₀p, (isArithFrobAt_iff L σ hp hpn Q₀ hQ₀prime hQ₀p).mpr h⟩

end Cyclotomic

/-- **Chebotarev density theorem** (qualitative form, cyclotomic case), general version:
for `L = ℚ(ζₙ)` and any `σ` in the Galois group, there are infinitely many rational primes `p`
such that `σ` is the Frobenius element at every prime of `𝓞 L` lying over `p` (and at least one
such prime exists). -/
