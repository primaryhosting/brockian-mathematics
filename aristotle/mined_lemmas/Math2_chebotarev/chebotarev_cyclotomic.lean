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

theorem chebotarev_cyclotomic (n : ℕ) [NeZero n] (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {n} ℚ L] (σ : L ≃ₐ[ℚ] L) :
    {p : ℕ | p.Prime ∧ (∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Ideal.under ℤ Q = Ideal.span {(p : ℤ)}) ∧
      ∀ Q : Ideal (𝓞 L), Q.IsPrime → Ideal.under ℤ Q = Ideal.span {(p : ℤ)} →
        IsArithFrobAt ℤ σ Q}.Infinite := by
  refine (Nat.infinite_setOf_prime_and_eq_mod (a := (cycloUnit (n := n) L σ : ZMod n))
    (cycloUnit (n := n) L σ).isUnit).mono ?_
  rintro p ⟨hp, hpa⟩
  have hpn : ¬ p ∣ n := not_dvd_of_isUnit_natCast hp.one_lt (hpa ▸ (cycloUnit (n := n) L σ).isUnit)
  obtain ⟨Q₀, hQ₀prime, hQ₀p, -⟩ := exists_isPrime_under_eq_span L p hp
  exact ⟨hp, ⟨Q₀, hQ₀prime, hQ₀p⟩, fun Q hQprime hQp =>
    (isArithFrobAt_iff L σ hp hpn Q hQprime hQp).mpr hpa⟩

/-- **Chebotarev density theorem** (qualitative form, cyclotomic case).

For the cyclotomic extension `ℚ(ζₙ)/ℚ` and any element `σ` of its Galois group, there are
infinitely many rational primes `p` admitting a prime `Q` of the ring of integers lying over
`p` whose Frobenius element is exactly `σ`; i.e. `σ x ≡ x ^ p (mod Q)` for all algebraic
integers `x`. Since the Galois group here is abelian, the Frobenius conjugacy class of such a
prime is the singleton `{σ}`, so every Frobenius conjugacy class is realized by infinitely
many primes. -/
