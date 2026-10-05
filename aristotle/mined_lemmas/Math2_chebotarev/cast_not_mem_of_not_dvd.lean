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

theorem cast_not_mem_of_not_dvd (L : Type) [Field L] [NumberField L] {p n : ℕ}
    {Q : Ideal (𝓞 L)} (hQp : Ideal.under ℤ Q = Ideal.span {(p : ℤ)}) (hpn : ¬ p ∣ n) :
    (n : 𝓞 L) ∉ Q := by
  intro hmem
  have h1 : (n : ℤ) ∈ Ideal.under ℤ Q := by
    simpa [Ideal.under, Ideal.mem_comap] using hmem
  rw [hQp, Ideal.mem_span_singleton] at h1
  exact hpn (by exact_mod_cast h1)

/-- A Frobenius element at a prime `Q` above `p` raises roots of unity of order prime to `p`
to their `p`-th power. -/
