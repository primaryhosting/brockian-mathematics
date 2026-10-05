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

theorem exists_isPrime_under_eq_span (L : Type) [Field L] [NumberField L] (p : ℕ)
    (hp : p.Prime) :
    ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Ideal.under ℤ Q = Ideal.span {(p : ℤ)} ∧
      Finite (𝓞 L ⧸ Q) := by
  have hinj := FaithfulSMul.algebraMap_injective ℤ (𝓞 L)
  have hP : (Ideal.span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hp
  obtain ⟨Q, -, hQ1, hQ2⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (R := ℤ) (S := 𝓞 L)
    (Ideal.span {(p : ℤ)}) ⊥ (by
      intro x hx
      have hx' : algebraMap ℤ (𝓞 L) x = 0 := by simpa [Ideal.mem_comap] using hx
      have hx0 : x = 0 := hinj (by simpa using hx')
      simp [hx0])
  exact ⟨Q, hQ1, hQ2, finite_quotient_of_under_eq_span L hp hQ2⟩

/-- If `Q` lies over the rational prime `p` and `p ∤ n`, then `n` is not in `Q`. -/
