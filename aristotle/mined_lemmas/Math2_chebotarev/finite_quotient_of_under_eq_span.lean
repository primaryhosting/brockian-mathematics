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

theorem finite_quotient_of_under_eq_span (L : Type) [Field L] [NumberField L] {p : ℕ}
    (hp : p.Prime) {Q : Ideal (𝓞 L)} (hQp : Ideal.under ℤ Q = Ideal.span {(p : ℤ)}) :
    Finite (𝓞 L ⧸ Q) := by
  have hinj := FaithfulSMul.algebraMap_injective ℤ (𝓞 L)
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have hmem : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.subset_span rfl
    rw [← hQp, Ideal.mem_comap] at hmem
    simp only [Ideal.mem_bot] at hmem
    have : (p : ℤ) = 0 := hinj (by simpa using hmem)
    exact hp.ne_zero (by exact_mod_cast this)
  exact Ideal.finiteQuotientOfFreeOfNeBot Q hne

/-- Over a number field `L`, every rational prime `p` lies under some prime ideal `Q`
of the ring of integers, and the residue ring `𝓞 L ⧸ Q` is finite. -/
