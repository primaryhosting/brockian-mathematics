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

theorem not_dvd_of_isUnit_natCast {n p : ℕ} [NeZero n] (hp : 1 < p)
    (h : IsUnit ((p : ZMod n))) : ¬ p ∣ n := by
  intro hdvd
  have hcop : p.Coprime n := (ZMod.isUnit_iff_coprime p n).mp h
  have hdvd1 : p ∣ Nat.gcd p n := Nat.dvd_gcd dvd_rfl hdvd
  rw [hcop] at hdvd1
  exact hp.ne' (Nat.dvd_one.mp hdvd1)

/-!
## Frobenius elements in cyclotomic extensions of `ℚ`
-/

section Cyclotomic

variable {n : ℕ} [NeZero n] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]

/-- A choice of primitive `n`-th root of unity in `L = ℚ(ζₙ)`. -/
noncomputable abbrev zeta : L := IsCyclotomicExtension.zeta n ℚ L

