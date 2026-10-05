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

theorem isArithFrobAt_iff (σ : L ≃ₐ[ℚ] L) {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n)
    (Q : Ideal (𝓞 L)) (hQprime : Q.IsPrime)
    (hQp : Ideal.under ℤ Q = Ideal.span {(p : ℤ)}) :
    IsArithFrobAt ℤ σ Q ↔ (p : ZMod n) = (cycloUnit (n := n) L σ : ZMod n) := by
  have hζ := isPrimitiveRoot_zeta (n := n) L
  set m : ℕ := ((cycloUnit (n := n) L σ : ZMod n)).val with hmdef
  have hmcast : ((m : ℕ) : ZMod n) = (cycloUnit (n := n) L σ : ZMod n) :=
    ZMod.natCast_zmod_val _
  have hσζ : zeta (n := n) L ^ m = σ (zeta (n := n) L) := zeta_pow_cycloUnit (n := n) L σ
  constructor
  · intro H
    have h1 : σ (zeta (n := n) L) = zeta (n := n) L ^ p :=
      apply_zeta_eq_pow_of_isArithFrobAt L hQp hpn H
    have h2 : zeta (n := n) L ^ (p % n) = zeta (n := n) L ^ (m % n) := by
      rw [pow_eq_pow_of_modEq hζ.pow_eq_one (Nat.mod_modEq p n),
        pow_eq_pow_of_modEq hζ.pow_eq_one (Nat.mod_modEq m n), ← h1, hσζ]
    have h3 : p % n = m % n :=
      hζ.pow_inj (Nat.mod_lt _ (NeZero.pos n)) (Nat.mod_lt _ (NeZero.pos n)) h2
    have : ((p : ℕ) : ZMod n) = ((m : ℕ) : ZMod n) := (ZMod.natCast_eq_natCast_iff p m n).mpr h3
    rw [this, hmcast]
  · intro h
    have hpm : p ≡ m [MOD n] := (ZMod.natCast_eq_natCast_iff p m n).mp (by rw [h, hmcast])
    refine isArithFrobAt_of_zeta_pow L σ hp hpn ?_ Q hQprime hQp
    rw [← hσζ]
    exact (pow_eq_pow_of_modEq hζ.pow_eq_one hpm).symm

/-- The set of primes whose Frobenius (at some, equivalently any, prime above it) is `σ`,
away from the primes dividing `n`, is the set of primes in the residue class attached to `σ`. -/
