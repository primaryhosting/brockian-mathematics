import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the file layout: Lean 4 requires `import` to be the very first command of a file, so the
header comment above is placed immediately after the single `import Mathlib` line.

# Chebotarev density theorem for Frobenius conjugacy classes

We prove the Chebotarev density theorem, in its "infinitude" form, for cyclotomic extensions of
`ℚ`: if `K = ℚ(ζₙ)` and `σ ∈ Gal(K/ℚ)`, then there are infinitely many rational primes `p`
admitting a prime `Q` of `𝓞 K` above `p` at which `σ` is an arithmetic Frobenius element, i.e.
`σ • x ≡ x ^ #(ℤ/(p)) (mod Q)` for all `x ∈ 𝓞 K` (Mathlib's `IsArithFrobAt`).  Since `Gal(K/ℚ)` is
abelian in this case, the conjugacy class of `σ` is `{σ}`, so this says precisely that every
Frobenius conjugacy class is hit by infinitely many primes.

The two main external inputs are:
* `Nat.infinite_setOf_prime_and_eq_mod` (Dirichlet's theorem on primes in arithmetic
  progressions), which is the analytic input, and
* `IsCyclotomicExtension.Rat.adjoin_singleton_eq_top` (`𝓞 ℚ(ζₙ) = ℤ[ζₙ]`), which lets us identify
  the Galois action modulo `Q` with the `p`-th power map.
-/

open NumberField IsCyclotomicExtension

namespace Math2

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {n} ℚ K]

/-- The `p`-th power map on the residue ring `𝓞 K ⧸ Q`, precomposed with the reduction map,
as a `ℤ`-algebra map `𝓞 K → 𝓞 K ⧸ Q`. It is a ring homomorphism because `𝓞 K ⧸ Q` has
characteristic `p`. -/

lemma powFrobHom_apply (p : ℕ) (hp : p.Prime) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    (hpQ : (p : 𝓞 K) ∈ Q) (x : 𝓞 K) :
    powFrobHom p hp Q hpQ x = Ideal.Quotient.mk Q (x ^ p) := by
  simp [powFrobHom, frobenius_def]

omit [IsCyclotomicExtension {n} ℚ K] in
