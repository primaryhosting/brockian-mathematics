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

theorem smul_sub_pow_mem (σ : Gal(K/ℚ)) {p : ℕ} (hp : p.Prime)
    (hpa : (p : ZMod n) = (Rat.galEquivZMod n K σ : ZMod n))
    (Q : Ideal (𝓞 K)) [Q.IsPrime] (hpQ : (p : 𝓞 K) ∈ Q) (x : 𝓞 K) :
    σ • x - x ^ p ∈ Q := by
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ K
  have key : galQuotHom σ Q = powFrobHom p hp Q hpQ := by
    refine AlgHom.ext_of_adjoin_eq_top (Rat.adjoin_singleton_eq_top hζ) ?_
    rintro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    rw [galQuotHom_apply, powFrobHom_apply,
      Rat.galEquivZMod_smul_of_pow_eq n K σ hζ.toInteger_isPrimitiveRoot.pow_eq_one]
    congr 1
    have hord : orderOf hζ.toInteger = n := (hζ.toInteger_isPrimitiveRoot.eq_orderOf).symm
    rw [(hζ.toInteger_isPrimitiveRoot.isOfFinOrder (NeZero.ne n)).pow_inj_mod, hord]
    have hcast : (((Rat.galEquivZMod n K σ : ZMod n).val : ℕ) : ZMod n) = (p : ZMod n) := by
      rw [hpa, ZMod.natCast_val, ZMod.cast_id]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hcast
  have h2 := congrArg (fun f => f x) key
  simp only [powFrobHom_apply] at h2
  exact (Ideal.Quotient.eq).1 h2

/-- **Chebotarev density theorem** (infinitude form) for the cyclotomic extension `K = ℚ(ζₙ)` of
`ℚ`: every element `σ` of `Gal(K/ℚ)` is an arithmetic Frobenius element at infinitely many
primes.  Precisely, for infinitely many rational primes `p` there is a prime `Q` of the ring of
integers `𝓞 K` lying over `p` such that `σ` is an arithmetic Frobenius at `Q`, i.e.
`σ • x ≡ x ^ #(ℤ/(p)) (mod Q)` for all `x ∈ 𝓞 K`.

As `Gal(ℚ(ζₙ)/ℚ)` is abelian, the conjugacy class of `σ` is `{σ}`, so this is exactly the
statement that each Frobenius conjugacy class occurs for infinitely many primes. -/
