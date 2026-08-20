/-
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` commands to come first in a file, so the module docstring version of
-- the header above is repeated immediately after the imports.)

import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open NumberField

/-- A cyclotomic extension of `ℚ` is Galois. -/

theorem aut_eq_of_pow_congr (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (σ τ : 𝓞 K ≃ₐ[ℤ] 𝓞 K) {i j : ℕ}
    (hi : σ hζ.toInteger = hζ.toInteger ^ i) (hj : τ hζ.toInteger = hζ.toInteger ^ j)
    (hij : (i : ZMod n) = (j : ZMod n)) : σ = τ := by
  have hz : IsPrimitiveRoot hζ.toInteger n := hζ.toInteger_isPrimitiveRoot
  have key : ∀ m : ℕ, hζ.toInteger ^ m = hζ.toInteger ^ (m % n) := by
    intro m
    conv_lhs => rw [← Nat.div_add_mod m n]
    rw [pow_add, pow_mul, hz.pow_eq_one, one_pow, one_mul]
  refine aut_ext_of_primitiveRoot n K hζ σ τ ?_
  rw [hi, hj, key i, key j, (ZMod.natCast_eq_natCast_iff _ _ _).mp hij]

/-- **Chebotarev density theorem** (cyclotomic case, in the qualitative "infinitely many primes"
form).

Let `K = ℚ(ζₙ)` be a cyclotomic field and let `σ` be any element of its Galois group,
realized as `Aut(𝓞 K / ℤ) ≃ Gal(K/ℚ)`.  Then there are infinitely many rational primes `p`
admitting a prime ideal `Q` of `𝓞 K` lying over `p` (i.e. `Q ∩ ℤ = pℤ`) whose Frobenius element
is `σ`, i.e. `σ x ≡ x ^ p (mod Q)` for all `x ∈ 𝓞 K`.

Since the Galois group of a cyclotomic field is abelian, the conjugacy class of `σ` is `{σ}`, so
this says precisely that every Frobenius conjugacy class of `Gal(ℚ(ζₙ)/ℚ)` is the Frobenius class
of infinitely many primes.  The proof deduces this from Dirichlet's theorem on primes in
arithmetic progressions, via the identification of the Frobenius at `p` with `ζ ↦ ζ ^ p`. -/
