import Mathlib

/-!
# Langlands Reciprocity
Category: Frontier Abel
Target: Frontier.langlands_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Frontier

open Polynomial IsCyclotomicExtension

variable (n : ℕ) [NeZero n] (L : Type*) [Field L] [Algebra ℚ L]
  [IsCyclotomicExtension {n} ℚ L]

/-- **The Artin reciprocity map** for the cyclotomic extension `ℚ(ζ_n)/ℚ`:
the isomorphism from the idele class group of conductor `n`, namely `(ZMod n)ˣ`,
onto the Galois group `Gal(ℚ(ζ_n)/ℚ)`. -/

theorem artinMap_frobenius (p : ℕ) (hp : Nat.Coprime p n) (σ : L ≃ₐ[ℚ] L)
    (hσ : ∀ x : L, x ^ n = 1 → σ x = x ^ p) :
    σ = artinMap n L (ZMod.unitOfCoprime p hp) := by
  refine aut_ext n L (fun x hx => ?_)
  rw [hσ x hx, artinMap_apply_root_of_unity n L _ x hx]
  have hval : ((ZMod.unitOfCoprime p hp : (ZMod n)ˣ) : ZMod n).val = p % n := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  rw [hval]
  conv_lhs => rw [← Nat.div_add_mod p n]
  rw [pow_add, pow_mul, hx, one_pow, one_mul]

/--
**Langlands reciprocity for `GL(1)` over `ℚ`** (the abelian case of the Langlands
correspondence, i.e. Artin reciprocity), for the cyclotomic extension `ℚ(ζ_n)/ℚ`.

The statement has three parts.

1. *Reciprocity (Artin map).* There is a canonical isomorphism
   `(ZMod n)ˣ ≃* Gal(ℚ(ζ_n)/ℚ)`, normalised so that the class of `a` acts on every
   `n`-th root of unity by `x ↦ x ^ a`. This is the automorphic-to-Galois transfer of
   conductor `n` on the level of groups.

2. *The correspondence.* Transport along the Artin map is a bijection between the
   one-dimensional (complex) Galois representations of `Gal(ℚ(ζ_n)/ℚ)`, i.e. the
   Artin characters of conductor dividing `n`, and the automorphic representations of
   `GL(1)` of conductor dividing `n`, i.e. the Dirichlet characters mod `n`.

3. *Local–global compatibility at unramified primes.* If `p` is a prime not dividing `n`
   and `σ` is a Frobenius element at `p` (an automorphism acting on `n`-th roots of unity
   by `x ↦ x ^ p`), then for every Galois character `ρ`, the value `ρ σ` of `ρ` at
   Frobenius equals the value at `p` of the associated Dirichlet character. Hence the
   two `L`-functions have the same Euler factors at all unramified primes.
-/
