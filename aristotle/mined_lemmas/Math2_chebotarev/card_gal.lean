/-
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

open ArithmeticFunction Complex Filter Topology

/-! ### The analytic input: Λ-weighted density of a residue class -/

/-- The terms of the `L`-series of the von Mangoldt function restricted to a residue class,
evaluated at a real point, are real. -/

theorem card_gal (q : ℕ) [NeZero q] :
    Nat.card (CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) = q.totient := by
  have e := IsCyclotomicExtension.autEquivPow (n := q) (K := ℚ) (CyclotomicField q ℚ)
    (irreducible_cyclotomic_rat q)
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-! ### Chebotarev -/

/-- **Chebotarev density theorem** for the cyclotomic extension `ℚ(ζ_q)/ℚ`:
for every element `σ` of the Galois group `G`, the set of primes whose Frobenius is `σ`
(i.e. the primes `p` at which `σ` acts on the `q`-th roots of unity as `x ↦ x ^ p`) has
Dirichlet density equal to the relative size `|C| / |G|` of the conjugacy class `C` of `σ`.

The density is taken in the von Mangoldt weighted analytic sense: writing `S` for the set of
primes in question, `(s - 1) * ∑' p ∈ S, Λ p / p ^ s → |C| / |G|` as `s → 1⁺` along the reals.
Ramified primes (those dividing `q`) are automatically excluded, since for them no `σ`
satisfies the Frobenius condition. -/
