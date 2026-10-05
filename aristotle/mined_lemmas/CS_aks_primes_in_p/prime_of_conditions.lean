import Mathlib

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

import RequestProject.AKS.Defs

/-!
# Introspective exponents

Fix a prime `p` and let `F = AlgebraicClosure (ZMod p)`.  A natural number `m` is
*introspective* for a polynomial `f ∈ 𝔽ₚ[X]` (relative to `r`) if `f(z)^m = f(z^m)` for every
`r`-th root of unity `z ∈ F`.  This is the key notion in the AKS correctness proof.
-/

open Polynomial

namespace CS
namespace AKS

/-- The algebraic closure of `𝔽ₚ`, the field in which the AKS argument takes place. -/
abbrev AC (p : ℕ) [Fact p.Prime] := AlgebraicClosure (ZMod p)

variable {p : ℕ} [Fact p.Prime]

/-- `m` is introspective for `f`: `f(z)^m = f(z^m)` for all `r`-th roots of unity `z`. -/

theorem prime_of_conditions {n r : ℕ} (hn : 2 ≤ n) (hr1 : 1 ≤ r) (hrn : r < n)
    (hcop : ∀ a, 1 ≤ a → a ≤ r → Nat.gcd a n = 1)
    (hord : 4 * blog n ^ 2 < orderOf (n : ZMod r))
    (hpp : ¬ IsPerfectPower n)
    (hpoly : ∀ a ≤ 2 * blog n * Nat.sqrt (Nat.totient r), PolyCond n r a) :
    n.Prime := by
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := exists_pow_of_conditions hp hpn hn hr1 hrn hcop hord hpoly
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · simp at hk; omega
    · rw [pow_one] at hk; rwa [← hk] at hp
  · exact absurd ⟨p, k, hk2, hk.symm⟩ hpp

end AKS
end CS

import RequestProject.AKS.Intro

/-!
# Auxiliary algebraic lemmas for the AKS correctness proof
-/

open Polynomial

namespace CS
namespace AKS

variable {p : ℕ} [Fact p.Prime]

/-- If `p ∤ r` then the algebraic closure of `𝔽ₚ` contains a primitive `r`-th root of unity. -/
