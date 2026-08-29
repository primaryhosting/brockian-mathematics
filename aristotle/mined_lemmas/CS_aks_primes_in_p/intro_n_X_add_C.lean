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

lemma intro_n_X_add_C {n r a : ℕ} (hpn : p ∣ n) (h : PolyCond n r a) :
    Intro p r n (X + C (a : ZMod p)) := by
  classical
  haveI : CharP (ZMod p) p := ZMod.charP p
  rw [PolyCond] at h
  set φ : ZMod n →+* ZMod p := ZMod.castHom hpn (ZMod p) with hφ
  have hmap : ((X : (ZMod p)[X]) ^ r - 1) ∣
      ((X + C (a : ZMod p)) ^ n - (X ^ n + C (a : ZMod p))) := by
    have := Polynomial.map_dvd φ h
    simpa [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_one,
      Polynomial.map_X, Polynomial.map_C, hφ, map_natCast] using this
  intro z hz
  obtain ⟨c, hc⟩ := hmap
  have : (z + (a : AC p)) ^ n - (z ^ n + (a : AC p)) = 0 := by
    have := congrArg (fun q => Polynomial.aeval z q) hc
    simp only [map_sub, map_add, map_pow, aeval_X, aeval_C, map_one, map_mul] at this
    rw [hz] at this
    simpa using this
  have h2 : (z + (a : AC p)) ^ n = z ^ n + (a : AC p) := by linear_combination this
  simpa using h2

end AKS
end CS

import Mathlib

/-!
# The AKS primality test: definitions

This file sets up the AKS ("PRIMES is in P") algorithm of Agrawal, Kayal and Saxena
as a predicate on natural numbers, together with its parameters.
-/

open Polynomial

namespace CS
namespace AKS

/-- `blog n = ⌊log₂ n⌋ + 1`, the bit length of `n`; an integer upper bound for `log₂ n`. -/
