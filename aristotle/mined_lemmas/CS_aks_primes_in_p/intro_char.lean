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

lemma intro_char (r : ℕ) (f : (ZMod p)[X]) : Intro p r p f := by
  intro z _
  have key : ((frobenius (AC p) p).comp
        ((aeval z : (ZMod p)[X] →ₐ[ZMod p] AC p) : (ZMod p)[X] →+* AC p))
      = ((aeval (z ^ p) : (ZMod p)[X] →ₐ[ZMod p] AC p) : (ZMod p)[X] →+* AC p) := by
    apply Polynomial.ringHom_ext
    · intro a
      show frobenius (AC p) p (aeval z (C a)) = aeval (z ^ p) (C a)
      simp only [aeval_C, frobenius_def, ← map_pow, ZMod.pow_card]
    · show frobenius (AC p) p (aeval z X) = aeval (z ^ p) X
      simp [frobenius_def]
  have := RingHom.congr_fun key f
  simpa [frobenius_def] using this

end AKS
end CS

import RequestProject.AKS.Aux

/-!
# Correctness of the AKS criterion

The main result of this file is `CS.AKS.prime_of_conditions`: if `n ≥ 2` passes the AKS
conditions for a suitable parameter `r`, then `n` is prime.
-/

open Polynomial

set_option maxHeartbeats 2000000

namespace CS
namespace AKS

variable {p : ℕ} [Fact p.Prime]

/-- Every `n ^ i * p ^ j` is introspective for the products `∏_{a ∈ S} (X + a)`. -/
