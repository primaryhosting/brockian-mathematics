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

lemma intro_prod_family {n r L : ℕ} (hpn : p ∣ n)
    (hpoly : ∀ a ≤ L, PolyCond n r a) {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 L) (i j : ℕ) :
    Intro p r (n ^ i * p ^ j) (∏ a ∈ S, (X + C (a : ZMod p))) := by
  refine intro_prod S _ (fun a ha => ?_)
  have haL : a ≤ L := by
    have := hS ha
    simp only [Finset.mem_Icc] at this
    omega
  exact ((intro_n_X_add_C hpn (hpoly a haL)).pow i).mul_exp ((intro_char r _).pow j)

/-- The key step of the AKS correctness proof: if `n` satisfies the AKS conditions for the
parameter `r` and `p` is a prime factor of `n`, then `n` is a power of `p`. -/
