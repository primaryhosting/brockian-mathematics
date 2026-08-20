/-
# Langlands Reciprocity
Category: Frontier Abel
Target: Frontier.langlands_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring, so the header above is
-- repeated as the module docstring immediately after the import.)
import Mathlib

/-!
# Langlands Reciprocity
Category: Frontier Abel
Target: Frontier.langlands_reciprocity
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

set_option grind.warning false

/-!
## Overview

Langlands reciprocity predicts a correspondence between `n`-dimensional (continuous)
representations of the absolute Galois group of a number field and automorphic
representations of `GL n` over that field, matching the local data (Frobenius
eigenvalues on the Galois side, Hecke eigenvalues / Satake parameters on the
automorphic side) and hence matching `L`-functions.

The abelian case `n = 1` over `ℚ` is Artin reciprocity: automorphic representations of
`GL 1` over `ℚ` of finite order and conductor dividing `N` are exactly the Dirichlet
characters mod `N`, and the correspondence attaches to a Dirichlet character `χ` the
Galois character `χ ∘ (mod N cyclotomic character)`.

This file formalizes that abelian statement and proves it at a fixed level `N`:

* `Frontier.galoisCharOfDirichlet` : the reciprocity map, automorphic ⟶ Galois.
* `Frontier.langlands_reciprocity` : the main theorem. At level `N` the reciprocity map
  is a bijection from Dirichlet characters mod `N` onto the Galois characters that are
  trivial on the kernel of the mod `N` cyclotomic character (i.e. those unramified
  outside `N`, cut out by the `N`-th cyclotomic field), it matches Frobenius eigenvalues
  with Hecke eigenvalues, and hence it matches `L`-functions.
* `Frontier.LanglandsReciprocityGL1` : the statement of the conjecture in the abelian
  case over `ℚ`, for *all* continuous characters at once.
* `Frontier.langlands_reciprocity_gl1_of_kroneckerWeber` : a Lean-checked reduction of
  that conjecture to the Kronecker–Weber property (every continuous character of the
  absolute Galois group of `ℚ` is trivial on the kernel of some mod `N` cyclotomic
  character).
-/

namespace Frontier

open Polynomial

/-- A fixed algebraic closure of `ℚ`. -/
noncomputable abbrev QBar : Type := AlgebraicClosure ℚ

/-- The absolute Galois group `Gal(ℚ̄/ℚ)`, with its Krull topology. -/
abbrev GalQ : Type := QBar ≃ₐ[ℚ] QBar

/-- There are exactly `N` `N`-th roots of unity in `ℚ̄`. -/

theorem pow_eq_pow_of_modEq {n i j : ℕ} {z : QBar} (hz : IsPrimitiveRoot z n)
    (h : i ≡ j [MOD n]) : z ^ i = z ^ j := by
  rw [← Nat.mod_add_div i n, ← Nat.mod_add_div j n, pow_add, pow_add, pow_mul, pow_mul,
    hz.pow_eq_one, one_pow, one_pow, mul_one, mul_one, h]

/-- Being a Frobenius element at `m` means exactly acting on the `N`-th roots of unity by
`ζ ↦ ζ ^ m`, which for a prime `p ∤ N` is the usual arithmetic Frobenius of the cyclotomic
extension. -/
