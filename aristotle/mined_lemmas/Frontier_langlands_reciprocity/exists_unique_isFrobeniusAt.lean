/-
# Langlands Reciprocity
Category: Frontier Abel
Target: Frontier.langlands_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` only because Lean 4 requires every command,
-- including module docstrings, to come after the `import` block.)

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Langlands reciprocity, the `GL(1)` (abelian) base case over `ℚ`

The Langlands reciprocity conjecture predicts, for each `n`, a correspondence

  `n`-dimensional (continuous) representations of the absolute Galois group of a number field
  `K`   ⟷   automorphic representations of `GL(n)` over `K`,

matching the local data on both sides: the Frobenius conjugacy class at an unramified prime `p`
on the Galois side corresponds to the Satake/Hecke parameter at `p` on the automorphic side, so
that the two `L`-functions coincide Euler factor by Euler factor.

We formalize and *prove* the base case `n = 1` over `K = ℚ` — this is abelian reciprocity, i.e.
class field theory for `ℚ` in its cyclotomic form.  Concretely, fix a level `N ≥ 1`.

* Galois side: a one dimensional Galois representation of conductor dividing `N` is a
  homomorphism `ρ : Gal(ℚ(ζ_N)/ℚ) →* ℂˣ`, i.e. a character of the Galois group of the cyclotomic
  field `ℚ(ζ_N)` (equivalently, a character of `Gal(ℚ̄/ℚ)` unramified outside `N` and of
  conductor dividing `N`, since it factors through `Gal(ℚ(ζ_N)/ℚ)`).
* Automorphic side: an automorphic representation of `GL(1)/ℚ` of conductor dividing `N` and
  finite order is a Dirichlet character `χ` modulo `N`, i.e. a term of
  `DirichletCharacter ℂ N`.
* Matching of local data: for a prime `p ∤ N`, the Frobenius element `Frob_p` of
  `Gal(ℚ(ζ_N)/ℚ)` is characterized by `Frob_p ζ = ζ ^ p` (see `Frontier.IsFrobeniusAt`,
  `Frontier.exists_unique_isFrobeniusAt` and, for the link with Mathlib's arithmetic Frobenius
  elements, `Frontier.isArithFrobAt_apply_zeta`), and reciprocity says `ρ (Frob_p) = χ p`.

The main statement is `Frontier.langlands_reciprocity`; `Frontier.langlands_reciprocity_euler`
records the resulting equality of Euler factors of the Artin and Dirichlet `L`-functions.

The key inputs from Mathlib are `IsCyclotomicExtension.autEquivPow` (the cyclotomic character
`Gal(K(ζ_N)/K) ≃* (ZMod N)ˣ`, an isomorphism as soon as the `N`-th cyclotomic polynomial is
irreducible over `K`), `Polynomial.cyclotomic.irreducible_rat` (irreducibility over `ℚ`),
`MulChar.equivToUnitHom` (Dirichlet characters mod `N` are the same as homomorphisms
`(ZMod N)ˣ →* ℂˣ`) and `AlgHom.IsArithFrobAt.apply_of_pow_eq_one` (an arithmetic Frobenius
raises roots of unity of order prime to the residue characteristic to the `q`-th power).
-/

namespace Frontier

open Polynomial IsCyclotomicExtension

/-- The cyclotomic field `ℚ(ζ_N)`. -/
abbrev CyclotomicQ (N : ℕ) := CyclotomicField N ℚ

/-- A fixed primitive `N`-th root of unity in `ℚ(ζ_N)`. -/
noncomputable abbrev zetaQ (N : ℕ) [NeZero N] : CyclotomicQ N :=
  IsCyclotomicExtension.zeta N ℚ (CyclotomicQ N)


theorem exists_unique_isFrobeniusAt (N : ℕ) [NeZero N] {p : ℕ} (hp : Nat.Coprime p N) :
    ∃! σ : CyclotomicQ N ≃ₐ[ℚ] CyclotomicQ N, IsFrobeniusAt N p σ := by
  refine ⟨(cycChar N).symm (ZMod.unitOfCoprime p hp), ?_, ?_⟩
  · show ((cycChar N).symm (ZMod.unitOfCoprime p hp)) (zetaQ N) = zetaQ N ^ p
    have h := cycChar_spec N ((cycChar N).symm (ZMod.unitOfCoprime p hp))
    rw [MulEquiv.apply_symm_apply] at h
    have hval : ((ZMod.unitOfCoprime p hp : ZMod N)).val = p % N := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    rw [hval] at h
    have hord : orderOf (zetaQ N) = N := (zetaQ_spec N).eq_orderOf.symm
    rw [← h]
    conv_rhs => rw [← pow_mod_orderOf (zetaQ N) p, hord]
  · intro τ hτ
    apply (cycChar N).injective
    rw [cycChar_frobenius N hp hτ, MulEquiv.apply_symm_apply]

/-- **The Frobenius elements of `Gal(ℚ(ζ_N)/ℚ)` in the sense of `Frontier.IsFrobeniusAt` are the
arithmetic Frobenius elements of Mathlib.**  If `Q` is a prime of the ring of integers of `ℚ(ζ_N)`
lying over the rational prime `p ∤ N`, then any `σ` which is an arithmetic Frobenius at `Q`
(i.e. `σ x ≡ x ^ p (mod Q)`) raises `N`-th roots of unity to the `p`-th power. -/
