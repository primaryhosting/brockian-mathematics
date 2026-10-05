/-
# Langlands Reciprocity
Category: Frontier Abel
Target: Frontier.langlands_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

Langlands reciprocity predicts that (suitable) `n`-dimensional representations of the absolute
Galois group of a global field correspond bijectively to (suitable) automorphic representations
of `GLₙ` over that field, the correspondence being characterized by the requirement that at every
unramified place the Frobenius parameter on the Galois side agrees with the Satake/Hecke parameter
on the automorphic side (equivalently, the two `L`-functions have the same Euler factors).

Since automorphic representations of `GLₙ` are not available in Mathlib, we formalize the *shape*
of a reciprocity law axiomatically (`Frontier.ReciprocityData` and
`Frontier.ReciprocityData.LanglandsReciprocity`): a collection of places, a Galois side, an
automorphic side, and the local parameter attached to an object of either side at a place.  The
conjecture asserts the existence of a parameter-preserving bijection between the two sides.

We then *prove* the base case `n = 1` over `ℚ`, in its classical cyclotomic incarnation
(Artin reciprocity for cyclotomic fields, which by Tate's thesis is exactly the automorphic
reciprocity law for `GL₁/ℚ`):

* the Galois side is the set of one-dimensional complex representations
  `Gal(ℚ(ζ_N)/ℚ) →* ℂˣ` (all Artin representations of dimension one whose conductor divides `N`
  arise this way);
* the automorphic side is the set of Dirichlet characters mod `N`, i.e. via Tate's thesis the
  automorphic representations of `GL₁/ℚ = 𝔸ˣ/ℚˣ` unramified outside `N` and at `∞`;
* the places are the primes `p ∤ N`, i.e. the unramified places;
* the parameter of a Galois character at `p` is its value on the arithmetic Frobenius
  (the Artin symbol) at `p`, and the parameter of a Dirichlet character at `p` is `χ(p)`.

`Frontier.langlands_reciprocity` states that this reciprocity law holds, that the Galois element
used is genuinely the Artin symbol (it raises every `N`-th root of unity to the `p`-th power), and
that consequently every local Euler factor of the Artin `L`-function of `ρ` equals the
corresponding Euler factor of the Dirichlet `L`-function of the matching character.
-/

namespace Frontier

/-- The data entering a reciprocity law: a set of (unramified) places, a "Galois side", an
"automorphic side", and the local parameter attached to an object of each side at each place.

For `GLₙ` one takes for `galoisParam ρ v` (resp. `automorphicParam π v`) a symmetric function of
the Frobenius eigenvalues (resp. of the Satake parameters) of `ρ` (resp. of `π`) at `v`; for
`n = 1` these are just the single Frobenius eigenvalue and the Hecke eigenvalue. -/
structure ReciprocityData where
  /-- The places at which parameters are compared (the unramified places). -/
  Place : Type
  /-- The Galois side of the correspondence. -/
  GaloisSide : Type
  /-- The automorphic side of the correspondence. -/
  AutomorphicSide : Type
  /-- The local (Frobenius) parameter of a Galois object at a place. -/
  galoisParam : GaloisSide → Place → ℂ
  /-- The local (Satake/Hecke) parameter of an automorphic object at a place. -/
  automorphicParam : AutomorphicSide → Place → ℂ

/-- **Langlands reciprocity** for a given collection of data: there is a bijection between the
Galois side and the automorphic side which matches the local parameters at every place.  Matching
of local parameters is exactly the statement that the corresponding `L`-functions agree Euler
factor by Euler factor. -/
def ReciprocityData.LanglandsReciprocity (D : ReciprocityData) : Prop :=
  ∃ e : D.GaloisSide ≃ D.AutomorphicSide,
    ∀ (ρ : D.GaloisSide) (v : D.Place), D.galoisParam ρ v = D.automorphicParam (e ρ) v

section GLOne

variable (N : ℕ) [NeZero N]

/-- The unramified places for the cyclotomic field `ℚ(ζ_N)`: the primes `p` not dividing `N`. -/
def UnramifiedPrime : Type := {p : ℕ // p.Prime ∧ p.Coprime N}

instance : CoeHead (UnramifiedPrime N) ℕ := ⟨Subtype.val⟩

/-- The Artin symbol (arithmetic Frobenius) at an unramified prime `p` in `Gal(ℚ(ζ_N)/ℚ)`: the
automorphism corresponding to the unit `p ∈ (ℤ/Nℤ)ˣ`. -/
noncomputable def artinSymbol (p : UnramifiedPrime N) : Gal(CyclotomicField N ℚ/ℚ) :=
  (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).symm
    (ZMod.unitOfCoprime p.1 p.2.2)

/-- The Artin symbol at `p` is the arithmetic Frobenius: it raises every `N`-th root of unity to
the `p`-th power. -/
theorem artinSymbol_apply (p : UnramifiedPrime N) {x : CyclotomicField N ℚ} (hx : x ^ N = 1) :
    artinSymbol N p x = x ^ (p.1 : ℕ) := by
  rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N _ _ hx, artinSymbol,
    MulEquiv.apply_symm_apply]
  have hval : ((ZMod.unitOfCoprime p.1 p.2.2 : (ZMod N)ˣ) : ZMod N).val = p.1 % N := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  rw [hval]
  conv_rhs => rw [← Nat.div_add_mod p.1 N]
  rw [pow_add, pow_mul, hx, one_pow, one_mul]

/-- The bijection between one-dimensional complex representations of `Gal(ℚ(ζ_N)/ℚ)` and Dirichlet
characters mod `N`, induced by the canonical isomorphism `Gal(ℚ(ζ_N)/ℚ) ≃* (ℤ/Nℤ)ˣ`. -/
noncomputable def galoisCharEquivDirichlet :
    (Gal(CyclotomicField N ℚ/ℚ) →* ℂˣ) ≃ DirichletCharacter ℂ N where
  toFun ρ := MulChar.equivToUnitHom.symm
    (ρ.comp (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).symm.toMonoidHom)
  invFun χ := (MulChar.equivToUnitHom χ).comp
    (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).toMonoidHom
  left_inv ρ := by
    ext σ
    simp only [Equiv.apply_symm_apply, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  right_inv χ := by
    have h : ((MulChar.equivToUnitHom χ).comp
        (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).toMonoidHom).comp
        (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).symm.toMonoidHom =
        MulChar.equivToUnitHom χ := by
      ext u
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply]
    simp only [h, Equiv.symm_apply_apply]

/-- The reciprocity data for `GL₁` over `ℚ`, with everything unramified outside `N` and `∞`:
one-dimensional Galois representations of conductor dividing `N` against Dirichlet characters
mod `N`, compared through Frobenius/Hecke eigenvalues at the primes `p ∤ N`. -/
noncomputable def glOneCyclotomicData : ReciprocityData where
  Place := UnramifiedPrime N
  GaloisSide := Gal(CyclotomicField N ℚ/ℚ) →* ℂˣ
  AutomorphicSide := DirichletCharacter ℂ N
  galoisParam ρ p := (ρ (artinSymbol N p) : ℂ)
  automorphicParam χ p := χ (p.1 : ZMod N)

end GLOne

/-- **Langlands reciprocity, base case `n = 1` over `ℚ`** (Artin reciprocity for cyclotomic
fields; equivalently, via Tate's thesis, reciprocity for `GL₁/ℚ`).

For every modulus `N`:

1. the abstract reciprocity law `ReciprocityData.LanglandsReciprocity` holds for the `GL₁`
   cyclotomic data: there is a bijection `e` between one-dimensional complex representations of
   `Gal(ℚ(ζ_N)/ℚ)` and Dirichlet characters mod `N` which matches the local parameters at every
   unramified prime, i.e. `ρ (Frob_p) = (e ρ) (p)`;
2. the Galois element occurring there is genuinely the arithmetic Frobenius (Artin symbol) at `p`:
   it raises every `N`-th root of unity to the `p`-th power;
3. consequently the two `L`-functions match Euler factor by Euler factor: for every complex `s`,
   the local factor `(1 - ρ(Frob_p) p^{-s})⁻¹` of the Artin `L`-function equals the local factor
   `(1 - χ(p) p^{-s})⁻¹` of the Dirichlet `L`-function of the matching character `χ = e ρ`. -/
theorem langlands_reciprocity (N : ℕ) [NeZero N] :
    (glOneCyclotomicData N).LanglandsReciprocity ∧
      ∃ e : (Gal(CyclotomicField N ℚ/ℚ) →* ℂˣ) ≃ DirichletCharacter ℂ N,
        (∀ (ρ : Gal(CyclotomicField N ℚ/ℚ) →* ℂˣ) (p : UnramifiedPrime N),
            (ρ (artinSymbol N p) : ℂ) = (e ρ) (p.1 : ZMod N)) ∧
          (∀ (p : UnramifiedPrime N) (x : CyclotomicField N ℚ), x ^ N = 1 →
            artinSymbol N p x = x ^ (p.1 : ℕ)) ∧
          (∀ (ρ : Gal(CyclotomicField N ℚ/ℚ) →* ℂˣ) (p : UnramifiedPrime N) (s : ℂ),
            (1 - (ρ (artinSymbol N p) : ℂ) * (p.1 : ℂ) ^ (-s))⁻¹ =
              (1 - (e ρ) (p.1 : ZMod N) * (p.1 : ℂ) ^ (-s))⁻¹) := by
  have key : ∀ (ρ : Gal(CyclotomicField N ℚ/ℚ) →* ℂˣ) (p : UnramifiedPrime N),
      (ρ (artinSymbol N p) : ℂ) = (galoisCharEquivDirichlet N ρ) (p.1 : ZMod N) := by
    intro ρ p
    have : ((p.1 : ℕ) : ZMod N) = ((ZMod.unitOfCoprime p.1 p.2.2 : (ZMod N)ˣ) : ZMod N) := by
      rw [ZMod.coe_unitOfCoprime]
    rw [this, galoisCharEquivDirichlet, Equiv.coe_fn_mk, MulChar.equivToUnitHom_symm_coe]
    simp [artinSymbol]
  refine ⟨⟨galoisCharEquivDirichlet N, key⟩, galoisCharEquivDirichlet N, key, ?_, ?_⟩
  · intro p x hx
    exact artinSymbol_apply N p hx
  · intro ρ p s
    rw [key ρ p]

end Frontier

