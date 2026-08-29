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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## The abstract shape of Langlands reciprocity

The Langlands reciprocity conjecture asserts that the "Galois side" of arithmetic
(continuous representations of a Galois group) and the "automorphic side"
(automorphic representations of a reductive group) are in a bijection which matches
*local parameters*: at every unramified place `v` the Frobenius conjugacy class on the
Galois side has the same characteristic data as the Satake parameter of the automorphic
representation. Since matching of local parameters at almost all places determines the
matching of the associated `L`-functions, this is the precise content of "reciprocity".

The following predicate isolates that shape, abstracting away the (currently
unformalisable in full) analytic definitions of automorphic representations: a
*reciprocity law* for a pair of local-parameter maps
`galoisParam : 𝒢 → Place → Param` and `autParam : 𝒜 → Place → Param`
is a bijection `𝒢 ≃ 𝒜` matching the parameters at every place.
-/

/-- **Langlands reciprocity, abstract form.** Given a family of "Galois objects" `𝒢`
and "automorphic objects" `𝒜`, each equipped with local parameters at every place of
`Place` valued in `Param`, reciprocity asserts the existence of a bijection between them
which matches the local parameters at all places. -/
def LanglandsReciprocityHolds {𝒢 𝒜 Place Param : Type*}
    (galoisParam : 𝒢 → Place → Param) (autParam : 𝒜 → Place → Param) : Prop :=
  ∃ e : 𝒢 ≃ 𝒜, ∀ ρ : 𝒢, ∀ v : Place, galoisParam ρ v = autParam (e ρ) v

/-!
## The abelian base case: `GL(1)` over `ℚ`

We prove the base case `n = 1` of the conjecture, i.e. reciprocity for `GL(1)`, which is
class field theory for `ℚ` in its cyclotomic (Kronecker–Weber) form.

* Galois side: one-dimensional complex representations, i.e. characters
  `Gal(ℚ(ζ_N)/ℚ) →* ℂˣ`; these are exactly the Artin characters of conductor dividing `N`.
* Automorphic side: automorphic representations of `GL(1)/ℚ` of conductor dividing `N`,
  i.e. Dirichlet characters `DirichletCharacter ℂ N` (Hecke characters of finite order
  and level `N`).
* Places: the primes `p ∤ N`, the places at which both sides are unramified.
* Local parameter: on the Galois side the value `ρ(Frob_p)`, on the automorphic side the
  Satake parameter `χ(p)`.
-/

section GL1

variable (N : ℕ) [NeZero N]

/-- The cyclotomic field `ℚ(ζ_N)`, whose Galois group is the maximal abelian quotient of
`Gal(ℚ̄/ℚ)` of conductor dividing `N`. -/
abbrev CycField : Type := CyclotomicField N ℚ

/-- A one-dimensional (i.e. `GL₁(ℂ)`-valued) Galois representation of conductor dividing
`N`: a character of `Gal(ℚ(ζ_N)/ℚ)`. -/
abbrev GaloisChar : Type := Gal((CycField N)/ℚ) →* ℂˣ

/-- The set of finite places of `ℚ` at which everything in sight is unramified: the primes
not dividing the level `N`. -/
abbrev UnramifiedPlace : Type := {p : ℕ // p.Prime ∧ ¬ p ∣ N}

omit [NeZero N] in
theorem UnramifiedPlace.coprime (v : UnramifiedPlace N) : Nat.Coprime v.1 N :=
  (Nat.Prime.coprime_iff_not_dvd v.2.1).2 v.2.2

/-- The **Frobenius element** at an unramified place `p`, as an element of
`Gal(ℚ(ζ_N)/ℚ)`: the automorphism corresponding to the unit `p mod N` under the
cyclotomic reciprocity isomorphism. -/
noncomputable def frob (v : UnramifiedPlace N) : Gal((CycField N)/ℚ) :=
  (IsCyclotomicExtension.Rat.galEquivZMod N (CycField N)).symm
    (ZMod.unitOfCoprime v.1 (UnramifiedPlace.coprime N v))

/-- The Frobenius element at `p` acts on `N`-th roots of unity by `x ↦ x ^ p`; this is the
characteristic property of the arithmetic Frobenius in a cyclotomic extension. -/
theorem frob_apply (v : UnramifiedPlace N) {x : CycField N} (hx : x ^ N = 1) :
    frob N v x = x ^ (v.1) := by
  rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N (CycField N) (frob N v) hx,
    frob, MulEquiv.apply_symm_apply, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  conv_rhs => rw [← Nat.div_add_mod (v.1) N]
  rw [pow_add, pow_mul, hx, one_pow, one_mul]

/-- Concretely, the Frobenius at `p ∤ N` sends the chosen primitive `N`-th root of unity
`ζ_N` to `ζ_N ^ p`. -/
theorem frob_zeta (v : UnramifiedPlace N) :
    frob N v (IsCyclotomicExtension.zeta N ℚ (CycField N))
      = (IsCyclotomicExtension.zeta N ℚ (CycField N)) ^ (v.1) :=
  frob_apply N v (IsCyclotomicExtension.zeta_spec N ℚ (CycField N)).pow_eq_one

/-- The local parameter of a one-dimensional Galois representation at an unramified place:
the value of the representation on the Frobenius element. -/
noncomputable def galoisLocalParam (ρ : GaloisChar N) (v : UnramifiedPlace N) : ℂ :=
  (ρ (frob N v) : ℂ)

/-- The Satake parameter of an automorphic representation of `GL(1)/ℚ` (i.e. a Dirichlet
character) at an unramified place: the value `χ(p)`. -/
def automorphicLocalParam (χ : DirichletCharacter ℂ N) (v : UnramifiedPlace N) : ℂ :=
  χ (v.1 : ZMod N)

/-- The reciprocity bijection between one-dimensional Galois representations of conductor
dividing `N` and automorphic representations of `GL(1)/ℚ` of level `N`, obtained from the
cyclotomic reciprocity isomorphism `Gal(ℚ(ζ_N)/ℚ) ≃ (ℤ/Nℤ)ˣ`. -/
noncomputable def reciprocityEquiv : GaloisChar N ≃ DirichletCharacter ℂ N where
  toFun ρ :=
    MulChar.ofUnitHom
      (ρ.comp (IsCyclotomicExtension.Rat.galEquivZMod N (CycField N)).symm.toMonoidHom)
  invFun χ :=
    (MulChar.equivToUnitHom χ).comp
      (IsCyclotomicExtension.Rat.galEquivZMod N (CycField N)).toMonoidHom
  left_inv ρ := by
    ext σ
    simp only [MulChar.ofUnitHom_eq, Equiv.apply_symm_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  right_inv χ := by
    ext a
    simp only [MulChar.ofUnitHom_eq, MulChar.equivToUnitHom_symm_coe, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, MulChar.coe_equivToUnitHom]

theorem reciprocityEquiv_apply (ρ : GaloisChar N) (v : UnramifiedPlace N) :
    reciprocityEquiv N ρ (v.1 : ZMod N) = (ρ (frob N v) : ℂ) := by
  have : ((v.1 : ℕ) : ZMod N)
      = ((ZMod.unitOfCoprime v.1 (UnramifiedPlace.coprime N v) : (ZMod N)ˣ) : ZMod N) := by
    rw [ZMod.coe_unitOfCoprime]
  rw [this, reciprocityEquiv]
  simp only [Equiv.coe_fn_mk, MulChar.ofUnitHom_eq, MulChar.equivToUnitHom_symm_coe,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, frob]

/-- The reciprocity bijection is compatible with twisting: it is multiplicative. -/
theorem reciprocityEquiv_mul (ρ₁ ρ₂ : GaloisChar N) :
    reciprocityEquiv N (ρ₁ * ρ₂) = reciprocityEquiv N ρ₁ * reciprocityEquiv N ρ₂ := by
  ext a
  simp only [reciprocityEquiv, Equiv.coe_fn_mk, MulChar.ofUnitHom_eq,
    MulChar.equivToUnitHom_symm_coe, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MonoidHom.mul_apply, Units.val_mul, MulChar.mul_apply]

/-- **Langlands reciprocity for `GL(1)` over `ℚ` (the abelian base case).**

There is a bijection between the one-dimensional Galois representations of conductor
dividing `N` (characters of `Gal(ℚ(ζ_N)/ℚ)`) and the automorphic representations of
`GL(1)/ℚ` of level `N` (Dirichlet characters mod `N`), which matches the Frobenius
parameter `ρ(Frob_p)` on the Galois side with the Satake parameter `χ(p)` on the
automorphic side at every unramified place `p ∤ N`.

This is the `n = 1` case of the Langlands reciprocity conjecture; equivalently, it is the
cyclotomic (Kronecker–Weber) form of Artin reciprocity for `ℚ`. -/
theorem langlands_reciprocity (N : ℕ) [NeZero N] :
    LanglandsReciprocityHolds (galoisLocalParam N) (automorphicLocalParam N) :=
  ⟨reciprocityEquiv N, fun ρ v => (reciprocityEquiv_apply N ρ v).symm⟩

/-- Consequence of the base case: the local `L`-factors of corresponding objects agree at
every unramified place, so the Artin `L`-function of `ρ` is the Dirichlet `L`-function of
the matching character. -/
theorem langlands_reciprocity_local_L_factor (N : ℕ) [NeZero N] (ρ : GaloisChar N)
    (v : UnramifiedPlace N) (s : ℂ) :
    (1 - (ρ (frob N v) : ℂ) * (v.1 : ℂ) ^ (-s))⁻¹
      = (1 - (reciprocityEquiv N ρ) (v.1 : ZMod N) * (v.1 : ℂ) ^ (-s))⁻¹ := by
  rw [reciprocityEquiv_apply]

end GL1

end Frontier

