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

open Polynomial IsCyclotomicExtension

namespace Frontier

/-!
## The shape of a reciprocity law

Langlands reciprocity asserts that the *Galois side* of arithmetic (Galois representations,
with their local Frobenius data at unramified places) and the *automorphic side*
(automorphic representations, with their local Satake/Hecke data) are in a bijection that
matches the local data place by place.  The structure `ReciprocityLaw` below records exactly
this shape: a bijection between the two collections of objects, together with the
local-data maps and the requirement that they agree under the bijection.  A reciprocity law
in this sense immediately gives equality of all the local Euler factors, hence of the
associated `L`-functions.

## What is proved here

We prove the abelian base case: **the `GL(1)` case of Langlands reciprocity over `ℚ`**, i.e.
class field theory for the cyclotomic extensions of `ℚ`.  The automorphic side consists of
the Dirichlet characters mod `N` (the automorphic representations of `GL(1)/ℚ` of conductor
dividing `N`), the Galois side of the (necessarily continuous, finite-image) characters of
`Gal(ℚ(ζ_N)/ℚ)`, and for a prime `p ∤ N` the local datum is the value at the Frobenius
element `Frob_p`, which is the unique automorphism with `ζ ↦ ζ ^ p`.  The reciprocity
statement is that under the correspondence, `ρ(Frob_p) = χ(p)` for all such `p`, so that all
unramified Euler factors — hence the Artin `L`-function of `ρ` and the Dirichlet `L`-function
of `χ` — agree.
-/

/-- The abstract shape of a *reciprocity law*: a bijection between automorphic objects and
Galois objects which matches the local data attached to each object at every place. -/
structure ReciprocityLaw (GalRep AutRep Place LocalData : Type*) where
  /-- The correspondence: automorphic objects ↔ Galois objects. -/
  correspondence : AutRep ≃ GalRep
  /-- Local data on the Galois side (Frobenius conjugacy data at a place). -/
  galLocalData : GalRep → Place → LocalData
  /-- Local data on the automorphic side (Satake / Hecke data at a place). -/
  autLocalData : AutRep → Place → LocalData
  /-- The two local data agree under the correspondence. -/
  local_compat : ∀ (π : AutRep) (v : Place), galLocalData (correspondence π) v = autLocalData π v

/-!
## Auxiliary lemmas
-/

private lemma pow_mod_eq {M : Type*} [Monoid M] {x : M} {n : ℕ} (hx : x ^ n = 1) (a : ℕ) :
    x ^ a = x ^ (a % n) := by
  conv_lhs => rw [← Nat.div_add_mod a n, pow_add, pow_mul, hx, one_pow, one_mul]

private lemma pow_eq_pow_of_natCast_eq {M : Type*} [Monoid M] {x : M} {n : ℕ}
    (hx : x ^ n = 1) {a b : ℕ} (h : (a : ZMod n) = (b : ZMod n)) : x ^ a = x ^ b := by
  have hab : a % n = b % n := (ZMod.natCast_eq_natCast_iff a b n).mp h
  rw [pow_mod_eq hx a, pow_mod_eq hx b, hab]

/-- A fixed primitive `N`-th root of unity in the `N`-th cyclotomic field over `ℚ`. -/
noncomputable abbrev cycZeta (N : ℕ) [NeZero N] : CyclotomicField N ℚ :=
  zeta N ℚ (CyclotomicField N ℚ)

/-- The cyclotomic character: the canonical isomorphism
`Gal(ℚ(ζ_N)/ℚ) ≃* (ZMod N)ˣ`, sending `σ` to the exponent `k` with `σ ζ = ζ ^ k`. -/
noncomputable def cycGalEquiv (N : ℕ) [NeZero N] :
    (CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) ≃* (ZMod N)ˣ :=
  autEquivPow (CyclotomicField N ℚ) (cyclotomic.irreducible_rat (NeZero.pos N))

/-- If `σ` acts on the chosen root of unity by `ζ ↦ ζ ^ p`, then the cyclotomic character
sends `σ` to `p mod N`. -/
lemma cycGalEquiv_coe_of_zeta_pow (N : ℕ) [NeZero N] (p : ℕ)
    (σ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ)
    (hσ : σ (cycZeta N) = (cycZeta N) ^ p) :
    ((cycGalEquiv N σ : (ZMod N)ˣ) : ZMod N) = (p : ZMod N) := by
  have hN : 0 < N := NeZero.pos N
  have hζ := zeta_spec N ℚ (CyclotomicField N ℚ)
  have key := hζ.autToPow_spec ℚ σ
  rw [hσ] at key
  simp only [cycGalEquiv, autEquivPow_apply]
  rw [pow_mod_eq hζ.pow_eq_one p] at key
  have hval : ((hζ.autToPow ℚ σ : (ZMod N)ˣ) : ZMod N).val = p % N :=
    hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ hN) key
  have hcast := congrArg (fun k : ℕ => (k : ZMod N)) hval
  simpa [ZMod.natCast_val, ZMod.cast_id, ZMod.natCast_mod] using hcast

/-- Existence of the Frobenius automorphism at a prime `p` unramified in `ℚ(ζ_N)/ℚ`:
there is a `ℚ`-automorphism of `ℚ(ζ_N)` acting on roots of unity by `ζ ↦ ζ ^ p`. -/
lemma exists_frobenius (N : ℕ) [NeZero N] {p : ℕ} (hp : Nat.Coprime p N) :
    ∃ σ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ,
      σ (cycZeta N) = (cycZeta N) ^ p := by
  have hζ := zeta_spec N ℚ (CyclotomicField N ℚ)
  refine ⟨(cycGalEquiv N).symm (ZMod.unitOfCoprime p hp), ?_⟩
  have key := hζ.autToPow_spec ℚ ((cycGalEquiv N).symm (ZMod.unitOfCoprime p hp))
  rw [← key]
  have hu : ((cycGalEquiv N ((cycGalEquiv N).symm (ZMod.unitOfCoprime p hp)) : (ZMod N)ˣ) :
      ZMod N) = (p : ZMod N) := by
    simp [ZMod.coe_unitOfCoprime]
  apply pow_eq_pow_of_natCast_eq hζ.pow_eq_one
  simp only [cycGalEquiv, autEquivPow_apply] at hu
  rw [ZMod.natCast_val, ZMod.cast_id] at *
  exact hu

/-- The reciprocity bijection for `GL(1)/ℚ` of level `N`: Dirichlet characters mod `N`
correspond to characters of `Gal(ℚ(ζ_N)/ℚ)`, by composing with the cyclotomic character. -/
noncomputable def gl1Correspondence (N : ℕ) [NeZero N] :
    DirichletCharacter ℂ N ≃
      ((CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) →* ℂˣ) :=
  MulChar.n.trans (MulEquiv.monoidHomCongrLeftEquiv (cycGalEquiv N).symm)

lemma gl1Correspondence_apply (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (σ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) :
    ((gl1Correspondence N χ σ : ℂˣ) : ℂ) = χ ((cycGalEquiv N σ : (ZMod N)ˣ) : ZMod N) := by
  simp [gl1Correspondence, MulChar.coe_n]

/-!
## Langlands reciprocity for `GL(1)` over `ℚ`
-/

/-- **Langlands reciprocity, the `GL(1)` case over `ℚ` (abelian class field theory for
cyclotomic fields).**

For every level `N ≥ 1` there is a bijection `Φ` between the automorphic side — the
Dirichlet characters mod `N`, i.e. the automorphic representations of `GL(1)/ℚ` whose
conductor divides `N` — and the Galois side — the characters of `Gal(ℚ(ζ_N)/ℚ)` — such
that for every prime `p` unramified in `ℚ(ζ_N)/ℚ` (equivalently `p ∤ N`):

* the Frobenius element at `p` exists, namely a `ℚ`-automorphism `σ` of `ℚ(ζ_N)` with
  `σ ζ = ζ ^ p`; and
* for every such `σ` and every Dirichlet character `χ`, the Galois local datum
  `Φ χ (Frob_p)` equals the automorphic local datum `χ(p)`.

Thus the correspondence matches the local (Satake / Frobenius) parameters at every
unramified place, which is precisely the reciprocity assertion in this case; equality of
all Euler factors follows (see `Frontier.langlands_reciprocity_euler_factor`). -/
theorem langlands_reciprocity (N : ℕ) [NeZero N] :
    ∃ Φ : DirichletCharacter ℂ N ≃
        ((CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) →* ℂˣ),
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        (∃ σ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ,
            σ (cycZeta N) = (cycZeta N) ^ p) ∧
        ∀ σ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ,
          σ (cycZeta N) = (cycZeta N) ^ p →
          ∀ χ : DirichletCharacter ℂ N, ((Φ χ σ : ℂˣ) : ℂ) = χ (p : ZMod N) := by
  refine ⟨gl1Correspondence N, fun p hp hpN => ?_⟩
  have hcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  refine ⟨exists_frobenius N hcop, fun σ hσ χ => ?_⟩
  rw [gl1Correspondence_apply, cycGalEquiv_coe_of_zeta_pow N p σ hσ]

/-- Consequence of `Frontier.langlands_reciprocity`: under the correspondence, the local
Euler factor of the Galois character at an unramified prime `p` agrees with the local Euler
factor of the corresponding Dirichlet character, for every complex `s`.  Hence the Artin
`L`-function of the Galois character coincides with the Dirichlet `L`-function of the
corresponding automorphic object. -/
theorem langlands_reciprocity_euler_factor (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (σ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ)
    (hσ : σ (cycZeta N) = (cycZeta N) ^ p) (s : ℂ) :
    (1 - ((gl1Correspondence N χ σ : ℂˣ) : ℂ) * (p : ℂ) ^ (-s))⁻¹
      = (1 - χ (p : ZMod N) * (p : ℂ) ^ (-s))⁻¹ := by
  rw [gl1Correspondence_apply, cycGalEquiv_coe_of_zeta_pow N p σ hσ]

/-- The `GL(1)/ℚ` reciprocity law of level `N`, packaged as a `ReciprocityLaw`: the places
are the primes `p ∤ N`, the local datum is the Frobenius eigenvalue (a complex number),
and the compatibility is the content of `Frontier.langlands_reciprocity`. -/
noncomputable def gl1ReciprocityLaw (N : ℕ) [NeZero N] :
    ReciprocityLaw ((CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) →* ℂˣ)
      (DirichletCharacter ℂ N) {p : ℕ // p.Prime ∧ ¬ p ∣ N} ℂ where
  correspondence := gl1Correspondence N
  galLocalData ρ v :=
    ((ρ (Classical.choose (exists_frobenius N
      ((Nat.Prime.coprime_iff_not_dvd v.2.1).mpr v.2.2))) : ℂˣ) : ℂ)
  autLocalData χ v := χ ((v : ℕ) : ZMod N)
  local_compat := by
    rintro χ ⟨p, hp, hpN⟩
    have hcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
    have hσ := Classical.choose_spec (exists_frobenius N hcop)
    simpa using
      (gl1Correspondence_apply N χ (Classical.choose (exists_frobenius N hcop))).trans
        (by rw [cycGalEquiv_coe_of_zeta_pow N p _ hσ])

end Frontier

