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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open Polynomial

/-!
## The abstract shape of a reciprocity statement

Langlands reciprocity asserts that Galois representations are matched, bijectively, with
automorphic representations, in such a way that the two sides have the same `L`-function.
Since Mathlib does not (yet) contain automorphic representations of `GL n` over the adeles,
we package the *shape* of such a statement: a type of Galois-side objects, a type of
automorphic-side objects, and, for each, the sequence of Dirichlet coefficients of its
`L`-function.
-/

/-- The data entering a reciprocity statement: a type of Galois representations, a type of
automorphic representations, and the Dirichlet coefficients of the associated `L`-functions. -/
structure ReciprocityData where
  /-- The Galois side: e.g. `n`-dimensional representations of the absolute Galois group. -/
  GaloisRep : Type
  /-- The automorphic side: e.g. cuspidal automorphic representations of `GL n`. -/
  AutomorphicRep : Type
  /-- Dirichlet coefficients of the Artin `L`-function of a Galois representation. -/
  galoisCoeff : GaloisRep → ℕ → ℂ
  /-- Dirichlet coefficients of the automorphic `L`-function. -/
  autCoeff : AutomorphicRep → ℕ → ℂ

/-- **Langlands reciprocity** for a given package of data: there is a bijection between the
Galois side and the automorphic side which preserves `L`-functions, i.e. matches all the
Dirichlet coefficients. -/
def LanglandsReciprocity (D : ReciprocityData) : Prop :=
  ∃ e : D.GaloisRep ≃ D.AutomorphicRep, ∀ ρ : D.GaloisRep, D.galoisCoeff ρ = D.autCoeff (e ρ)

/-- If reciprocity holds, then every Galois `L`-function coincides, as a Dirichlet series, with
an automorphic one. -/
theorem lSeries_eq_of_langlandsReciprocity {D : ReciprocityData} (h : LanglandsReciprocity D) :
    ∃ e : D.GaloisRep ≃ D.AutomorphicRep, ∀ (ρ : D.GaloisRep) (s : ℂ),
      LSeries (D.galoisCoeff ρ) s = LSeries (D.autCoeff (e ρ)) s := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, fun ρ s => by rw [he ρ]⟩

/-!
## The abelian (`GL 1`) case over `ℚ`

Here reciprocity is a theorem: it is the cyclotomic case of class field theory.  For a level
`n`, the Galois group of `ℚ(ζₙ)/ℚ` is `(ℤ/nℤ)ˣ`, and hence one-dimensional Galois
representations of `Gal(ℚ(ζₙ)/ℚ)` correspond bijectively to Dirichlet characters mod `n`
(the automorphic representations of `GL 1` of conductor dividing `n`).  Under this bijection
the Artin `L`-function equals the Dirichlet `L`-function, because the Frobenius at `m`
corresponds to the class of `m` in `(ℤ/nℤ)ˣ`.
-/

section GL1

variable (n : ℕ) [NeZero n]

/-- The Galois group of `ℚ(ζₙ)/ℚ` is isomorphic to `(ℤ/nℤ)ˣ`, via `σ ζ = ζ ^ a`. -/
noncomputable def cycGalEquiv : Gal((CyclotomicField n ℚ)/ℚ) ≃* (ZMod n)ˣ :=
  IsCyclotomicExtension.autEquivPow _ (cyclotomic.irreducible_rat (NeZero.pos n))

/-- One-dimensional (necessarily continuous, as the group is finite) Galois representations of
`Gal(ℚ(ζₙ)/ℚ)`. -/
abbrev GaloisChar : Type := Gal((CyclotomicField n ℚ)/ℚ) →* ℂˣ

/-- The Frobenius element at `m`, for `m` invertible mod `n`: the automorphism of `ℚ(ζₙ)`
sending each `n`-th root of unity `x` to `x ^ m`. -/
noncomputable def frob {m : ℕ} (h : IsUnit (m : ZMod n)) : Gal((CyclotomicField n ℚ)/ℚ) :=
  (cycGalEquiv n).symm h.unit

/-- The Frobenius at `m` really does raise `n`-th roots of unity to the `m`-th power. -/
theorem frob_apply {m : ℕ} (h : IsUnit (m : ZMod n)) {x : CyclotomicField n ℚ} (hx : x ^ n = 1) :
    frob n h x = x ^ m := by
  have h1 : frob n h x = x ^ ((cycGalEquiv n (frob n h)).val.val) :=
    IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq n _ _ hx
  have h2 : cycGalEquiv n (frob n h) = h.unit := (cycGalEquiv n).apply_symm_apply _
  rw [h1, h2]
  have hval : ((h.unit : (ZMod n)ˣ) : ZMod n) = (m : ZMod n) := h.unit_spec
  have : ((h.unit : (ZMod n)ˣ) : ZMod n).val ≡ m [MOD n] := by
    rw [hval, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.cast_id]
  exact pow_eq_pow_of_modEq this hx

/-- The Dirichlet coefficients of the Artin `L`-function of a one-dimensional Galois
representation: at `m` coprime to `n` it is the value at the Frobenius at `m`, and `0`
otherwise (the ramified places). -/
noncomputable def artinCoeff (ρ : GaloisChar n) (m : ℕ) : ℂ :=
  if h : IsUnit (m : ZMod n) then ((ρ (frob n h) : ℂˣ) : ℂ) else 0

/-- The reciprocity package in the `GL 1` case of level `n` over `ℚ`. -/
noncomputable def gl1Data : ReciprocityData where
  GaloisRep := GaloisChar n
  AutomorphicRep := DirichletCharacter ℂ n
  galoisCoeff := artinCoeff n
  autCoeff := fun χ m => χ (m : ZMod n)

/-- The reciprocity bijection in the `GL 1` case: a Galois character of `Gal(ℚ(ζₙ)/ℚ)` is
transported along `Gal(ℚ(ζₙ)/ℚ) ≃ (ℤ/nℤ)ˣ` to a Dirichlet character mod `n`. -/
noncomputable def gl1Equiv : GaloisChar n ≃ DirichletCharacter ℂ n :=
  (MulEquiv.monoidHomCongrLeftEquiv (cycGalEquiv n)).trans MulChar.equivToUnitHom.symm

/-- Matching of `L`-functions: the Artin coefficients of `ρ` are the values of the associated
Dirichlet character. -/
theorem artinCoeff_eq_dirichlet (ρ : GaloisChar n) :
    artinCoeff n ρ = fun m : ℕ => (gl1Equiv n ρ) (m : ZMod n) := by
  funext m
  rw [artinCoeff]
  split_ifs with h
  · have hm : ((h.unit : (ZMod n)ˣ) : ZMod n) = (m : ZMod n) := h.unit_spec
    rw [← hm, gl1Equiv]
    simp only [Equiv.trans_apply, MulChar.equivToUnitHom_symm_coe,
      MulEquiv.monoidHomCongrLeftEquiv_apply, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom]
    rfl
  · exact ((gl1Equiv n ρ).map_nonunit h).symm

end GL1

/-- **Langlands reciprocity, abelian (`GL 1`) case over `ℚ`.**

For every level `n`, one-dimensional Galois representations of `Gal(ℚ(ζₙ)/ℚ)` are in
bijection with Dirichlet characters mod `n` — the automorphic representations of `GL 1` of
level dividing `n` — in such a way that the Artin `L`-function of a Galois character equals
the Dirichlet `L`-function of the corresponding character, coefficient by coefficient.

This is the base case of the general Langlands reciprocity conjecture, whose shape is
formalized by `Frontier.LanglandsReciprocity`. -/
theorem langlands_reciprocity (n : ℕ) [NeZero n] : LanglandsReciprocity (gl1Data n) :=
  ⟨gl1Equiv n, fun ρ => artinCoeff_eq_dirichlet n ρ⟩

/-- The `L`-function form of the abelian case: the Artin `L`-series of a Galois character of
`Gal(ℚ(ζₙ)/ℚ)` equals the Dirichlet `L`-series of the corresponding Dirichlet character. -/
theorem artin_lSeries_eq_dirichlet_lSeries (n : ℕ) [NeZero n] (ρ : GaloisChar n) (s : ℂ) :
    LSeries (artinCoeff n ρ) s = LSeries (fun m : ℕ => (gl1Equiv n ρ) (m : ZMod n)) s := by
  rw [artinCoeff_eq_dirichlet]

end Frontier

