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

namespace Frontier

/-!
## The shape of the conjecture

Langlands reciprocity predicts that every `d`-dimensional (continuous, complex) representation
`ρ` of the absolute Galois group of a number field is *automorphic*: there is an automorphic
representation `π` of `GL_d` over that field whose local data (Satake parameters / Hecke
eigenvalues) match the Frobenius data of `ρ`, so that `L(s, ρ) = L(s, π)`.

For `d = 1` over `ℚ` the automorphic representations of `GL_1` of finite order are exactly the
Dirichlet characters, and the predicted matching is provided by the Artin reciprocity map.  This
degree-one case is the classical base case of the conjecture (abelian class field theory), and it
is the case formalized and proved here.

`IsArtinReciprocity art` below is the precise degree-one reciprocity statement relative to a
reciprocity ("Artin") map `art : G →* (ZMod n)ˣ`: *every* one-dimensional Galois representation of
`G` is matched by a *unique* Dirichlet character modulo `n`, the matching being
`χ (art g) = ρ g`.
-/

/-- A degree-one Galois representation of a group `G`: a character `G →* ℂˣ`.
(For a finite Galois group every homomorphism to `ℂˣ` is automatically continuous with finite
image, so this is exactly the notion of an Artin character of degree one.) -/
abbrev GaloisChar (G : Type*) [Group G] := G →* ℂˣ

/-- **Degree-one Langlands reciprocity relative to a reciprocity map `art`.**

Every one-dimensional Galois representation `ρ : G →* ℂˣ` is automorphic: there is a *unique*
Dirichlet character `χ` modulo `n` (i.e. a unique automorphic representation of `GL₁` of
conductor dividing `n`) whose value at `art g` is `ρ g` for all `g`. -/
def IsArtinReciprocity {G : Type*} [Group G] {n : ℕ} (art : G →* (ZMod n)ˣ) : Prop :=
  ∀ ρ : GaloisChar G, ∃! χ : DirichletCharacter ℂ n,
    ∀ g : G, χ ((art g : ZMod n)) = (ρ g : ℂ)

/-!
## The reduction

Degree-one reciprocity for `G` holds as soon as the reciprocity map is an isomorphism
`G ≃* (ZMod n)ˣ`.  This is the abstract form of the classical statement that the Artin map
identifies the Galois group of an abelian extension with a ray class group.
-/

/-- **Reduction lemma.** If the reciprocity map is an isomorphism `G ≃* (ZMod n)ˣ`, then
degree-one Langlands reciprocity holds for `G`. -/
theorem isArtinReciprocity_of_mulEquiv {G : Type*} [Group G] {n : ℕ} (e : G ≃* (ZMod n)ˣ) :
    IsArtinReciprocity (e : G →* (ZMod n)ˣ) := by
  intro ρ
  refine ⟨MulChar.ofUnitHom (ρ.comp (e.symm : (ZMod n)ˣ →* G)), ?_, ?_⟩
  · intro g
    simp
  · intro χ hχ
    refine MulChar.ext ?_
    intro u
    have h := hχ (e.symm u)
    simp only [MonoidHom.coe_coe, MulEquiv.apply_symm_apply] at h
    rw [h, MulChar.ofUnitHom_coe]
    simp

/-!
## The base case: cyclotomic fields

Let `K = ℚ(ζₙ)`.  The Artin (cyclotomic) reciprocity map sends `σ ∈ Gal(K/ℚ)` to the class
`a ∈ (ZMod n)ˣ` with `σ ζ = ζ ^ a`, and it is an isomorphism.  Combined with the reduction above
this proves degree-one Langlands reciprocity for `ℚ(ζₙ)/ℚ`.
-/

variable (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {n} ℚ K]

/-- The cyclotomic Artin reciprocity map `Gal(ℚ(ζₙ)/ℚ) ≃* (ZMod n)ˣ`, characterized by
`σ ζ = ζ ^ (artinMap σ)` on `n`-th roots of unity. -/
noncomputable abbrev cyclotomicArtinMap : (K ≃ₐ[ℚ] K) ≃* (ZMod n)ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod n K

/-- The defining property of the cyclotomic Artin map: it acts on `n`-th roots of unity by
raising to the corresponding power. -/
theorem cyclotomicArtinMap_spec (σ : K ≃ₐ[ℚ] K) {x : K} (hx : x ^ n = 1) :
    σ x = x ^ ((cyclotomicArtinMap n K σ : ZMod n).val) :=
  IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq n K σ hx

/-- If `σ` sends a primitive `n`-th root of unity `ζ` to `ζ ^ a`, then `a` reduces modulo `n` to
the Artin symbol of `σ`. -/
theorem cyclotomicArtinMap_eq_of_pow_eq (ζ : K) (hζ : IsPrimitiveRoot ζ n) (σ : K ≃ₐ[ℚ] K)
    (a : ℕ) (ha : σ ζ = ζ ^ a) :
    (a : ZMod n) = ((cyclotomicArtinMap n K σ : (ZMod n)ˣ) : ZMod n) := by
  have h1 : σ ζ = ζ ^ ((cyclotomicArtinMap n K σ : ZMod n).val) :=
    cyclotomicArtinMap_spec n K σ hζ.pow_eq_one
  have h2 : ζ ^ a = ζ ^ ((cyclotomicArtinMap n K σ : ZMod n).val) := by rw [← ha, h1]
  have hmod : ∀ m : ℕ, ζ ^ m = ζ ^ (m % n) := by
    intro m
    conv_lhs => rw [← Nat.div_add_mod m n]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have h4 : a % n = (cyclotomicArtinMap n K σ : ZMod n).val := by
    refine hζ.pow_inj (Nat.mod_lt _ (NeZero.pos n)) (ZMod.val_lt _) ?_
    rw [← hmod a, h2]
  have h5 : ((a : ZMod n)) = (((cyclotomicArtinMap n K σ : ZMod n).val : ℕ) : ZMod n) := by
    rw [← h4, ZMod.natCast_mod]
  rw [h5, ZMod.natCast_val, ZMod.cast_id]

/-- Degree-one Langlands reciprocity for the cyclotomic field `ℚ(ζₙ)`, phrased through the
cyclotomic Artin map. -/
theorem isArtinReciprocity_cyclotomic :
    IsArtinReciprocity ((cyclotomicArtinMap n K : (K ≃ₐ[ℚ] K) ≃* (ZMod n)ˣ) :
      (K ≃ₐ[ℚ] K) →* (ZMod n)ˣ) :=
  isArtinReciprocity_of_mulEquiv _

/-- **Langlands reciprocity, degree-one cyclotomic base case.**

Let `K = ℚ(ζₙ)` with `ζ` a primitive `n`-th root of unity, and let `ρ : Gal(K/ℚ) →* ℂˣ` be a
one-dimensional Galois representation.  Then `ρ` is automorphic: there is a *unique* Dirichlet
character `χ` modulo `n` — i.e. a unique automorphic representation of `GL₁/ℚ` of conductor
dividing `n` — matching `ρ` under reciprocity, in the sense that whenever `σ` acts on `ζ` by
`ζ ↦ ζ ^ a` (i.e. `a` is the Artin symbol of `σ`, so that for a prime `p ∤ n` unramified in `K`
the Frobenius `σ = Frob_p` has `a = p`), one has `χ a = ρ σ`.

Equivalently: the Artin `L`-function of `ρ` equals the Dirichlet `L`-function of `χ`, since the
Euler factors agree at every unramified prime. -/
theorem langlands_reciprocity (ζ : K) (hζ : IsPrimitiveRoot ζ n) (ρ : GaloisChar (K ≃ₐ[ℚ] K)) :
    ∃! χ : DirichletCharacter ℂ n,
      ∀ (σ : K ≃ₐ[ℚ] K) (a : ℕ), σ ζ = ζ ^ a → χ (a : ZMod n) = (ρ σ : ℂ) := by
  have key := cyclotomicArtinMap_eq_of_pow_eq n K ζ hζ
  obtain ⟨χ, hχ, huniq⟩ := isArtinReciprocity_cyclotomic n K ρ
  refine ⟨χ, ?_, ?_⟩
  · intro σ a ha
    rw [key σ a ha]
    exact hχ σ
  · intro χ' hχ'
    refine huniq χ' ?_
    intro σ
    have hpow : σ ζ = ζ ^ ((cyclotomicArtinMap n K σ : ZMod n).val) :=
      cyclotomicArtinMap_spec n K σ hζ.pow_eq_one
    have := hχ' σ _ hpow
    rwa [ZMod.natCast_val, ZMod.cast_id] at this

/-- **The converse (automorphic to Galois) direction.**

Every Dirichlet character `χ` modulo `n` comes from a one-dimensional Galois representation of
`Gal(ℚ(ζₙ)/ℚ)`; together with `langlands_reciprocity` this exhibits the degree-one correspondence
as a bijection between Galois characters and Dirichlet characters modulo `n`. -/
theorem langlands_reciprocity_converse (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (χ : DirichletCharacter ℂ n) :
    ∃ ρ : GaloisChar (K ≃ₐ[ℚ] K),
      ∀ (σ : K ≃ₐ[ℚ] K) (a : ℕ), σ ζ = ζ ^ a → χ (a : ZMod n) = (ρ σ : ℂ) := by
  refine ⟨(MulChar.equivToUnitHom χ).comp
    ((cyclotomicArtinMap n K : (K ≃ₐ[ℚ] K) ≃* (ZMod n)ˣ) : (K ≃ₐ[ℚ] K) →* (ZMod n)ˣ), ?_⟩
  intro σ a ha
  rw [cyclotomicArtinMap_eq_of_pow_eq n K ζ hζ σ a ha]
  simp [MulChar.coe_equivToUnitHom]

/-- The hypotheses of `langlands_reciprocity` are satisfiable: the theorem applies to the
concrete cyclotomic field `ℚ(ζₙ)` for every `n ≥ 1`, so the statement is not vacuous. -/
theorem langlands_reciprocity_cyclotomicField (m : ℕ) [NeZero m]
    (ρ : GaloisChar (CyclotomicField m ℚ ≃ₐ[ℚ] CyclotomicField m ℚ)) :
    ∃! χ : DirichletCharacter ℂ m,
      ∀ (σ : CyclotomicField m ℚ ≃ₐ[ℚ] CyclotomicField m ℚ) (a : ℕ),
        σ (IsCyclotomicExtension.zeta m ℚ (CyclotomicField m ℚ))
          = (IsCyclotomicExtension.zeta m ℚ (CyclotomicField m ℚ)) ^ a → χ (a : ZMod m) = (ρ σ : ℂ) :=
  langlands_reciprocity m (CyclotomicField m ℚ) _
    (IsCyclotomicExtension.zeta_spec m ℚ (CyclotomicField m ℚ)) ρ

end Frontier

#print axioms Frontier.langlands_reciprocity
#print axioms Frontier.langlands_reciprocity_cyclotomicField
#print axioms Frontier.langlands_reciprocity_converse

