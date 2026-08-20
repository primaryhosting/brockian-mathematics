import Mathlib

/-!
# Langlands Reciprocity
Category: Frontier Abel
Target: Frontier.langlands_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Frontier

open Polynomial IsCyclotomicExtension

variable (n : ℕ) [NeZero n] (L : Type*) [Field L] [Algebra ℚ L]
  [IsCyclotomicExtension {n} ℚ L]

/-- **The Artin reciprocity map** for the cyclotomic extension `ℚ(ζ_n)/ℚ`:
the isomorphism from the idele class group of conductor `n`, namely `(ZMod n)ˣ`,
onto the Galois group `Gal(ℚ(ζ_n)/ℚ)`. -/
noncomputable def artinMap : (ZMod n)ˣ ≃* (L ≃ₐ[ℚ] L) :=
  (IsCyclotomicExtension.autEquivPow L (cyclotomic.irreducible_rat (NeZero.pos n))).symm

/-- The Artin map is normalised so that the class of `a` acts on `n`-th roots of unity
by `ζ ↦ ζ ^ a`. -/
theorem artinMap_apply_root_of_unity (a : (ZMod n)ˣ) (x : L) (hx : x ^ n = 1) :
    artinMap n L a x = x ^ ((a : ZMod n).val) := by
  have h : Irreducible (cyclotomic n ℚ) := cyclotomic.irreducible_rat (NeZero.pos n)
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ L) n :=
    IsCyclotomicExtension.zeta_spec n ℚ L
  have hpow : hζ.autToPow ℚ (artinMap n L a) = a := by
    have := (IsCyclotomicExtension.autEquivPow (n := n) (K := ℚ) L h).apply_symm_apply a
    simpa [artinMap, IsCyclotomicExtension.autEquivPow_apply] using this
  have hζ' : artinMap n L a (IsCyclotomicExtension.zeta n ℚ L)
      = (IsCyclotomicExtension.zeta n ℚ L) ^ ((a : ZMod n).val) := by
    have key := hζ.autToPow_spec ℚ (artinMap n L a)
    rw [hpow] at key
    exact key.symm
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [map_pow, hζ', ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- An automorphism of a cyclotomic extension is determined by its effect on
the `n`-th roots of unity. -/
theorem aut_ext {σ τ : L ≃ₐ[ℚ] L}
    (h : ∀ x : L, x ^ n = 1 → σ x = τ x) : σ = τ := by
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ L) n :=
    IsCyclotomicExtension.zeta_spec n ℚ L
  apply AlgEquiv.coe_algHom_injective
  apply (hζ.powerBasis ℚ).algHom_ext
  simpa [hζ.powerBasis_gen ℚ] using h _ hζ.pow_eq_one

/-- The Frobenius at a prime `p` unramified in `ℚ(ζ_n)/ℚ` (i.e. `p ∤ n`) is the image
under the Artin map of the class of `p`. -/
theorem artinMap_frobenius (p : ℕ) (hp : Nat.Coprime p n) (σ : L ≃ₐ[ℚ] L)
    (hσ : ∀ x : L, x ^ n = 1 → σ x = x ^ p) :
    σ = artinMap n L (ZMod.unitOfCoprime p hp) := by
  refine aut_ext n L (fun x hx => ?_)
  rw [hσ x hx, artinMap_apply_root_of_unity n L _ x hx]
  have hval : ((ZMod.unitOfCoprime p hp : (ZMod n)ˣ) : ZMod n).val = p % n := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  rw [hval]
  conv_lhs => rw [← Nat.div_add_mod p n]
  rw [pow_add, pow_mul, hx, one_pow, one_mul]

/--
**Langlands reciprocity for `GL(1)` over `ℚ`** (the abelian case of the Langlands
correspondence, i.e. Artin reciprocity), for the cyclotomic extension `ℚ(ζ_n)/ℚ`.

The statement has three parts.

1. *Reciprocity (Artin map).* There is a canonical isomorphism
   `(ZMod n)ˣ ≃* Gal(ℚ(ζ_n)/ℚ)`, normalised so that the class of `a` acts on every
   `n`-th root of unity by `x ↦ x ^ a`. This is the automorphic-to-Galois transfer of
   conductor `n` on the level of groups.

2. *The correspondence.* Transport along the Artin map is a bijection between the
   one-dimensional (complex) Galois representations of `Gal(ℚ(ζ_n)/ℚ)`, i.e. the
   Artin characters of conductor dividing `n`, and the automorphic representations of
   `GL(1)` of conductor dividing `n`, i.e. the Dirichlet characters mod `n`.

3. *Local–global compatibility at unramified primes.* If `p` is a prime not dividing `n`
   and `σ` is a Frobenius element at `p` (an automorphism acting on `n`-th roots of unity
   by `x ↦ x ^ p`), then for every Galois character `ρ`, the value `ρ σ` of `ρ` at
   Frobenius equals the value at `p` of the associated Dirichlet character. Hence the
   two `L`-functions have the same Euler factors at all unramified primes.
-/
theorem langlands_reciprocity :
    (∀ (a : (ZMod n)ˣ) (x : L), x ^ n = 1 →
        artinMap n L a x = x ^ ((a : ZMod n).val)) ∧
    Function.Bijective
      (fun ρ : (L ≃ₐ[ℚ] L) →* ℂˣ =>
        (MulChar.ofUnitHom (ρ.comp (artinMap n L).toMonoidHom) : DirichletCharacter ℂ n)) ∧
    (∀ (ρ : (L ≃ₐ[ℚ] L) →* ℂˣ) (p : ℕ), Nat.Coprime p n → ∀ σ : L ≃ₐ[ℚ] L,
        (∀ x : L, x ^ n = 1 → σ x = x ^ p) →
        (MulChar.ofUnitHom (ρ.comp (artinMap n L).toMonoidHom) : DirichletCharacter ℂ n)
            (p : ZMod n) = (ρ σ : ℂ)) := by
  refine ⟨artinMap_apply_root_of_unity n L, ⟨?_, ?_⟩, ?_⟩
  · intro ρ₁ ρ₂ h
    simp only [MulChar.ofUnitHom_eq] at h
    have h' := MulChar.equivToUnitHom.symm.injective h
    ext σ
    have := congrArg (fun f : (ZMod n)ˣ →* ℂˣ => f ((artinMap n L).symm σ)) h'
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] at this
    exact congrArg Units.val this
  · intro χ
    refine ⟨(MulChar.equivToUnitHom χ).comp (artinMap n L).symm.toMonoidHom, ?_⟩
    have : ((MulChar.equivToUnitHom χ).comp (artinMap n L).symm.toMonoidHom).comp
        (artinMap n L).toMonoidHom = MulChar.equivToUnitHom χ := by
      ext a; simp
    show MulChar.ofUnitHom _ = χ
    rw [MulChar.ofUnitHom_eq, this, Equiv.symm_apply_apply]
  · intro ρ p hp σ hσ
    have h1 : σ = artinMap n L (ZMod.unitOfCoprime p hp) := artinMap_frobenius n L p hp σ hσ
    have h2 : ((p : ZMod n)) = ((ZMod.unitOfCoprime p hp : (ZMod n)ˣ) : ZMod n) :=
      (ZMod.coe_unitOfCoprime p hp).symm
    rw [h2, MulChar.ofUnitHom_coe, h1]
    simp

/-- The reciprocity statement is non-vacuous: it applies to the cyclotomic field `ℚ(ζ_n)`
for every `n ≠ 0`. -/
theorem langlands_reciprocity_cyclotomicField :
    (∀ (a : (ZMod n)ˣ) (x : CyclotomicField n ℚ), x ^ n = 1 →
        artinMap n (CyclotomicField n ℚ) a x = x ^ ((a : ZMod n).val)) ∧
    Function.Bijective
      (fun ρ : (CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) →* ℂˣ =>
        (MulChar.ofUnitHom (ρ.comp (artinMap n (CyclotomicField n ℚ)).toMonoidHom) :
          DirichletCharacter ℂ n)) ∧
    (∀ (ρ : (CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) →* ℂˣ) (p : ℕ), Nat.Coprime p n →
        ∀ σ : CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ,
        (∀ x : CyclotomicField n ℚ, x ^ n = 1 → σ x = x ^ p) →
        (MulChar.ofUnitHom (ρ.comp (artinMap n (CyclotomicField n ℚ)).toMonoidHom) :
          DirichletCharacter ℂ n) (p : ZMod n) = (ρ σ : ℂ)) :=
  langlands_reciprocity n (CyclotomicField n ℚ)

end Frontier

