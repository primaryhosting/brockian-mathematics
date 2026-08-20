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

theorem zetaQ_spec (N : ℕ) [NeZero N] : IsPrimitiveRoot (zetaQ N) N :=
  IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicQ N)

/-- One dimensional Galois representations of conductor dividing `N`: characters of
`Gal(ℚ(ζ_N)/ℚ)`. -/
abbrev GaloisRepGL1 (N : ℕ) := (CyclotomicQ N ≃ₐ[ℚ] CyclotomicQ N) →* ℂˣ

/-- `σ` is *the Frobenius at `p`* in `Gal(ℚ(ζ_N)/ℚ)`: it raises roots of unity to the `p`-th
power. -/
def IsFrobeniusAt (N : ℕ) [NeZero N] (p : ℕ) (σ : CyclotomicQ N ≃ₐ[ℚ] CyclotomicQ N) : Prop :=
  σ (zetaQ N) = zetaQ N ^ p

/-- The `N`-th cyclotomic polynomial is irreducible over `ℚ`. -/
theorem cyclotomic_irr (N : ℕ) [NeZero N] : Irreducible (cyclotomic N ℚ) :=
  cyclotomic.irreducible_rat (NeZero.pos N)

/-- The cyclotomic character `Gal(ℚ(ζ_N)/ℚ) ≃* (ZMod N)ˣ`. -/
noncomputable def cycChar (N : ℕ) [NeZero N] :
    (CyclotomicQ N ≃ₐ[ℚ] CyclotomicQ N) ≃* (ZMod N)ˣ :=
  IsCyclotomicExtension.autEquivPow (CyclotomicQ N) (cyclotomic_irr N)

/-- The cyclotomic character sends `σ` to the exponent by which it acts on `N`-th roots of
unity. -/
theorem cycChar_spec (N : ℕ) [NeZero N] (σ : CyclotomicQ N ≃ₐ[ℚ] CyclotomicQ N) :
    zetaQ N ^ ((cycChar N σ : ZMod N)).val = σ (zetaQ N) := by
  simp [cycChar, (zetaQ_spec N).autToPow_spec ℚ σ]

/-- If a primitive `N`-th root of unity satisfies `ζ ^ a = ζ ^ b`, then `a = b` in `ZMod N`. -/
theorem natCast_eq_of_pow_eq_pow {M : Type*} [CommMonoid M] {n : ℕ} [NeZero n] {z : M}
    (hz : IsPrimitiveRoot z n) {a b : ℕ} (h : z ^ a = z ^ b) : (a : ZMod n) = (b : ZMod n) := by
  have hord : orderOf z = n := hz.eq_orderOf.symm
  have hlt : ∀ m : ℕ, m % n < n := fun m => Nat.mod_lt _ (NeZero.pos n)
  have hab : a % n = b % n := by
    refine hz.pow_inj (hlt a) (hlt b) ?_
    rw [← hord, pow_mod_orderOf, pow_mod_orderOf]
    exact h
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hab

/-- Frobenius at `p` corresponds to `p` under the cyclotomic character. -/
theorem cycChar_frobenius (N : ℕ) [NeZero N] {p : ℕ} (hp : Nat.Coprime p N)
    {σ : CyclotomicQ N ≃ₐ[ℚ] CyclotomicQ N} (hσ : IsFrobeniusAt N p σ) :
    cycChar N σ = ZMod.unitOfCoprime p hp := by
  have h1 : zetaQ N ^ ((cycChar N σ : ZMod N)).val = zetaQ N ^ p := by
    rw [cycChar_spec, hσ]
  have h2 := natCast_eq_of_pow_eq_pow (zetaQ_spec N) h1
  apply Units.ext
  simpa using h2

/-- Existence and uniqueness of the Frobenius element at a prime `p ∤ N`. -/
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
theorem isArithFrobAt_apply_zeta (N : ℕ) [NeZero N] {p : ℕ} (hpN : ¬ p ∣ N)
    {Q : Ideal (NumberField.RingOfIntegers (CyclotomicQ N))}
    (hQ : Ideal.under ℤ Q = Ideal.span {(p : ℤ)})
    {σ : CyclotomicQ N ≃ₐ[ℚ] CyclotomicQ N} (hσ : IsArithFrobAt ℤ σ Q) :
    IsFrobeniusAt N p σ := by
  have hzcoe : ((zetaQ_spec N).toInteger : CyclotomicQ N) = zetaQ N :=
    (zetaQ_spec N).coe_toInteger
  have hpow : (zetaQ_spec N).toInteger ^ N = 1 := by
    apply Subtype.ext
    push_cast [hzcoe]
    exact (zetaQ_spec N).pow_eq_one
  have hNQ : ((N : ℕ) : NumberField.RingOfIntegers (CyclotomicQ N)) ∉ Q := by
    intro hmem
    have hz : ((N : ℤ)) ∈ Ideal.under ℤ Q := by
      rw [Ideal.under, Ideal.mem_comap]
      simpa using hmem
    rw [hQ, Ideal.mem_span_singleton] at hz
    exact hpN (by exact_mod_cast hz)
  have hcard : Nat.card (ℤ ⧸ Ideal.under ℤ Q) = p := by
    rw [hQ, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have key := hσ.apply_of_pow_eq_one hpow hNQ
  rw [hcard] at key
  show σ (zetaQ N) = zetaQ N ^ p
  have hL : σ (zetaQ N)
      = ((MulSemiringAction.toAlgHom ℤ (NumberField.RingOfIntegers (CyclotomicQ N)) σ
          (zetaQ_spec N).toInteger : NumberField.RingOfIntegers (CyclotomicQ N)) :
          CyclotomicQ N) := by
    rw [MulSemiringAction.toAlgHom_apply,
      show ((σ • (zetaQ_spec N).toInteger : NumberField.RingOfIntegers (CyclotomicQ N)) :
          CyclotomicQ N) = σ ((zetaQ_spec N).toInteger : CyclotomicQ N) from rfl, hzcoe]
  rw [hL, key]
  simp

/-- The reciprocity map: transport of characters along the cyclotomic character. -/
noncomputable def reciprocityEquiv (N : ℕ) [NeZero N] :
    GaloisRepGL1 N ≃ DirichletCharacter ℂ N where
  toFun ρ := MulChar.equivToUnitHom.symm (ρ.comp (cycChar N).symm.toMonoidHom)
  invFun χ := (MulChar.equivToUnitHom χ).comp (cycChar N).toMonoidHom
  left_inv ρ := by ext σ; simp
  right_inv χ := by
    apply MulChar.equivToUnitHom.injective
    ext u
    simp

/-- **Langlands reciprocity, base case `n = 1` over `ℚ`.**

For every level `N ≥ 1` there is a bijection between the one dimensional Galois representations
of conductor dividing `N` (characters of `Gal(ℚ(ζ_N)/ℚ)`) and the automorphic representations of
`GL(1)/ℚ` of conductor dividing `N` (Dirichlet characters mod `N`), which is multiplicative and
matches local data: for every prime `p ∤ N` the Frobenius element at `p` exists, is unique, and
the value of the Galois character at it equals the value of the Dirichlet character at `p`. -/
theorem langlands_reciprocity (N : ℕ) [NeZero N] :
    ∃ e : GaloisRepGL1 N ≃ DirichletCharacter ℂ N,
      (∀ ρ₁ ρ₂ : GaloisRepGL1 N, e (ρ₁ * ρ₂) = e ρ₁ * e ρ₂) ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        (∃! σ : CyclotomicQ N ≃ₐ[ℚ] CyclotomicQ N, IsFrobeniusAt N p σ) ∧
        ∀ (ρ : GaloisRepGL1 N) (σ : CyclotomicQ N ≃ₐ[ℚ] CyclotomicQ N),
          IsFrobeniusAt N p σ → ((ρ σ : ℂ) = e ρ (p : ZMod N)) := by
  refine ⟨reciprocityEquiv N, ?_, ?_⟩
  · intro ρ₁ ρ₂
    show MulChar.equivToUnitHom.symm ((ρ₁ * ρ₂).comp (cycChar N).symm.toMonoidHom) = _
    rw [MonoidHom.mul_comp]
    exact map_mul (MulChar.mulEquivToUnitHom (R := ZMod N) (R' := ℂ)).symm _ _
  · intro p hp hpN
    have hcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).2 hpN
    refine ⟨exists_unique_isFrobeniusAt N hcop, ?_⟩
    intro ρ σ hσ
    have hu : ((p : ℕ) : ZMod N) = ((ZMod.unitOfCoprime p hcop : (ZMod N)ˣ) : ZMod N) :=
      (ZMod.coe_unitOfCoprime p hcop).symm
    show (ρ σ : ℂ)
      = MulChar.equivToUnitHom.symm (ρ.comp (cycChar N).symm.toMonoidHom) (p : ZMod N)
    rw [hu, MulChar.equivToUnitHom_symm_coe]
    have : (cycChar N).symm (ZMod.unitOfCoprime p hcop) = σ := by
      rw [← cycChar_frobenius N hcop hσ, MulEquiv.symm_apply_apply]
    simp [this]

/-- The Euler factors at an unramified prime of the Artin `L`-function of `ρ` and of the
Dirichlet `L`-function of the matching character agree. -/
theorem langlands_reciprocity_euler (N : ℕ) [NeZero N]
    (e : GaloisRepGL1 N ≃ DirichletCharacter ℂ N)
    (he : ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        (∃! σ : CyclotomicQ N ≃ₐ[ℚ] CyclotomicQ N, IsFrobeniusAt N p σ) ∧
        ∀ (ρ : GaloisRepGL1 N) (σ : CyclotomicQ N ≃ₐ[ℚ] CyclotomicQ N),
          IsFrobeniusAt N p σ → ((ρ σ : ℂ) = e ρ (p : ZMod N)))
    (ρ : GaloisRepGL1 N) (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (σ : CyclotomicQ N ≃ₐ[ℚ] CyclotomicQ N) (hσ : IsFrobeniusAt N p σ) (s : ℂ) :
    (1 - (ρ σ : ℂ) * (p : ℂ) ^ (-s))⁻¹ = (1 - e ρ (p : ZMod N) * (p : ℂ) ^ (-s))⁻¹ := by
  rw [(he p hp hpN).2 ρ σ hσ]

end Frontier

