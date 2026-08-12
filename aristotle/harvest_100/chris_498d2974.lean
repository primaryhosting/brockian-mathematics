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
theorem card_rootsOfUnity_qbar (N : ℕ) [NeZero N] :
    Fintype.card {x // x ∈ rootsOfUnity N QBar} = N :=
  (HasEnoughRootsOfUnity.prim (M := QBar) (n := N)).choose_spec.card_rootsOfUnity

/-- The mod `N` cyclotomic character `Gal(ℚ̄/ℚ) →* (ZMod N)ˣ`: it sends `σ` to the unique
unit `u` with `σ ζ = ζ ^ u` for every `N`-th root of unity `ζ`. -/
noncomputable def cycloChar (N : ℕ) [NeZero N] : GalQ →* (ZMod N)ˣ :=
  (modularCyclotomicCharacter QBar (card_rootsOfUnity_qbar N)).comp
    (⟨⟨AlgEquiv.toRingEquiv, rfl⟩, fun _ _ => rfl⟩ : GalQ →* (QBar ≃+* QBar))

/-- The defining property of the mod `N` cyclotomic character. -/
theorem cycloChar_spec (N : ℕ) [NeZero N] (σ : GalQ) {t : QBarˣ} (ht : t ∈ rootsOfUnity N QBar) :
    σ (t : QBar) = (t : QBar) ^ ((cycloChar N σ : ZMod N)).val :=
  modularCyclotomicCharacter.spec QBar (card_rootsOfUnity_qbar N) σ.toRingEquiv ht

/-- The mod `N` cyclotomic character of `ℚ` is surjective: this is the irreducibility of
the `N`-th cyclotomic polynomial over `ℚ`, i.e. `Gal(ℚ(ζ_N)/ℚ) ≃ (ZMod N)ˣ`. -/
theorem cycloChar_surjective (N : ℕ) [NeZero N] : Function.Surjective (cycloChar N) := by
  intro u
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.prim (M := QBar) (n := N)
  set k := ((u : ZMod N)).val with hk
  have hcop : Nat.Coprime k N := ZMod.val_coe_unit_coprime u
  have hzk : IsPrimitiveRoot (z ^ k) N := hz.pow_of_coprime k hcop
  have hmin : minpoly ℚ (z ^ k) = minpoly ℚ z := by
    rw [← cyclotomic_eq_minpoly_rat hzk (Nat.pos_of_neZero N),
      ← cyclotomic_eq_minpoly_rat hz (Nat.pos_of_neZero N)]
  obtain ⟨σ, hσ⟩ := IsConjRoot.exists_algEquiv (K := ℚ) (L := QBar) (x := z ^ k) (y := z)
    (by rw [IsConjRoot, hmin])
  refine ⟨σ, ?_⟩
  have key : ((u : ZMod N)) =
      (modularCyclotomicCharacter QBar (card_rootsOfUnity_qbar N) σ.toRingEquiv : ZMod N) := by
    apply modularCyclotomicCharacter.unique
    intro t ht
    have ht' : ((t : QBar)) ^ N = 1 := by
      simpa using congrArg Units.val ((mem_rootsOfUnity N t).1 ht)
    obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one ht'
    show σ (t : QBar) = _
    rw [← hi, map_pow, hσ, ← pow_mul, ← pow_mul, Nat.mul_comm]
  exact Units.ext key.symm

/-- The action of `σ` on a primitive `N`-th root of unity is raising to the power given by
the mod `N` cyclotomic character. -/
theorem cycloChar_spec_primitiveRoot (N : ℕ) [NeZero N] (σ : GalQ) {z : QBar}
    (hz : IsPrimitiveRoot z N) : σ z = z ^ ((cycloChar N σ : ZMod N)).val := by
  show σ.toRingEquiv z = _
  rw [modularCyclotomicCharacter.toFun_spec'' σ.toRingEquiv hz]
  congr 1
  exact (ZMod.ringEquivCongr_val _ _).symm

/-- The kernel of the mod `N` cyclotomic character is `Gal(ℚ̄/ℚ(ζ_N))`: it consists of the
automorphisms fixing a primitive `N`-th root of unity. -/
theorem mem_ker_cycloChar_iff (N : ℕ) [NeZero N] {z : QBar} (hz : IsPrimitiveRoot z N) (σ : GalQ) :
    σ ∈ MonoidHom.ker (cycloChar N) ↔ σ z = z := by
  have hz1 : N = 1 → z = 1 := by
    intro h
    have := hz.pow_eq_one
    rw [h] at this
    simpa using this
  constructor
  · intro h
    have h1 : ((cycloChar N σ : ZMod N)) = 1 := by rw [h]; rfl
    have hs := cycloChar_spec_primitiveRoot N σ hz
    rw [h1] at hs
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 (NeZero.ne N)) with h2 | h2
    · simp [hz1 h2.symm]
    · rwa [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h2, pow_one] at hs
  · intro h
    have key : ((1 : ZMod N)) = (cycloChar N σ : ZMod N) := by
      apply modularCyclotomicCharacter.unique
      intro t ht
      have ht' : ((t : QBar)) ^ N = 1 := by
        simpa using congrArg Units.val ((mem_rootsOfUnity N t).1 ht)
      obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one ht'
      show σ (t : QBar) = _
      rw [← hi, map_pow, h]
      rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 (NeZero.ne N)) with h2 | h2
      · simp [hz1 h2.symm]
      · rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h2, pow_one]
    exact Units.ext key.symm

/-- The mod `N` cyclotomic character is continuous: its kernel is open, being the Galois
group of `ℚ̄` over the finite extension `ℚ(ζ_N)` of `ℚ`. -/
theorem isOpen_ker_cycloChar (N : ℕ) [NeZero N] :
    IsOpen (MonoidHom.ker (cycloChar N) : Set GalQ) := by
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.prim (M := QBar) (n := N)
  have hset : (MonoidHom.ker (cycloChar N) : Set GalQ)
      = (MulAction.stabilizer GalQ z : Set GalQ) := by
    ext σ
    simp only [SetLike.mem_coe, mem_ker_cycloChar_iff N hz, MulAction.mem_stabilizer_iff]
    rfl
  rw [hset]
  exact stabilizer_isOpen_of_isIntegral z

/-!
### The reciprocity map
-/

/-- The Galois character attached to a Dirichlet character mod `N` (equivalently, to a
finite-order Hecke character of `ℚ` of conductor dividing `N`, i.e. an automorphic
representation of `GL 1` over `ℚ`): compose `χ` with the mod `N` cyclotomic character. -/
noncomputable def galoisCharOfDirichlet (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) :
    GalQ →* ℂˣ :=
  χ.toUnitHom.comp (cycloChar N)

@[simp]
theorem galoisCharOfDirichlet_apply (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (σ : GalQ) :
    (galoisCharOfDirichlet N χ σ : ℂ) = χ ((cycloChar N σ : ZMod N)) :=
  MulChar.coe_toUnitHom χ _

/-- The Galois character attached to a Dirichlet character is continuous: its kernel is
open, since it contains the (open) kernel of the mod `N` cyclotomic character. -/
theorem isOpen_ker_galoisCharOfDirichlet (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) :
    IsOpen (MonoidHom.ker (galoisCharOfDirichlet N χ) : Set GalQ) := by
  refine Subgroup.isOpen_mono (H₁ := MonoidHom.ker (cycloChar N)) ?_ (isOpen_ker_cycloChar N)
  intro σ hσ
  simp only [MonoidHom.mem_ker] at hσ ⊢
  simp [galoisCharOfDirichlet, hσ]

/-- `σ` is a Frobenius element at `p` for the level `N` cyclotomic tower: it acts on `N`-th
roots of unity by `ζ ↦ ζ ^ p`. -/
def IsFrobeniusAt (N p : ℕ) (σ : GalQ) [NeZero N] : Prop :=
  ((cycloChar N σ : ZMod N)) = (p : ZMod N)

theorem pow_eq_pow_of_modEq {n i j : ℕ} {z : QBar} (hz : IsPrimitiveRoot z n)
    (h : i ≡ j [MOD n]) : z ^ i = z ^ j := by
  rw [← Nat.mod_add_div i n, ← Nat.mod_add_div j n, pow_add, pow_add, pow_mul, pow_mul,
    hz.pow_eq_one, one_pow, one_pow, mul_one, mul_one, h]

/-- Being a Frobenius element at `m` means exactly acting on the `N`-th roots of unity by
`ζ ↦ ζ ^ m`, which for a prime `p ∤ N` is the usual arithmetic Frobenius of the cyclotomic
extension. -/
theorem isFrobeniusAt_iff (N m : ℕ) [NeZero N] (σ : GalQ) {z : QBar} (hz : IsPrimitiveRoot z N) :
    IsFrobeniusAt N m σ ↔ σ z = z ^ m := by
  have hs := cycloChar_spec_primitiveRoot N σ hz
  constructor
  · intro h
    have hmod : ((cycloChar N σ : ZMod N)).val ≡ m [MOD N] := by
      rw [Nat.ModEq, ← ZMod.natCast_eq_natCast_iff']
      simpa using h
    rw [hs]
    exact pow_eq_pow_of_modEq hz hmod
  · intro h
    rw [hs] at h
    have h2 : z ^ ((cycloChar N σ : ZMod N)).val = z ^ (m % N) :=
      h.trans (pow_eq_pow_of_modEq hz (Nat.mod_modEq m N).symm)
    have h3 := hz.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (Nat.pos_of_neZero N)) h2
    have h4 : ((((cycloChar N σ : ZMod N)).val : ℕ) : ZMod N) = (m : ZMod N) := by
      rw [h3, ZMod.natCast_mod]
    simpa using h4

/-- Frobenius elements exist at every prime (indeed every natural number) coprime to `N`. -/
theorem exists_isFrobeniusAt (N p : ℕ) [NeZero N] (hp : Nat.Coprime p N) :
    ∃ σ : GalQ, IsFrobeniusAt N p σ := by
  obtain ⟨σ, hσ⟩ := cycloChar_surjective N (ZMod.unitOfCoprime p hp)
  refine ⟨σ, ?_⟩
  show ((cycloChar N σ : ZMod N)) = (p : ZMod N)
  rw [hσ, ZMod.coe_unitOfCoprime]

/-- The Artin `L`-series coefficients of a Galois character `ρ` unramified outside `N`:
the coefficient at `m` is `ρ (Frob_m)` when `m` is prime to `N`, and `0` otherwise. -/
noncomputable def artinCoeff (N : ℕ) [NeZero N] (ρ : GalQ →* ℂˣ) (m : ℕ) : ℂ :=
  if h : IsUnit ((m : ZMod N)) then
    (ρ (Classical.choose (cycloChar_surjective N h.unit)) : ℂ)
  else 0

/-!
### The main theorem: reciprocity at level `N`
-/

/-- Every Galois character trivial on the kernel of the mod `N` cyclotomic character
comes from a Dirichlet character mod `N`. -/
theorem exists_dirichletCharacter (N : ℕ) [NeZero N] (ρ : GalQ →* ℂˣ)
    (hρ : MonoidHom.ker (cycloChar N) ≤ MonoidHom.ker ρ) :
    ∃ χ : DirichletCharacter ℂ N, galoisCharOfDirichlet N χ = ρ := by
  classical
  set e := QuotientGroup.quotientKerEquivOfSurjective (cycloChar N) (cycloChar_surjective N)
  set f : (ZMod N)ˣ →* ℂˣ :=
    (QuotientGroup.lift (MonoidHom.ker (cycloChar N)) ρ hρ).comp
      (e.symm.toMonoidHom) with hf
  refine ⟨MulChar.ofUnitHom f, MonoidHom.ext fun σ => ?_⟩
  have hσ : e.symm (cycloChar N σ) = (QuotientGroup.mk σ : GalQ ⧸ MonoidHom.ker (cycloChar N)) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have h2 : (MulChar.ofUnitHom f).toUnitHom = f := by
    simp [MulChar.ofUnitHom_eq, MulChar.toUnitHom_eq]
  show (MulChar.ofUnitHom f).toUnitHom (cycloChar N σ) = ρ σ
  rw [h2, hf]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, hσ]
  rfl

/-- The reciprocity map is injective at each level. -/
theorem galoisCharOfDirichlet_injective (N : ℕ) [NeZero N] :
    Function.Injective (galoisCharOfDirichlet N) := by
  intro χ₁ χ₂ h
  refine (DirichletCharacter.toUnitHom_inj χ₁ χ₂).1 ?_
  ext u
  obtain ⟨σ, rfl⟩ := cycloChar_surjective N u
  exact congrArg (fun ρ : GalQ →* ℂˣ => ((ρ σ : ℂˣ) : ℂ)) h

/-- Frobenius eigenvalues of the attached Galois character are the Hecke eigenvalues
`χ p` of the automorphic side. -/
theorem galoisCharOfDirichlet_frobenius (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (σ : GalQ) (m : ℕ) (h : IsFrobeniusAt N m σ) :
    (galoisCharOfDirichlet N χ σ : ℂ) = χ (m : ZMod N) := by
  rw [galoisCharOfDirichlet_apply, h]

/-- Matching of `L`-functions, coefficientwise: the Artin `L`-series of the Galois
character attached to `χ` is the Dirichlet `L`-series of `χ`. -/
theorem artinCoeff_galoisCharOfDirichlet (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (m : ℕ) : artinCoeff N (galoisCharOfDirichlet N χ) m = χ (m : ZMod N) := by
  classical
  unfold artinCoeff
  split_ifs with h
  · have hσ := Classical.choose_spec (cycloChar_surjective N h.unit)
    rw [galoisCharOfDirichlet_apply, hσ]
    simp
  · exact (MulChar.map_nonunit χ h).symm

/-- The Artin `L`-series of the Galois character attached to a Dirichlet character `χ`
coincides with the Dirichlet `L`-series of `χ`. -/
theorem LSeries_artinCoeff (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    LSeries (artinCoeff N (galoisCharOfDirichlet N χ)) s = LSeries (fun m => χ (m : ZMod N)) s := by
  refine congrArg (fun a => LSeries a s) ?_
  funext m
  exact artinCoeff_galoisCharOfDirichlet N χ m

/--
**Langlands reciprocity for `GL 1` over `ℚ`, at level `N`** (Artin reciprocity in the
cyclotomic case).

For every `N ≥ 1`:

0. the reciprocity map takes values in *continuous* characters of `Gal(ℚ̄/ℚ)` (open kernel
   for the Krull topology);
1. the reciprocity map `χ ↦ χ ∘ cycloChar N`, from automorphic representations of
   `GL 1` over `ℚ` of finite order and conductor dividing `N` (i.e. Dirichlet characters
   mod `N`) to complex characters of `Gal(ℚ̄/ℚ)`, is injective;
2. it surjects onto the Galois characters unramified outside `N`, i.e. those trivial on
   the kernel of the mod `N` cyclotomic character (equivalently, cut out by `ℚ(ζ_N)`);
3. it matches local data: the value at a Frobenius element at `m` is the Hecke eigenvalue
   `χ m`;
4. consequently it matches `L`-functions: the Artin `L`-series of the attached Galois
   character is the Dirichlet `L`-series of `χ`.
-/
theorem langlands_reciprocity (N : ℕ) [NeZero N] :
    (∀ χ : DirichletCharacter ℂ N,
        IsOpen (MonoidHom.ker (galoisCharOfDirichlet N χ) : Set GalQ)) ∧
    Function.Injective (galoisCharOfDirichlet N) ∧
    (∀ ρ : GalQ →* ℂˣ, MonoidHom.ker (cycloChar N) ≤ MonoidHom.ker ρ →
        ∃ χ : DirichletCharacter ℂ N, galoisCharOfDirichlet N χ = ρ) ∧
    (∀ (χ : DirichletCharacter ℂ N) (σ : GalQ) (m : ℕ), IsFrobeniusAt N m σ →
        (galoisCharOfDirichlet N χ σ : ℂ) = χ (m : ZMod N)) ∧
    (∀ (χ : DirichletCharacter ℂ N) (s : ℂ),
        LSeries (artinCoeff N (galoisCharOfDirichlet N χ)) s
          = LSeries (fun m => χ (m : ZMod N)) s) :=
  ⟨isOpen_ker_galoisCharOfDirichlet N, galoisCharOfDirichlet_injective N,
    exists_dirichletCharacter N,
    fun χ σ m h => galoisCharOfDirichlet_frobenius N χ σ m h, LSeries_artinCoeff N⟩

/-!
### The full abelian conjecture, and a reduction
-/

/-- **Langlands reciprocity for `GL 1` over `ℚ`** (the abelian case of the Langlands
reciprocity conjecture; a theorem of class field theory): every continuous character of
the absolute Galois group of `ℚ` (continuity for the Krull topology being the openness of
the kernel) is the Galois character attached to a Dirichlet character, i.e. to an
automorphic representation of `GL 1` over `ℚ`. -/
def LanglandsReciprocityGL1 : Prop :=
  ∀ ρ : GalQ →* ℂˣ, IsOpen (MonoidHom.ker ρ : Set GalQ) →
    ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N), galoisCharOfDirichlet N χ = ρ

/-- **Reduction of abelian Langlands reciprocity to Kronecker–Weber.** If every continuous
character of `Gal(ℚ̄/ℚ)` is trivial on the kernel of some mod `N` cyclotomic character
(i.e. is cut out by a cyclotomic field), then Langlands reciprocity for `GL 1` over `ℚ`
holds. -/
theorem langlands_reciprocity_gl1_of_kroneckerWeber
    (KW : ∀ ρ : GalQ →* ℂˣ, IsOpen (MonoidHom.ker ρ : Set GalQ) →
      ∃ (N : ℕ) (_ : NeZero N), MonoidHom.ker (cycloChar N) ≤ MonoidHom.ker ρ) :
    LanglandsReciprocityGL1 := by
  intro ρ hρ
  obtain ⟨N, hN, hker⟩ := KW ρ hρ
  obtain ⟨χ, hχ⟩ := exists_dirichletCharacter N ρ hker
  exact ⟨N, hN, χ, hχ⟩

end Frontier

