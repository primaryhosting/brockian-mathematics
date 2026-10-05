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

open Complex IsCyclotomicExtension

/-! ## Setting

Langlands reciprocity predicts a bijection between `n`-dimensional complex representations of
the absolute Galois group of a number field and automorphic representations of `GLₙ`, matching
Artin `L`-functions with automorphic `L`-functions, and matching, at each unramified place, the
Frobenius conjugacy class with the Satake parameter of the local component.

We formalise and *prove* the abelian base case `n = 1` over `ℚ`, in its cyclotomic incarnation:
one-dimensional complex representations of `Gal(ℚ(ζ_N)/ℚ)` correspond bijectively to automorphic
representations of `GL₁/ℚ` of conductor dividing `N`, i.e. to Dirichlet characters mod `N`,
in a way which is compatible with Frobenius elements at all unramified primes and which
identifies the Artin `L`-function with the automorphic (Dirichlet) `L`-function.
-/

section

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {N} ℚ K]

/-- A one-dimensional complex representation of the Galois group `Gal(ℚ(ζ_N)/ℚ)`
(the "Galois side" of the correspondence in the abelian case). -/
abbrev GaloisChar : Type _ := (K ≃ₐ[ℚ] K) →* ℂˣ

/-- The (arithmetic) Frobenius at an unramified prime `p`, i.e. a prime not dividing `N`:
it is the unique element of `Gal(ℚ(ζ_N)/ℚ)` acting on `N`-th roots of unity by `ζ ↦ ζ ^ p`. -/
noncomputable def frob {p : ℕ} (hp : Nat.Coprime p N) : K ≃ₐ[ℚ] K :=
  (IsCyclotomicExtension.Rat.galEquivZMod N K).symm (ZMod.unitOfCoprime p hp)

/-- `frob` deserves its name: at an unramified prime `p` it acts on the `N`-th roots of unity
by `x ↦ x ^ p`, i.e. it is the arithmetic Frobenius at `p`. -/
theorem frob_apply_of_pow_eq_one {p : ℕ} (hp : Nat.Coprime p N) {x : K} (hx : x ^ N = 1) :
    (frob N K hp) x = x ^ p := by
  have h := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N K (frob N K hp) hx
  rw [frob, MulEquiv.apply_symm_apply] at h
  rw [frob, h, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  conv_rhs => rw [← Nat.div_add_mod p N, pow_add, pow_mul, hx, one_pow, one_mul]

/-- The local Euler factor at `p` of the Artin `L`-function of a one-dimensional Galois
representation `ρ`: at unramified primes it is `(1 - ρ(Frob_p) p^{-s})⁻¹`, and at the ramified
primes (those dividing `N`, where the inertia invariants vanish for a faithful character) it is
taken to be `1`. -/
noncomputable def artinEulerFactor (ρ : GaloisChar K) (p : ℕ) (s : ℂ) : ℂ :=
  if h : Nat.Coprime p N then (1 - (ρ (frob N K h) : ℂ) * (p : ℂ) ^ (-s))⁻¹ else 1

/-- The reciprocity map itself: a Galois character `ρ` of `Gal(ℚ(ζ_N)/ℚ)` is transported, along
the cyclotomic isomorphism `Gal(ℚ(ζ_N)/ℚ) ≃* (ℤ/Nℤ)ˣ` of class field theory, to a Dirichlet
character mod `N` (= an automorphic representation of `GL₁/ℚ` of conductor dividing `N`). -/
noncomputable def recip : GaloisChar K ≃ DirichletCharacter ℂ N :=
  (MulEquiv.monoidHomCongrLeftEquiv
    (IsCyclotomicExtension.Rat.galEquivZMod N K)).trans MulChar.equivToUnitHom.symm

/-- Local–global compatibility of `Frontier.recip` at an unramified prime `p`: the automorphic
character `recip ρ` takes at `p` the value of `ρ` at the Frobenius element `Frob_p`. -/
theorem recip_apply_coe_of_coprime (ρ : GaloisChar K) {p : ℕ} (hp : Nat.Coprime p N) :
    (recip N K ρ) (p : ZMod N) = (ρ (frob N K hp) : ℂ) := by
  have : ((ZMod.unitOfCoprime p hp : (ZMod N)ˣ) : ZMod N) = (p : ZMod N) :=
    ZMod.coe_unitOfCoprime p hp
  rw [← this, recip, Equiv.trans_apply, MulChar.equivToUnitHom_symm_coe]
  rfl

/-- At a ramified prime (one dividing `N`) the automorphic character vanishes. -/
theorem recip_apply_coe_of_not_coprime (ρ : GaloisChar K) {p : ℕ} (hp : ¬ Nat.Coprime p N) :
    (recip N K ρ) (p : ZMod N) = 0 :=
  MulChar.map_nonunit _ (fun h ↦ hp ((ZMod.isUnit_iff_coprime p N).mp h))

end

/-- **Langlands reciprocity, the abelian base case (`GL₁` over `ℚ`).**

For every modulus `N` and every cyclotomic field `K = ℚ(ζ_N)` there is a bijection
`recip` between the one-dimensional complex representations of the Galois group `Gal(ℚ(ζ_N)/ℚ)`
and the automorphic representations of `GL₁/ℚ` of conductor dividing `N`, i.e. the Dirichlet
characters mod `N`, such that:

* (local–global compatibility) for every prime `p` unramified in `K`, the value of the Galois
  character at the Frobenius element `Frob_p` equals the value of the corresponding automorphic
  character at `p` (its Satake parameter);
* (equality of `L`-functions) for `Re s > 1` the Artin `L`-function of `ρ`, given by its Euler
  product over all primes, converges to the automorphic `L`-function `L(recip ρ, s)`. -/
theorem langlands_reciprocity (N : ℕ) [NeZero N] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {N} ℚ K] :
    ∃ recip : GaloisChar K ≃ DirichletCharacter ℂ N,
      (∀ (ρ : GaloisChar K) (p : ℕ), p.Prime → ∀ hp : Nat.Coprime p N,
          (ρ (frob N K hp) : ℂ) = recip ρ (p : ZMod N)) ∧
      (∀ (ρ : GaloisChar K) (s : ℂ), 1 < s.re →
          HasProd (fun p : Nat.Primes ↦ artinEulerFactor N K ρ p s)
            (LSeries (fun m : ℕ ↦ (recip ρ) (m : ZMod N)) s)) := by
  refine ⟨recip N K, fun ρ p _ hp ↦ (recip_apply_coe_of_coprime N K ρ hp).symm, ?_⟩
  intro ρ s hs
  have key : (fun p : Nat.Primes ↦ artinEulerFactor N K ρ p s) =
      fun p : Nat.Primes ↦ (1 - (recip N K ρ) ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
    funext p
    rw [artinEulerFactor]
    by_cases h : Nat.Coprime (p : ℕ) N
    · rw [dif_pos h, recip_apply_coe_of_coprime N K ρ h]
    · rw [dif_neg h, recip_apply_coe_of_not_coprime N K ρ h]
      simp
  rw [key]
  exact DirichletCharacter.LSeries_eulerProduct_hasProd (recip N K ρ) hs

/-- The concrete instance of `Frontier.langlands_reciprocity` for the cyclotomic field
`ℚ(ζ_N)` itself; in particular the hypotheses of the theorem are satisfiable. -/
theorem langlands_reciprocity_cyclotomicField (N : ℕ) [NeZero N] :
    ∃ recip : GaloisChar (CyclotomicField N ℚ) ≃ DirichletCharacter ℂ N,
      (∀ (ρ : GaloisChar (CyclotomicField N ℚ)) (p : ℕ), p.Prime → ∀ hp : Nat.Coprime p N,
          (ρ (frob N (CyclotomicField N ℚ) hp) : ℂ) = recip ρ (p : ZMod N)) ∧
      (∀ (ρ : GaloisChar (CyclotomicField N ℚ)) (s : ℂ), 1 < s.re →
          HasProd (fun p : Nat.Primes ↦ artinEulerFactor N (CyclotomicField N ℚ) ρ p s)
            (LSeries (fun m : ℕ ↦ (recip ρ) (m : ZMod N)) s)) :=
  langlands_reciprocity N (CyclotomicField N ℚ)

end Frontier

#print axioms Frontier.langlands_reciprocity
#print axioms Frontier.langlands_reciprocity_cyclotomicField

