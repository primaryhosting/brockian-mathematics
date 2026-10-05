/-
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open NumberField IsCyclotomicExtension

namespace Math2

section Auxiliary

/-- In a Galois number field `L`, the elements of the ring of integers fixed by the whole
Galois group are exactly the (images of the) rational integers. -/
instance isInvariant_ringOfIntegers (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [IsGalois ℚ L] : Algebra.IsInvariant ℤ (𝓞 L) (L ≃ₐ[ℚ] L) := by
  constructor
  intro x hx
  have hfix : ∀ g : L ≃ₐ[ℚ] L, g (x : L) = (x : L) := fun g =>
    congrArg (fun y : 𝓞 L => (y : L)) (hx g)
  obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := ℚ) (E := L) (x : L)).2 hfix
  have hint : IsIntegral ℤ a := by
    have hxint : IsIntegral ℤ (x : L) := x.2
    rw [← ha] at hxint
    exact (isIntegral_algebraMap_iff (algebraMap ℚ L).injective).1 hxint
  obtain ⟨m, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine ⟨m, Subtype.ext ?_⟩
  show (algebraMap ℤ (𝓞 L) m : L) = (x : L)
  rw [← ha]
  simp

/-- Every rational prime lies under some prime ideal of the ring of integers. -/

theorem chebotarev_arithFrobAt (n : ℕ) [NeZero n] (L : Type*) [Field L] [NumberField L]
    [Algebra ℚ L] [IsCyclotomicExtension {n} ℚ L] [IsGalois ℚ L] (σ : L ≃ₐ[ℚ] L) :
    {p : ℕ | p.Prime ∧ ∃ (Q : Ideal (𝓞 L)) (hQ : Q.IsPrime) (hf : Finite (𝓞 L ⧸ Q)),
      Ideal.under ℤ Q = Ideal.span {(p : ℤ)} ∧
        letI := hQ; letI := hf; arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q = σ}.Infinite := by
  have hζ : IsPrimitiveRoot (zeta n ℚ L) n := zeta_spec n ℚ L
  refine Set.Infinite.mono ?_ (Nat.infinite_setOf_prime_and_eq_mod (q := n)
    (a := ((hζ.autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)) (Units.isUnit _))
  rintro p ⟨hp, hpu⟩
  refine ⟨hp, ?_⟩
  obtain ⟨Q, hQprime, hQunder⟩ := exists_prime_over L hp
  haveI : Q.IsPrime := hQprime
  have hQbot : Q ≠ ⊥ := by
    intro h
    have hmem : ((p : ℤ)) ∈ Ideal.under ℤ Q := by
      rw [hQunder]; exact Ideal.mem_span_singleton_self _
    rw [h] at hmem
    have hz : ((p : ℤ)) = 0 := by
      simpa [Ideal.under, Ideal.mem_comap] using hmem
    exact hp.ne_zero (by exact_mod_cast hz)
  haveI hfin : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQbot
  exact ⟨Q, hQprime, hfin, hQunder,
    eq_of_isArithFrobAt n L hp hQunder (IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) hpu⟩

end Math2

import Mathlib

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

