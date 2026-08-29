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

theorem card_quotient_span (p : ℕ) :
    Nat.card (ℤ ⧸ Ideal.span {(p : ℤ)}) = p := by
  have h : Nat.card (ℤ ⧸ Ideal.span {(p : ℤ)}) = Nat.card (ZMod (p : ℤ).natAbs) :=
    Nat.card_congr (Int.quotientSpanEquivZMod (p : ℤ)).toEquiv
  rw [h]
  simp [Nat.card_zmod]

end Auxiliary

/-- If the residue of a prime `p` modulo `n` corresponds to `σ` under the embedding of the
Galois group of `L = ℚ(ζₙ)` into `(ZMod n)ˣ`, then any Frobenius element at a prime of `𝓞 L`
above `p` is equal to `σ`. -/
