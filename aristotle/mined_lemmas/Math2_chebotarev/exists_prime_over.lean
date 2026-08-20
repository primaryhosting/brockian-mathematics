import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math2

open NumberField

section NumberFields

variable (L : Type*) [Field L] [NumberField L]

/-- The group of `ℤ`-algebra automorphisms of the ring of integers of a number field is
finite. -/

lemma exists_prime_over {p : ℕ} (hp : p.Prime) :
    ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Ideal.under ℤ Q = Ideal.span {(p : ℤ)} ∧ Finite (𝓞 L ⧸ Q) := by
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hp
  obtain ⟨Q, -, hQp, hQu⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := ℤ) (S := 𝓞 L) (Ideal.span {(p : ℤ)}) ⊥
      ((Ideal.comap_bot_le_of_injective _ (FaithfulSMul.algebraMap_injective ℤ _)).trans bot_le)
  refine ⟨Q, hQp, hQu, ?_⟩
  have hbot : Q ≠ ⊥ := by
    intro h
    rw [h] at hQu
    have hmem : ((p : ℤ)) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton_self _
    rw [← hQu] at hmem
    simp only [Ideal.mem_comap, Ideal.mem_bot] at hmem
    have hinj : Function.Injective (algebraMap ℤ (𝓞 L)) := FaithfulSMul.algebraMap_injective _ _
    have hp0 := hinj (by simpa using hmem : algebraMap ℤ (𝓞 L) p = algebraMap ℤ _ 0)
    exact hp.ne_zero (by exact_mod_cast hp0)
  exact Ideal.finiteQuotientOfFreeOfNeBot Q hbot

end NumberFields

section Cyclotomic

variable (n : ℕ) [NeZero n] (L : Type*) [Field L] [NumberField L]
  [IsCyclotomicExtension {n} ℚ L]

omit [NeZero n] in
include n in
/-- A cyclotomic extension of `ℚ` is Galois. -/
