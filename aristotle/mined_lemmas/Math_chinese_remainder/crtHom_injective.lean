import Mathlib

/-!
# Chinese Remainder
Category: Pure Mathematics
Target: Math.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Function

namespace Math

variable {ι : Type*} [Fintype ι]

/-- The natural reduction ring homomorphism `ℤ/(∏ i, n i) → ∏ i, ℤ/(n i)`. -/

lemma crtHom_injective (n : ι → ℕ) (hco : Pairwise (Nat.Coprime on n)) :
    Function.Injective (crtHom n) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  have hdvd : ∀ i : ι, ((n i : ℤ)) ∣ a := by
    intro i
    have h0 : ((a : ℤ) : ZMod (n i)) = 0 := by
      have := congrFun hx i
      rwa [crtHom_intCast] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd a (n i)).mp h0
  have hpair : ((Finset.univ : Finset ι) : Set ι).Pairwise
      (Function.onFun IsCoprime fun i => ((n i : ℤ))) := by
    intro i _ j _ hij
    exact Nat.isCoprime_iff_coprime.mpr (hco hij)
  have hprod : (∏ i, ((n i : ℤ))) ∣ a :=
    Finset.prod_dvd_of_coprime hpair fun i _ => hdvd i
  have hcast : ((∏ i, n i : ℕ) : ℤ) ∣ a := by
    rw [Nat.cast_prod]; exact hprod
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd a (∏ i, n i)).mpr hcast

/-- When all the moduli are positive, the natural reduction map is bijective. -/
