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
def crtHom (n : ι → ℕ) : ZMod (∏ i, n i) →+* ∀ i, ZMod (n i) :=
  Pi.ringHom fun i =>
    ZMod.castHom (Finset.dvd_prod_of_mem n (Finset.mem_univ i)) (ZMod (n i))

@[simp]
lemma crtHom_intCast (n : ι → ℕ) (a : ℤ) (i : ι) :
    crtHom n (a : ZMod (∏ i, n i)) i = (a : ZMod (n i)) := by
  have : crtHom n (a : ZMod (∏ i, n i)) = ((a : ℤ) : ∀ i, ZMod (n i)) := by
    simp [map_intCast]
  rw [this]
  simp

/-- The natural reduction map is injective when the moduli are pairwise coprime. -/
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
lemma crtHom_bijective_of_pos (n : ι → ℕ) (hco : Pairwise (Nat.Coprime on n))
    (hpos : ∀ i, 0 < n i) : Function.Bijective (crtHom n) := by
  classical
  haveI : ∀ i, NeZero (n i) := fun i => ⟨(hpos i).ne'⟩
  haveI : NeZero (∏ i, n i) := ⟨Finset.prod_ne_zero_iff.mpr fun i _ => (hpos i).ne'⟩
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨crtHom_injective n hco, ?_⟩
  rw [ZMod.card, Fintype.card_pi]
  exact Finset.prod_congr rfl fun i _ => (ZMod.card (n i)).symm

omit [Fintype ι] in
/-- If one modulus is zero, evaluation at that index is a bijection of `∏ i, ℤ/(n i)`
onto `ℤ/(n i₀)`, since all other moduli are then `1`. -/
lemma evalRingHom_bijective_of_zero (n : ι → ℕ) (hco : Pairwise (Nat.Coprime on n))
    {i₀ : ι} (h0 : n i₀ = 0) :
    Function.Bijective (Pi.evalRingHom (fun i => ZMod (n i)) i₀) := by
  classical
  have hone : ∀ j, j ≠ i₀ → n j = 1 := by
    intro j hj
    have := hco (Ne.symm hj)
    simp only [Function.onFun, Nat.Coprime, h0, Nat.gcd_zero_left] at this
    exact this
  have hsub : ∀ j, j ≠ i₀ → Subsingleton (ZMod (n j)) := by
    intro j hj
    rw [hone j hj]
    infer_instance
  constructor
  · intro y y' hyy'
    funext j
    by_cases hj : j = i₀
    · subst hj; exact hyy'
    · haveI := hsub j hj; exact Subsingleton.elim _ _
  · intro z
    refine ⟨Function.update 0 i₀ z, ?_⟩
    simp

/-- **Chinese remainder theorem.**  For pairwise coprime moduli `n i`, the ring
`ℤ/(∏ i, n i)` is isomorphic to the product ring `∏ i, ℤ/(n i)`; moreover the
isomorphism is the natural one, sending the class of an integer `x` to the tuple
of its classes modulo each `n i`. -/
theorem chinese_remainder (n : ι → ℕ) (hco : Pairwise (Nat.Coprime on n)) :
    ∃ e : ZMod (∏ i, n i) ≃+* ∀ i, ZMod (n i),
      ∀ (x : ℤ) (i : ι), e ((x : ZMod (∏ i, n i))) i = (x : ZMod (n i)) := by
  classical
  -- Compatibility with the integer casts is automatic for any ring isomorphism.
  suffices h : Nonempty (ZMod (∏ i, n i) ≃+* ∀ i, ZMod (n i)) by
    obtain ⟨e⟩ := h
    refine ⟨e, fun x i => ?_⟩
    have : e ((x : ZMod (∏ i, n i))) = ((x : ℤ) : ∀ i, ZMod (n i)) := by
      simp [map_intCast]
    rw [this]
    simp
  by_cases hpos : ∀ i, 0 < n i
  · exact ⟨RingEquiv.ofBijective (crtHom n) (crtHom_bijective_of_pos n hco hpos)⟩
  · push_neg at hpos
    obtain ⟨i₀, hi₀⟩ := hpos
    have h0 : n i₀ = 0 := Nat.le_zero.mp hi₀
    have hN : ∏ i, n i = n i₀ :=
      (Finset.prod_eq_zero (Finset.mem_univ i₀) h0).trans h0.symm
    exact ⟨(ZMod.ringEquivCongr hN).trans
      (RingEquiv.ofBijective _ (evalRingHom_bijective_of_zero n hco h0)).symm⟩

end Math

