import Mathlib

/-!
# Mod-2 Milnor K-theory of a field

For a field `F` we define
`k_n(F) = K^M_n(F)/2`, the `n`-th mod-2 Milnor K-group, as the quotient of the `n`-fold
tensor power over `𝔽₂` of the square class group `F^×/(F^×)²` by the Steinberg relations
`{a, 1-a} = 0`.
-/

open scoped TensorProduct

namespace MilnorK

variable (F : Type) [Field F]

/-- The subgroup of squares of `Fˣ`. -/

theorem exists_sqrt_of_finrank_two (L : IntermediateField F (Ksep F))
    (hL : Module.finrank F L = 2) :
    ∃ y : Ksep F, y ∈ L ∧ y ∉ (⊥ : IntermediateField F (Ksep F)) ∧
      ∃ a : F, y * y = algebraMap F (Ksep F) a := by
  haveI : FiniteDimensional F L := Module.finite_of_finrank_pos (by rw [hL]; norm_num)
  obtain ⟨x, hxL, hxbot⟩ : ∃ x : Ksep F, x ∈ L ∧ x ∉ (⊥ : IntermediateField F (Ksep F)) := by
    by_contra hcon
    push_neg at hcon
    have hbot : L = ⊥ := le_antisymm (fun x hx => hcon x hx) bot_le
    rw [hbot, IntermediateField.finrank_bot] at hL
    exact absurd hL (by norm_num)
  have hxint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hadj_le : F⟮ x ⟯ ≤ L := IntermediateField.adjoin_simple_le_iff.2 hxL
  haveI : FiniteDimensional F F⟮ x ⟯ := IntermediateField.adjoin.finiteDimensional hxint
  have hne1 : Module.finrank F F⟮ x ⟯ ≠ 1 := by
    intro h
    rw [IntermediateField.finrank_eq_one_iff] at h
    exact hxbot (h ▸ IntermediateField.mem_adjoin_simple_self F x)
  have hpos : 0 < Module.finrank F F⟮ x ⟯ := Module.finrank_pos
  have heq : F⟮ x ⟯ = L := IntermediateField.eq_of_le_of_finrank_le hadj_le (by omega)
  have hdeg : (minpoly F x).natDegree = 2 := by
    rw [← IntermediateField.adjoin.finrank hxint, heq, hL]
  have hc2 : (minpoly F x).coeff 2 = 1 := by
    rw [← hdeg]; exact (minpoly.monic hxint).coeff_natDegree
  have hsum := Polynomial.aeval_eq_sum_range (p := minpoly F x) x
  rw [minpoly.aeval, hdeg] at hsum
  simp [Finset.sum_range_succ, hc2, Algebra.smul_def] at hsum
  set b := (minpoly F x).coeff 1 with hb_def
  set c := (minpoly F x).coeff 0 with hc_def
  refine ⟨x + algebraMap F (Ksep F) (b / 2), ?_, ?_, b ^ 2 / 4 - c, ?_⟩
  · exact add_mem hxL (L.algebraMap_mem _)
  · intro hmem
    apply hxbot
    have : x = (x + algebraMap F (Ksep F) (b / 2)) - algebraMap F (Ksep F) (b / 2) := by ring
    rw [this]
    exact sub_mem hmem ((⊥ : IntermediateField F (Ksep F)).algebraMap_mem _)
  · have h2ne : (2 : Ksep F) ≠ 0 := NeZero.ne _
    have h4ne : (4 : Ksep F) ≠ 0 := by
      intro h
      apply h2ne
      have h' : (2 : Ksep F) * 2 = 0 := by linear_combination h
      rcases mul_eq_zero.1 h' with h'' | h'' <;> exact h''
    have hbm : algebraMap F (Ksep F) (b / 2) = algebraMap F (Ksep F) b / 2 := by
      rw [map_div₀, map_ofNat]
    have hA : algebraMap F (Ksep F) (b ^ 2 / 4 - c)
        = (algebraMap F (Ksep F) b) ^ 2 / 4 - algebraMap F (Ksep F) c := by
      rw [map_sub, map_div₀, map_pow, map_ofNat]
    rw [hbm, hA]
    field_simp
    linear_combination (-16 : Ksep F) * hsum

/-- Surjectivity of the Kummer map: every continuous homomorphism `G_F → ℤ/2` is `χ_a`
for some `a ∈ F^×`. -/
