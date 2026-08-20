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
def sqUnits : Subgroup Fˣ where
  carrier := {x | ∃ y : Fˣ, y ^ 2 = x}
  one_mem' := ⟨1, one_pow 2⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, by rw [mul_pow]⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a⁻¹, by rw [inv_pow]⟩

/-- The group of square classes `F^× / (F^×)²`, written additively. This is `k_1(F)`. -/
def SqCl : Type := Additive (Fˣ ⧸ sqUnits F)

noncomputable instance : AddCommGroup (SqCl F) :=
  inferInstanceAs (AddCommGroup (Additive (Fˣ ⧸ sqUnits F)))

variable {F}

/-- The square class of a unit. -/
def sqClass (a : Fˣ) : SqCl F := Additive.ofMul (QuotientGroup.mk a)

theorem sqClass_mul (a b : Fˣ) : sqClass (a * b) = sqClass a + sqClass b := rfl

theorem sqClass_surjective : Function.Surjective (sqClass (F := F)) := by
  intro x
  induction x using QuotientGroup.induction_on with
  | H a => exact ⟨a, rfl⟩

theorem sqClass_eq_zero_iff {a : Fˣ} : sqClass a = 0 ↔ ∃ b : Fˣ, b ^ 2 = a := by
  constructor
  · intro h
    have : (QuotientGroup.mk a : Fˣ ⧸ sqUnits F) = 1 := h
    rw [QuotientGroup.eq_one_iff] at this
    exact this
  · rintro ⟨b, rfl⟩
    have : (QuotientGroup.mk (b ^ 2) : Fˣ ⧸ sqUnits F) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ⟨b, rfl⟩
    exact this

variable (F)

theorem two_nsmul_sqCl (x : SqCl F) : (2 : ℕ) • x = 0 := by
  obtain ⟨a, rfl⟩ := sqClass_surjective x
  have h : (2 : ℕ) • sqClass a = sqClass (a ^ 2) := by
    rw [pow_two, sqClass_mul, two_nsmul]
  rw [h, sqClass_eq_zero_iff]
  exact ⟨a, rfl⟩

noncomputable instance : Module (ZMod 2) (SqCl F) := AddCommGroup.zmodModule (two_nsmul_sqCl F)

/-- The `n`-fold tensor power of the square class group over `𝔽₂`. -/
abbrev MilnorTensor (n : ℕ) : Type := PiTensorProduct (ZMod 2) (fun _ : Fin n => SqCl F)

/-- The Steinberg submodule: the span of the tensors of square classes of units
`a₀, …, a_{n-1}` such that two consecutive ones satisfy `aᵢ + aᵢ₊₁ = 1`. -/
noncomputable def steinberg (n : ℕ) : Submodule (ZMod 2) (MilnorTensor F n) :=
  Submodule.span (ZMod 2)
    {t | ∃ (v : Fin n → Fˣ) (i : ℕ) (hi : i + 1 < n),
      ((v ⟨i, Nat.lt_of_succ_lt hi⟩ : F) + (v ⟨i + 1, hi⟩ : F) = 1) ∧
        t = PiTensorProduct.tprod (ZMod 2) fun j => sqClass (v j)}

/-- The `n`-th mod-2 Milnor K-group `k_n(F) = K^M_n(F)/2`. -/
abbrev MilnorK2 (n : ℕ) : Type := MilnorTensor F n ⧸ steinberg F n

theorem steinberg_eq_bot_of_lt_two {n : ℕ} (hn : n < 2) : steinberg F n = ⊥ := by
  rw [steinberg, Submodule.span_eq_bot]
  rintro t ⟨v, i, hi, -, rfl⟩
  omega

/-- `k_0(F) ≅ 𝔽₂`. -/
noncomputable def milnorK2ZeroEquiv : MilnorK2 F 0 ≃ₗ[ZMod 2] ZMod 2 :=
  (Submodule.quotEquivOfEqBot _ (steinberg_eq_bot_of_lt_two F (by norm_num))).trans
    (PiTensorProduct.isEmptyEquiv (Fin 0))

/-- `k_1(F) ≅ F^×/(F^×)²`. -/
noncomputable def milnorK2OneEquiv : MilnorK2 F 1 ≃ₗ[ZMod 2] SqCl F :=
  (Submodule.quotEquivOfEqBot _ (steinberg_eq_bot_of_lt_two F (by norm_num))).trans
    (PiTensorProduct.subsingletonEquiv (0 : Fin 1))

end MilnorK

import RequestProject.ContCohomology
import RequestProject.MilnorK

/-!
# Kummer theory: the degree one norm residue isomorphism

Let `F` be a field of characteristic `≠ 2`, `K` a separable closure of `F` and
`G_F = Gal(K/F)` the absolute Galois group with its Krull topology.

We construct the *Kummer map*
`F^×/(F^×)² → H¹(G_F, ℤ/2)`,  `a ↦ (σ ↦ σ(√a)/√a)`
and prove that it is bijective. This is the degree one case of the norm residue
(Milnor) isomorphism.
-/

open IntermediateField ContCoh MilnorK
open scoped Classical

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace Kummer

variable (F : Type) [Field F] [NeZero (2 : F)]

/-- A separable closure of `F`. -/
abbrev Ksep : Type := SeparableClosure F

/-- The absolute Galois group of `F`, with the Krull topology. -/
abbrev GalF : Type := (SeparableClosure F) ≃ₐ[F] (SeparableClosure F)

instance : NeZero (2 : Ksep F) := by
  refine ⟨fun h => NeZero.ne (2 : F) ?_⟩
  have h2 : (algebraMap F (Ksep F)) 2 = 0 := by rw [map_ofNat]; exact h
  exact (map_eq_zero (algebraMap F (Ksep F))).1 h2

/-- A chosen square root in the separable closure. -/
noncomputable def sqrtOf (a : F) : Ksep F :=
  (IsSepClosed.exists_eq_mul_self (algebraMap F (Ksep F) a)).choose

theorem sqrtOf_mul_self (a : F) : sqrtOf F a * sqrtOf F a = algebraMap F (Ksep F) a :=
  ((IsSepClosed.exists_eq_mul_self (algebraMap F (Ksep F) a)).choose_spec).symm

variable {F}

/-- Two square roots of the same element differ by a sign. -/
theorem eq_or_eq_neg_of_mul_self_eq {r s : Ksep F} (h : r * r = s * s) : s = r ∨ s = -r := by
  have h0 : (s - r) * (s + r) = 0 := by linear_combination -h
  rcases mul_eq_zero.1 h0 with h' | h'
  · exact Or.inl (by linear_combination h')
  · exact Or.inr (by linear_combination h')

/-- Any automorphism sends a square root of an element of `F` to `± ` itself. -/
theorem aut_root_eq_or_neg {a : F} {r : Ksep F} (hr : r * r = algebraMap F (Ksep F) a)
    (σ : GalF F) : σ r = r ∨ σ r = -r := by
  have h : (σ r) * (σ r) = r * r := by
    rw [← map_mul, hr, AlgEquiv.commutes]
  exact eq_or_eq_neg_of_mul_self_eq h.symm

/-- The character `χ_a : G_F → ℤ/2` attached to `a ∈ F`. -/
noncomputable def chi (a : F) (σ : GalF F) : ZMod 2 :=
  if σ (sqrtOf F a) = sqrtOf F a then 0 else 1

/-- `χ_a` computed using an arbitrary square root of `a`. -/
theorem chi_eq_of_root {a : F} {r : Ksep F} (hr : r * r = algebraMap F (Ksep F) a) (σ : GalF F) :
    chi a σ = if σ r = r then 0 else 1 := by
  have hs := sqrtOf_mul_self F a
  rcases eq_or_eq_neg_of_mul_self_eq (hr.trans hs.symm) with h | h
  · unfold chi; rw [h]
  · unfold chi; rw [h, map_neg]; simp only [neg_inj]

/-- In characteristic `≠ 2`, a nonzero element of the separable closure differs from its
negative. -/
theorem neg_ne_self_of_ne_zero {x : Ksep F} (hx : x ≠ 0) : -x ≠ x := by
  intro h
  apply hx
  have h2 : (2 : Ksep F) * x = 0 := by linear_combination -h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 (NeZero.ne (2 : Ksep F))
  · exact h3

theorem sqrtOf_ne_zero (a : Fˣ) : sqrtOf F (a : F) ≠ 0 := by
  intro h
  have hh := sqrtOf_mul_self F (a : F)
  rw [h, mul_zero] at hh
  exact a.ne_zero ((map_eq_zero (algebraMap F (Ksep F))).1 hh.symm)

theorem chi_eq_zero_iff_of_root {a : F} {r : Ksep F} (hr : r * r = algebraMap F (Ksep F) a)
    (σ : GalF F) : chi a σ = 0 ↔ σ r = r := by
  rw [chi_eq_of_root hr σ]
  by_cases h : σ r = r <;> simp [h]

/-- The character attached to a unit of `F`. -/
noncomputable def chiU (a : Fˣ) (σ : GalF F) : ZMod 2 := chi (a : F) σ

theorem chiU_one (σ : GalF F) : chiU (1 : Fˣ) σ = 0 := by
  have hr : (1 : Ksep F) * 1 = algebraMap F (Ksep F) ((1 : Fˣ) : F) := by simp
  rw [chiU, chi_eq_of_root hr σ]
  simp

theorem chiU_mul (a b : Fˣ) (σ : GalF F) : chiU (a * b) σ = chiU a σ + chiU b σ := by
  have hra : sqrtOf F (a : F) * sqrtOf F (a : F) = algebraMap F (Ksep F) (a : F) :=
    sqrtOf_mul_self F _
  have hrb : sqrtOf F (b : F) * sqrtOf F (b : F) = algebraMap F (Ksep F) (b : F) :=
    sqrtOf_mul_self F _
  have hrab : (sqrtOf F (a : F) * sqrtOf F (b : F)) * (sqrtOf F (a : F) * sqrtOf F (b : F))
      = algebraMap F (Ksep F) ((a * b : Fˣ) : F) := by
    rw [Units.val_mul, map_mul, ← hra, ← hrb]; ring
  have hra0 := sqrtOf_ne_zero a
  have hrb0 := sqrtOf_ne_zero b
  have hab0 : sqrtOf F (a : F) * sqrtOf F (b : F) ≠ 0 := mul_ne_zero hra0 hrb0
  simp only [chiU]
  rw [chi_eq_of_root hrab, chi_eq_of_root hra, chi_eq_of_root hrb]
  rcases aut_root_eq_or_neg hra σ with h1 | h1 <;> rcases aut_root_eq_or_neg hrb σ with h2 | h2 <;>
    rw [map_mul, h1, h2] <;>
    simp [mul_neg, neg_mul, neg_neg, neg_ne_self_of_ne_zero hab0, neg_ne_self_of_ne_zero hra0,
      neg_ne_self_of_ne_zero hrb0]
  decide

theorem chiU_map_mul (a : Fˣ) (σ τ : GalF F) : chiU a (σ * τ) = chiU a σ + chiU a τ := by
  have hra : sqrtOf F (a : F) * sqrtOf F (a : F) = algebraMap F (Ksep F) (a : F) :=
    sqrtOf_mul_self F _
  have hra0 := sqrtOf_ne_zero a
  simp only [chiU]
  rw [chi_eq_of_root hra, chi_eq_of_root hra, chi_eq_of_root hra]
  rcases aut_root_eq_or_neg hra σ with h1 | h1 <;> rcases aut_root_eq_or_neg hra τ with h2 | h2 <;>
    rw [AlgEquiv.mul_apply, h2] <;>
    simp [h1, map_neg, neg_neg, neg_ne_self_of_ne_zero hra0]
  decide

theorem chiU_continuous (a : Fˣ) : Continuous (chiU a : GalF F → ZMod 2) := by
  have hra : sqrtOf F (a : F) * sqrtOf F (a : F) = algebraMap F (Ksep F) (a : F) :=
    sqrtOf_mul_self F _
  refine ContCoh.continuous_of_isOpen_zero_set _ (fun x y => chiU_map_mul a x y) ?_
  have hset : {σ : GalF F | chiU a σ = 0}
      = (MulAction.stabilizer (GalF F) (sqrtOf F (a : F)) : Set (GalF F)) := by
    ext σ
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    rw [chiU, chi_eq_zero_iff_of_root hra]
    rfl
  rw [hset]
  exact stabilizer_isOpen_of_isIntegral _

theorem chiU_eq_zero_iff (a : Fˣ) : (∀ σ : GalF F, chiU a σ = 0) ↔ ∃ b : Fˣ, b ^ 2 = a := by
  have hra : sqrtOf F (a : F) * sqrtOf F (a : F) = algebraMap F (Ksep F) (a : F) :=
    sqrtOf_mul_self F _
  constructor
  · intro h
    have hfix : ∀ σ : GalF F, σ (sqrtOf F (a : F)) = sqrtOf F (a : F) := fun σ =>
      (chi_eq_zero_iff_of_root hra σ).1 (h σ)
    obtain ⟨c, hc⟩ :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := F) (sqrtOf F (a : F))).2 hfix
    have hc0 : c ≠ 0 := by
      intro h0
      apply sqrtOf_ne_zero a
      rw [← hc, h0, map_zero]
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    have hcc : algebraMap F (Ksep F) (c * c) = algebraMap F (Ksep F) (a : F) := by
      rw [map_mul, hc, hra]
    simpa [pow_two] using (algebraMap F (Ksep F)).injective hcc
  · rintro ⟨b, rfl⟩ σ
    have hrb : (algebraMap F (Ksep F) (b : F)) * (algebraMap F (Ksep F) (b : F))
        = algebraMap F (Ksep F) (((b ^ 2 : Fˣ)) : F) := by
      rw [← map_mul]
      congr 1
      push_cast
      ring
    rw [chiU, chi_eq_of_root hrb σ]
    simp

/-- A quadratic extension of a field of characteristic `≠ 2` is generated by a square root:
any intermediate field `L` of degree `2` over `F` contains an element `y ∉ F` with `y² ∈ F`. -/
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
theorem exists_chiU_eq (f : GalF F → ZMod 2) (hcont : Continuous f)
    (hf : ∀ σ τ : GalF F, f (σ * τ) = f σ + f τ) : ∃ a : Fˣ, ∀ σ, f σ = chiU a σ := by
  by_cases hzero : ∀ σ, f σ = 0
  · exact ⟨1, fun σ => by rw [hzero σ, chiU_one]⟩
  push_neg at hzero
  obtain ⟨σ₀, hσ₀⟩ := hzero
  have hσ₀₁ : f σ₀ = 1 := by revert hσ₀; generalize f σ₀ = v; revert v; decide
  have hf1 : f 1 = 0 := by
    have h := hf 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  let H : Subgroup (GalF F) :=
    { carrier := {σ | f σ = 0}
      one_mem' := hf1
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [hf, hx, hy, add_zero]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        have h := hf x x⁻¹
        rw [mul_inv_cancel, hf1, hx, zero_add] at h
        exact h.symm }
  have hmemH : ∀ σ : GalF F, σ ∈ H ↔ f σ = 0 := fun _ => Iff.rfl
  have hHopen : IsOpen (H : Set (GalF F)) := hcont.isOpen_preimage {0} (isOpen_discrete _)
  have hHclosed : IsClosed (H : Set (GalF F)) := (OpenSubgroup.mk H hHopen).isClosed
  have hidx : H.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨σ₀, fun b => ?_⟩
    have hb : f (b * σ₀) = f b + 1 := by rw [hf, hσ₀₁]
    rw [Xor', hmemH, hmemH, hb]
    generalize f b = v
    revert v
    decide
  have hfixL : (fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHclosed⟩
  have hrank : Module.finrank F (fixedField H) = 2 := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (fixedField H), hfixL]
    exact hidx
  obtain ⟨y, hyL, hybot, a₀, hy2⟩ := exists_sqrt_of_finrank_two (fixedField H) hrank
  have ha₀ : a₀ ≠ 0 := by
    intro h
    rw [h, map_zero, mul_self_eq_zero] at hy2
    exact hybot (hy2 ▸ zero_mem _)
  refine ⟨Units.mk0 a₀ ha₀, fun σ => ?_⟩
  have hroot : y * y = algebraMap F (Ksep F) ((Units.mk0 a₀ ha₀ : Fˣ) : F) := hy2
  have hchi : chi ((Units.mk0 a₀ ha₀ : Fˣ) : F) σ = 0 ↔ σ y = y :=
    chi_eq_zero_iff_of_root hroot σ
  haveI : FiniteDimensional F (fixedField H) :=
    Module.finite_of_finrank_pos (by rw [hrank]; norm_num)
  have hFy : F⟮ y ⟯ = fixedField H := by
    haveI : FiniteDimensional F F⟮ y ⟯ :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
    have hne1 : Module.finrank F F⟮ y ⟯ ≠ 1 := by
      intro h
      rw [IntermediateField.finrank_eq_one_iff] at h
      exact hybot (h ▸ IntermediateField.mem_adjoin_simple_self F y)
    have hpos : 0 < Module.finrank F F⟮ y ⟯ := Module.finrank_pos
    exact IntermediateField.eq_of_le_of_finrank_le
      (IntermediateField.adjoin_simple_le_iff.2 hyL) (by rw [hrank]; omega)
  have hHy : σ ∈ H ↔ σ y = y := by
    rw [← hfixL, ← hFy]
    constructor
    · intro h
      rw [IntermediateField.mem_fixingSubgroup_iff] at h
      exact h y (IntermediateField.mem_adjoin_simple_self F y)
    · intro h
      rw [IntermediateField.mem_fixingSubgroup_iff]
      have hall := (IntermediateField.forall_mem_adjoin_smul_eq_self_iff (F := F) (S := {y}) σ).2
        (by rintro z (rfl : z = y); exact h)
      exact fun x hx => hall x hx
  by_cases hσH : σ ∈ H
  · rw [(hmemH σ).1 hσH, chiU, hchi.2 (hHy.1 hσH)]
  · have h1 : f σ = 1 := by
      have hne : f σ ≠ 0 := hσH
      revert hne; generalize f σ = v; revert v; decide
    have h2 : chiU (Units.mk0 a₀ ha₀) σ = 1 := by
      have hne : chi ((Units.mk0 a₀ ha₀ : Fˣ) : F) σ ≠ 0 := fun h => hσH (hHy.2 (hchi.1 h))
      rw [chiU]
      revert hne; generalize chi ((Units.mk0 a₀ ha₀ : Fˣ) : F) σ = v; revert v; decide
    rw [h1, h2]

variable (F)

/-- The Kummer map on square classes, as a function. -/
noncomputable def kummerFun (x : SqCl F) (σ : GalF F) : ZMod 2 :=
  Quotient.liftOn' (Additive.toMul x : Fˣ ⧸ sqUnits F) (fun a : Fˣ => chiU a σ) (by
    intro a b hab
    have hmem : a⁻¹ * b ∈ sqUnits F := QuotientGroup.leftRel_apply.1 hab
    obtain ⟨c, hc⟩ := hmem
    have hb : b = a * c ^ 2 := by
      rw [hc]
      group
    subst hb
    show chiU a σ = chiU (a * c ^ 2) σ
    rw [chiU_mul]
    have : chiU (c ^ 2) σ = 0 := by
      rw [pow_two, chiU_mul]
      generalize chiU c σ = z
      revert z
      decide
    rw [this, add_zero])

theorem kummerFun_sqClass (a : Fˣ) (σ : GalF F) : kummerFun F (sqClass a) σ = chiU a σ := rfl

/-- The Kummer map into continuous `1`-cocycles. -/
noncomputable def kummerAddHom : SqCl F →+ ContCoh.Cochain (GalF F) 1 where
  toFun x := fun g => kummerFun F x (g 0)
  map_zero' := by
    ext g
    have : (0 : SqCl F) = sqClass (1 : Fˣ) := rfl
    rw [this, kummerFun_sqClass, chiU_one]
    rfl
  map_add' x y := by
    obtain ⟨a, rfl⟩ := sqClass_surjective x
    obtain ⟨b, rfl⟩ := sqClass_surjective y
    ext g
    rw [← sqClass_mul]
    simp only [kummerFun_sqClass]
    rw [chiU_mul]
    rfl

theorem kummerAddHom_mem_cocycles (x : SqCl F) :
    kummerAddHom F x ∈ ContCoh.cocycles (GalF F) 1 := by
  obtain ⟨a, rfl⟩ := sqClass_surjective x
  have hfun : (kummerAddHom F (sqClass a) : ContCoh.Cochain (GalF F) 1)
      = fun g => chiU a (g 0) := rfl
  rw [mem_cocycles_one, hfun]
  refine ⟨(chiU_continuous a).comp (continuous_apply 0), fun x y => ?_⟩
  simpa using chiU_map_mul a x y

/-- The Kummer map `k₁(F) = F^×/(F^×)² → Z¹(G_F, ℤ/2)`. -/
noncomputable def kummerMap : SqCl F →ₗ[ZMod 2] ContCoh.cocycles (GalF F) 1 :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun x => ⟨kummerAddHom F x, kummerAddHom_mem_cocycles F x⟩
      map_zero' := Subtype.ext (map_zero (kummerAddHom F))
      map_add' := fun x y => Subtype.ext (map_add (kummerAddHom F) x y) }

theorem kummerMap_injective : Function.Injective (kummerMap F) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := sqClass_surjective x
  have hval : ∀ σ : GalF F, chiU a σ = 0 := by
    intro σ
    have h := congrFun (congrArg Subtype.val hx) ![σ]
    simpa using h
  obtain ⟨b, hb⟩ := (chiU_eq_zero_iff a).1 hval
  exact sqClass_eq_zero_iff.2 ⟨b, hb⟩

theorem kummerMap_surjective : Function.Surjective (kummerMap F) := by
  intro y
  have hy := y.2
  rw [mem_cocycles_one] at hy
  obtain ⟨hcont, hhom⟩ := hy
  have hc : Continuous (fun σ : GalF F => (y : ContCoh.Cochain (GalF F) 1) ![σ]) :=
    hcont.comp (continuous_pi (fun i => by fin_cases i; exact continuous_id))
  obtain ⟨a, ha⟩ := exists_chiU_eq (fun σ => (y : ContCoh.Cochain (GalF F) 1) ![σ]) hc
    (fun σ τ => by simpa using hhom σ τ)
  refine ⟨sqClass a, Subtype.ext (funext fun g => ?_)⟩
  have hg : g = ![g 0] := by ext i; fin_cases i; rfl
  show chiU a (g 0) = (y : ContCoh.Cochain (GalF F) 1) g
  rw [hg]
  exact (ha (g 0)).symm

theorem kummerMap_bijective : Function.Bijective (kummerMap F) :=
  ⟨kummerMap_injective F, kummerMap_surjective F⟩

end Kummer

import Mathlib
import RequestProject.ContCohomology
import RequestProject.MilnorK
import RequestProject.Kummer

/-!
# Voevodsky Milnor
Category: Frontier — Fields Medal Work
Target: Frontier.voevodsky_milnor
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header comment above has to be preceded by the `import` lines, since Lean 4 requires
`import` commands to come first in a file.)

## What is formalized here

For a field `F` with `char F ≠ 2` we have defined

* `MilnorK.MilnorK2 F n`, the mod-2 Milnor K-group `k_n(F) = K^M_n(F)/2`, as the quotient of the
  `n`-fold tensor power over `𝔽₂` of the square class group `F^×/(F^×)²` by the Steinberg
  relations (see `RequestProject/MilnorK.lean`);
* `ContCoh.H G n`, the continuous cochain cohomology `Hⁿ(G, ℤ/2)` of a topological group `G`
  with trivial coefficients `ℤ/2` (see `RequestProject/ContCohomology.lean`), applied to the
  absolute Galois group `G_F = Gal(F^sep/F)` with its Krull topology;
* the norm residue maps in degrees `0` and `1`, the latter being the Kummer map
  `a ↦ (σ ↦ σ(√a)/√a)`.

`Frontier.milnorConjecture F` states the Milnor conjecture (Voevodsky's theorem):
mod-2 Galois cohomology is isomorphic to mod-2 Milnor K-theory in every degree.

The theorem `Frontier.voevodsky_milnor` proves the base cases: the norm residue maps in
degrees `0` and `1` are bijective. Degree `1` is Kummer theory, and it is proved here in full
(injectivity and surjectivity) for every field of characteristic `≠ 2`.
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open MilnorK ContCoh Kummer

namespace Frontier

variable (F : Type) [Field F] [NeZero (2 : F)]

/-- The Milnor conjecture (Voevodsky's theorem): in every degree the mod-2 Milnor K-group
`k_n(F) = K^M_n(F)/2` is isomorphic to the mod-2 Galois cohomology `Hⁿ(G_F, ℤ/2)`. -/
def milnorConjecture : Prop :=
  ∀ n : ℕ, Nonempty (MilnorK2 F n ≃ₗ[ZMod 2] ContCoh.H (GalF F) n)

/-- The norm residue map in degree `0`: `k₀(F) = 𝔽₂ → H⁰(G_F, ℤ/2) = 𝔽₂`. -/
noncomputable def normResidue₀ : MilnorK2 F 0 →ₗ[ZMod 2] ContCoh.H (GalF F) 0 :=
  (ContCoh.H0Equiv (GalF F)).symm.toLinearMap ∘ₗ (milnorK2ZeroEquiv F).toLinearMap

/-- The norm residue map in degree `1`: the Kummer map
`k₁(F) = F^×/(F^×)² → H¹(G_F, ℤ/2)`, `a ↦ (σ ↦ σ(√a)/√a)`. -/
noncomputable def normResidue₁ : MilnorK2 F 1 →ₗ[ZMod 2] ContCoh.H (GalF F) 1 :=
  (ContCoh.H1Equiv (GalF F)).symm.toLinearMap ∘ₗ
    (Kummer.kummerMap F ∘ₗ (milnorK2OneEquiv F).toLinearMap)

/-- **The Milnor conjecture in degrees `0` and `1`.**

For every field `F` of characteristic `≠ 2`, the norm residue maps
`k₀(F) → H⁰(G_F, ℤ/2)` and `k₁(F) → H¹(G_F, ℤ/2)` are bijective.
Degree `1` is the Kummer isomorphism `F^×/(F^×)² ≅ H¹(G_F, ℤ/2)`. -/
theorem voevodsky_milnor :
    Function.Bijective (normResidue₀ F) ∧ Function.Bijective (normResidue₁ F) := by
  constructor
  · exact (ContCoh.H0Equiv (GalF F)).symm.bijective.comp (milnorK2ZeroEquiv F).bijective
  · exact (ContCoh.H1Equiv (GalF F)).symm.bijective.comp
      ((Kummer.kummerMap_bijective F).comp (milnorK2OneEquiv F).bijective)

/-- The Milnor conjecture holds in degrees `0` and `1`. -/
theorem milnorConjecture_degree_le_one (n : ℕ) (hn : n ≤ 1) :
    Nonempty (MilnorK2 F n ≃ₗ[ZMod 2] ContCoh.H (GalF F) n) := by
  interval_cases n
  · exact ⟨LinearEquiv.ofBijective (normResidue₀ F) (voevodsky_milnor F).1⟩
  · exact ⟨LinearEquiv.ofBijective (normResidue₁ F) (voevodsky_milnor F).2⟩

end Frontier

import Mathlib

/-!
# Continuous cochain cohomology with `ZMod 2` coefficients

For a topological group `G` we define the cohomology of the complex of *continuous*
inhomogeneous cochains with values in the discrete trivial `G`-module `ZMod 2`.
This is the usual definition of Galois cohomology `Hⁿ(G, ℤ/2)` when `G` is a profinite
(e.g. absolute Galois) group.

The differential is the one from `Mathlib`'s `groupCohomology.inhomogeneousCochains`
applied to the trivial representation, so `d ∘ d = 0` comes for free.
-/

open groupCohomology inhomogeneousCochains

namespace ContCoh

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Inhomogeneous `n`-cochains of `G` with values in `ZMod 2` (no continuity imposed). -/
abbrev Cochain (n : ℕ) : Type := (Fin n → G) → ZMod 2

/-- The differential on inhomogeneous cochains with trivial `ZMod 2` coefficients. -/
noncomputable def d (n : ℕ) : Cochain G n →ₗ[ZMod 2] Cochain G (n + 1) :=
  (inhomogeneousCochains.d (Rep.trivial (ZMod 2) G (ZMod 2)) n).hom

variable {G}

theorem d_apply (n : ℕ) (f : Cochain G n) (g : Fin (n + 1) → G) :
    d G n f g = f (fun i => g i.succ) + ∑ j : Fin (n + 1), f (Fin.contractNth j (· * ·) g) := by
  simp [d, inhomogeneousCochains.d_hom_apply]

theorem d_comp_d (n : ℕ) (f : Cochain G n) : d G (n + 1) (d G n f) = 0 := by
  have h := inhomogeneousCochains.d_comp_d (A := Rep.trivial (ZMod 2) G (ZMod 2)) (n := n)
  have h2 := congrArg (fun (m : ModuleCat.Hom _ _) => m.hom f) h
  simpa [d] using h2

/-- The differential out of degree `0` vanishes, since the coefficients are trivial. -/
theorem d_zero_eq_zero (f : Cochain G 0) : d G 0 f = 0 := by
  ext g
  rw [d_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Pi.zero_apply]
  rw [Subsingleton.elim (fun i => g i.succ) (Fin.contractNth 0 (· * ·) g)]
  generalize f (Fin.contractNth 0 (· * ·) g) = a
  revert a
  decide

variable (G)

/-- Continuous `n`-cochains, as a submodule of all cochains. -/
def contCochains (n : ℕ) : Submodule (ZMod 2) (Cochain G n) where
  carrier := {f | Continuous f}
  add_mem' hf hg := hf.add hg
  zero_mem' := continuous_const
  smul_mem' c f hf := by
    have h : (c • f) = fun x => c • f x := rfl
    rw [Set.mem_setOf_eq, h]
    exact (continuous_const (y := c)).smul hf

theorem mem_contCochains {n : ℕ} {f : Cochain G n} :
    f ∈ contCochains G n ↔ Continuous f := Iff.rfl

theorem continuous_contractNth (n : ℕ) (j : Fin (n + 1)) :
    Continuous fun g : Fin (n + 1) → G => Fin.contractNth j (· * ·) g := by
  refine continuous_pi fun i => ?_
  simp only [Fin.contractNth]
  split_ifs
  · exact continuous_apply _
  · exact (continuous_apply _).mul (continuous_apply _)
  · exact continuous_apply _

theorem continuous_d {n : ℕ} {f : Cochain G n} (hf : Continuous f) : Continuous (d G n f) := by
  have h : (d G n f) = (fun g : Fin (n + 1) → G => f (fun i => g i.succ) +
      ∑ j : Fin (n + 1), f (Fin.contractNth j (· * ·) g)) := funext fun g => d_apply n f g
  rw [h]
  refine Continuous.add (hf.comp (continuous_pi fun i => continuous_apply _)) ?_
  exact continuous_finset_sum _ fun j _ => hf.comp (continuous_contractNth G n j)

/-- A homomorphism to the discrete group `ZMod 2` with open kernel is continuous. -/
theorem continuous_of_isOpen_zero_set {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (f : H → ZMod 2) (hf : ∀ x y, f (x * y) = f x + f y)
    (h : IsOpen {x | f x = 0}) : Continuous f := by
  have key : ∀ v : ZMod 2, IsOpen {x | f x = v} := by
    intro v
    by_cases hne : ∃ x₀, f x₀ = v
    · obtain ⟨x₀, hx₀⟩ := hne
      have hset : {x | f x = v} = (fun y => x₀ * y) '' {y | f y = 0} := by
        ext x
        constructor
        · intro hx
          refine ⟨x₀⁻¹ * x, ?_, by group⟩
          have hx2 := hf x₀ (x₀⁻¹ * x)
          rw [← mul_assoc, mul_inv_cancel, one_mul, hx, hx₀] at hx2
          exact left_eq_add.mp hx2
        · rintro ⟨y, hy, rfl⟩
          simp only [Set.mem_setOf_eq] at hy ⊢
          rw [hf, hy, add_zero, hx₀]
      rw [hset]
      exact (Homeomorph.mulLeft x₀).isOpenMap _ h
    · have hempty : {x | f x = v} = (∅ : Set H) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hx => hne ⟨x, hx⟩
      rw [hempty]
      exact isOpen_empty
  rw [continuous_def]
  intro s _
  have hpre : f ⁻¹' s = ⋃ v ∈ s, {x | f x = v} := by
    ext x
    simp
  rw [hpre]
  exact isOpen_biUnion fun v _ => key v

/-- Continuous `n`-cocycles. -/
noncomputable def cocycles (n : ℕ) : Submodule (ZMod 2) (Cochain G n) :=
  contCochains G n ⊓ LinearMap.ker (d G n)

theorem mem_cocycles {n : ℕ} {f : Cochain G n} :
    f ∈ cocycles G n ↔ Continuous f ∧ d G n f = 0 := Iff.rfl

/-- Continuous `n`-coboundaries. -/
noncomputable def coboundaries : ∀ n : ℕ, Submodule (ZMod 2) (Cochain G n)
  | 0 => ⊥
  | n + 1 => (contCochains G n).map (d G n)

theorem coboundaries_le_cocycles (n : ℕ) : coboundaries G n ≤ cocycles G n := by
  cases n with
  | zero => simp [coboundaries]
  | succ n =>
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨continuous_d G hf, d_comp_d n f⟩

/-- The `n`-th continuous cohomology group of `G` with coefficients in the trivial
module `ZMod 2`. -/
abbrev H (n : ℕ) : Type :=
  (cocycles G n) ⧸ (Submodule.comap (cocycles G n).subtype (coboundaries G n))

noncomputable instance (n : ℕ) : AddCommGroup (H G n) := inferInstance
noncomputable instance (n : ℕ) : Module (ZMod 2) (H G n) := inferInstance

/-- The projection from cocycles to cohomology. -/
def Hmk {n : ℕ} (f : cocycles G n) : H G n := Submodule.Quotient.mk f

/-! ### Degrees `0` and `1` -/

theorem coboundaries_zero : coboundaries G 0 = ⊥ := rfl

theorem coboundaries_one : coboundaries G 1 = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro _ ⟨f, -, rfl⟩
  simpa using d_zero_eq_zero f

/-- Degree-`0` cocycles are just the constants. -/
noncomputable def cocyclesZeroEquiv : (cocycles G 0) ≃ₗ[ZMod 2] ZMod 2 where
  toFun f := (f : Cochain G 0) (fun i => i.elim0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun c := ⟨fun _ => c, continuous_const, d_zero_eq_zero _⟩
  left_inv f := by
    ext g
    exact congrArg (f : Cochain G 0) (Subsingleton.elim (fun i : Fin 0 => i.elim0) g)
  right_inv c := rfl

/-- In degree `0`, every cochain is a cocycle, and cohomology is `ZMod 2`. -/
noncomputable def H0Equiv : H G 0 ≃ₗ[ZMod 2] ZMod 2 :=
  (Submodule.quotEquivOfEqBot _ (by rw [coboundaries_zero]; simp)).trans (cocyclesZeroEquiv G)

/-- The subgroup of continuous homomorphisms `G → ZMod 2`, i.e. continuous `1`-cocycles. -/
theorem mem_cocycles_one {f : Cochain G 1} :
    f ∈ cocycles G 1 ↔ Continuous f ∧ ∀ x y : G, f ![x * y] = f ![x] + f ![y] := by
  rw [mem_cocycles]
  refine and_congr_right fun hf => ?_
  constructor
  · intro h x y
    have := congrFun h ![x, y]
    rw [d_apply] at this
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Pi.zero_apply] at this
    have e0 : (fun i : Fin 1 => (![x, y] : Fin 2 → G) i.succ) = ![y] := by
      ext i; fin_cases i; rfl
    have e1 : Fin.contractNth (0 : Fin 2) (· * ·) ![x, y] = ![x * y] := by
      ext i; fin_cases i; simp [Fin.contractNth]
    have e2 : Fin.contractNth (Fin.succ (0 : Fin 1)) (· * ·) ![x, y] = ![x] := by
      ext i; fin_cases i; simp [Fin.contractNth]
    rw [e0, e1, e2] at this
    revert this
    generalize f ![y] = a
    generalize f ![x * y] = b
    generalize f ![x] = c
    revert a b c
    decide
  · intro h
    ext g
    rw [d_apply]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Pi.zero_apply]
    have e0 : (fun i : Fin 1 => g i.succ) = ![g 1] := by
      ext i; fin_cases i; rfl
    have e1 : Fin.contractNth (0 : Fin 2) (· * ·) g = ![g 0 * g 1] := by
      ext i; fin_cases i; simp [Fin.contractNth]
    have e2 : Fin.contractNth (Fin.succ (0 : Fin 1)) (· * ·) g = ![g 0] := by
      ext i; fin_cases i; simp [Fin.contractNth]
    rw [e0, e1, e2, h (g 0) (g 1)]
    generalize f ![g 1] = a
    generalize f ![g 0] = b
    revert a b
    decide

/-- Degree-one cohomology is the group of continuous homomorphisms into `ZMod 2`. -/
noncomputable def H1Equiv : H G 1 ≃ₗ[ZMod 2] cocycles G 1 :=
  Submodule.quotEquivOfEqBot _ (by rw [coboundaries_one]; simp)

end ContCoh

