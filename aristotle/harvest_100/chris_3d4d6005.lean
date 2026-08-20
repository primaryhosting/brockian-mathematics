/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring; the required header is
-- reproduced verbatim as the module docstring immediately below the import.)

import RequestProject.Math2.Canonical

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Statement

For a smooth projective curve, described here through its function field `F / K` with its
family of places `P` (see `Math2.PreCurve` and `Math2.PreCurve.IsCurve`), there exists a
*canonical divisor* `W` such that for every divisor `D`

  `ℓ(D) - ℓ(W - D) = deg D + 1 - g`,

where `ℓ(D) = dim_K L(D)` is the dimension of the Riemann-Roch space of `D`, `deg D` is the
degree of `D` and `g` is the genus of the curve.  The canonical divisor moreover satisfies
`ℓ(W) = g` and `deg W = 2g - 2`.
-/

namespace Math2

open PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]

/-- **Riemann-Roch for a smooth projective curve.**

There is a canonical divisor `W` (of degree `2g - 2` and with `ℓ(W) = g`) such that for every
divisor `D` on the curve,
`ℓ(D) - ℓ(W - D) = deg D + 1 - g`. -/
theorem riemann_roch_curve (C : PreCurve K F P) (hC : C.IsCurve) :
    ∃ W : P →₀ ℤ, C.ell W = C.genus ∧ C.degD W = 2 * C.genus - 2 ∧
      ∀ D : P →₀ ℤ, (C.ell D : ℤ) - (C.ell (W - D) : ℤ) = C.degD D + 1 - C.genus := by
  obtain ⟨W, hW⟩ := hC.riemann_roch
  have h0 := hW 0
  rw [sub_zero, C.degD_zero, C.ell_zero] at h0
  have hellW : C.ell W = C.genus := by
    push_cast at h0
    omega
  have hWW := hW W
  rw [sub_self, C.ell_zero, hellW] at hWW
  refine ⟨W, hellW, ?_, hW⟩
  push_cast at hWW
  linarith

end Math2

#print axioms Math2.riemann_roch_curve

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

/-
Duality: the module of Weil differentials is one dimensional over `F`.
-/
import RequestProject.Math2.Differentials

namespace Math2

open Module Submodule

namespace PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]
variable {C : PreCurve K F P}

/-! ### Dimension of the spaces of differentials -/

lemma IsCurve.finiteDimensional_OmegaSub (hC : C.IsCurve) (A : P →₀ ℤ) :
    FiniteDimensional K (C.OmegaSub A) := by
  haveI := hC.H1_finite A
  exact Module.Finite.equiv (Submodule.dualQuotEquivDualAnnihilator (C.AD A ⊔ C.FSub))

lemma IsCurve.finrank_OmegaSub (hC : C.IsCurve) (A : P →₀ ℤ) :
    finrank K (C.OmegaSub A) = C.iH A := by
  haveI := hC.H1_finite A
  rw [OmegaSub, ← (Submodule.dualQuotEquivDualAnnihilator (C.AD A ⊔ C.FSub)).finrank_eq]
  exact Subspace.dual_finrank_eq

/-! ### Multiplying differentials by functions -/

lemma mulAdele_mem_AD {x : F} (hx : x ≠ 0) {B : P →₀ ℤ} {α : C.Adele} (hα : α ∈ C.AD B) :
    C.mulAdele x α ∈ C.AD (B - C.divisorOf x) := by
  intro p
  have h := hα p
  have h2 := C.ord_mul_ge p x (α.val p) hx (-(B p)) h
  have h3 : (C.mulAdele x α).val p = x * α.val p := rfl
  rw [h3]
  refine le_trans (le_of_eq ?_) h2
  have hval : -((B - C.divisorOf x) p) = -B p + C.ordZ p x := by
    simp only [Finsupp.coe_sub, Pi.sub_apply, C.divisorOf_apply hx p]
    ring
  rw [hval]

lemma mem_OmegaSub_smulDual {x : F} (hx : x ≠ 0) {A : P →₀ ℤ} {ω : Module.Dual K C.Adele}
    (hω : ω ∈ C.OmegaSub A) : C.smulDual x ω ∈ C.OmegaSub (A + C.divisorOf x) := by
  rw [mem_OmegaSub_iff]
  intro α hα
  rw [smulDual_apply]
  rw [mem_OmegaSub_iff] at hω
  refine hω _ ?_
  have hsub : C.AD (A + C.divisorOf x) ⊔ C.FSub ≤
      Submodule.comap (C.mulAdele x) (C.AD A ⊔ C.FSub) := by
    refine sup_le ?_ ?_
    · intro β hβ
      have h := mulAdele_mem_AD hx hβ
      have heq : A + C.divisorOf x - C.divisorOf x = A := by abel
      rw [heq] at h
      exact Submodule.mem_sup_left h
    · rintro β ⟨y, rfl⟩
      refine Submodule.mem_sup_right ?_
      rw [C.mulAdele_diagLin]
      exact ⟨x * y, rfl⟩
  exact hsub hα

/-- Multiplication of a fixed differential by functions, as a linear map. -/
def toDualLin (C : PreCurve K F P) (ω : Module.Dual K C.Adele) :
    F →ₗ[K] Module.Dual K C.Adele where
  toFun x := C.smulDual x ω
  map_add' := by
    intro x y
    ext α
    have h : C.mulAdele (x + y) α = C.mulAdele x α + C.mulAdele y α := by
      apply Adele.val_injective
      funext p
      simp [add_mul]
    simp [smulDual_apply, h]
  map_smul' := by
    intro c x
    ext α
    have h : C.mulAdele (c • x) α = c • C.mulAdele x α := by
      apply Adele.val_injective
      funext p
      simp only [Adele.val_mk, Adele.val_smul, Pi.smul_apply, Algebra.smul_def, mulAdele_val]
      ring
    simp [smulDual_apply, h]

@[simp] lemma toDualLin_apply (ω : Module.Dual K C.Adele) (x : F) :
    C.toDualLin ω x = C.smulDual x ω := rfl

/-- If `ω` vanishes on `A(A) + F` and `x ∈ L(B + A)`, then `xω` vanishes on `A(-B) + F`. -/
lemma smulDual_mem_OmegaSub_neg {A B : P →₀ ℤ} {ω : Module.Dual K C.Adele}
    (hω : ω ∈ C.OmegaSub A) {x : F} (hx : x ∈ C.LSpace (B + A)) :
    C.smulDual x ω ∈ C.OmegaSub (-B) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · have : C.smulDual (0 : F) ω = 0 := by
      ext α
      have h : C.mulAdele (0 : F) α = 0 := by
        apply Adele.val_injective
        funext p
        simp
      simp [smulDual_apply, h]
    rw [this]
    exact Submodule.zero_mem _
  · have hmem := mem_OmegaSub_smulDual hx0 hω
    refine C.OmegaSub_antitone ?_ hmem
    intro p
    have h := hx p
    rw [C.ord_eq_ordZ hx0] at h
    have h2 : -((B + A) p) ≤ C.ordZ p x := by exact_mod_cast h
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_neg, Pi.neg_apply,
      C.divisorOf_apply hx0 p]
    simp only [Finsupp.coe_add, Pi.add_apply] at h2
    omega

/-- The fundamental inequality `ell (B + A) ≤ i(-B)` for a nonzero differential in `Ω(A)`. -/
lemma IsCurve.ell_le_iH_neg (hC : C.IsCurve) {A : P →₀ ℤ} {ω : Module.Dual K C.Adele}
    (hω : ω ∈ C.OmegaSub A) (hω0 : ω ≠ 0) (B : P →₀ ℤ) :
    C.ell (B + A) ≤ C.iH (-B) := by
  haveI := hC.finiteDimensional_OmegaSub (-B)
  haveI := hC.finiteDimensional_LSpace (B + A)
  set f : ↥(C.LSpace (B + A)) →ₗ[K] ↥(C.OmegaSub (-B)) :=
    LinearMap.codRestrict (C.OmegaSub (-B))
      ((C.toDualLin ω).comp (C.LSpace (B + A)).subtype)
      (fun x => smulDual_mem_OmegaSub_neg hω x.2) with hf
  have hinj : Function.Injective f := by
    intro x y hxy
    have h : C.smulDual ((x : F) - y) ω = 0 := by
      have h1 : C.smulDual (x : F) ω = C.smulDual (y : F) ω := by
        have := congrArg (Subtype.val) hxy
        simpa [hf] using this
      have h2 : C.toDualLin ω ((x : F) - (y : F)) = 0 := by
        rw [map_sub, toDualLin_apply, toDualLin_apply, h1, sub_self]
      simpa using h2
    by_contra hne
    have hxy0 : (x : F) - y ≠ 0 := by
      intro h0
      exact hne (Subtype.ext (by linear_combination (norm := skip) h0; ring))
    exact hω0 ((C.smulDual_eq_zero_iff hxy0 ω).1 h)
  have := LinearMap.finrank_le_finrank_of_injective (f := f) hinj
  rw [hC.finrank_OmegaSub (-B)] at this
  exact this

end PreCurve

end Math2

/-
Finite dimensionality of Riemann-Roch spaces and the function `ell`.
-/
import RequestProject.Math2.Local

namespace Math2

open Module Submodule

namespace PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]
variable (C : PreCurve K F P)

/-- The residue map on a Riemann-Roch space at a place. -/
noncomputable def resL (E : P →₀ ℤ) (p : P) : ↥(C.LSpace E) →ₗ[K] C.resField p :=
  C.resMap p (E p) (C.LSpace E).subtype (fun v => v.2 p)

lemma LSpace_sub_single_le (E : P →₀ ℤ) (p : P) :
    C.LSpace (E - Finsupp.single p 1) ≤ C.LSpace E := by
  refine C.LSpace_mono ?_
  intro q
  simp only [Finsupp.coe_sub, Pi.sub_apply]
  rcases eq_or_ne q p with rfl | hq
  · simp
  · simp [Finsupp.single_apply, hq]

lemma ker_resL (E : P →₀ ℤ) (p : P) :
    LinearMap.ker (C.resL E p) = (C.LSpace (E - Finsupp.single p 1)).comap
      (C.LSpace E).subtype := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
  rw [resL, C.resMap_eq_zero_iff]
  constructor
  · intro h q
    rcases eq_or_ne q p with rfl | hq
    · simpa using h
    · have := x.2 q
      simpa [Finsupp.single_apply, hq] using this
  · intro h
    have := h p
    simpa using this

/-- `ell D` is the dimension of the Riemann-Roch space `L(D)`. -/
noncomputable def ell (D : P →₀ ℤ) : ℕ := finrank K (C.LSpace D)

lemma ell_eq_zero_of_degD_neg (D : P →₀ ℤ) (hD : C.degD D < 0) : C.ell D = 0 := by
  rw [ell, C.LSpace_eq_bot_of_degD_neg hD]
  simp

/-- The Riemann-Roch space of the zero divisor is one dimensional (the constants). -/
lemma ell_zero : C.ell 0 = 1 := by
  rw [ell, C.LSpace_zero]
  have hiso : LinearMap.range (Algebra.linearMap K F) ≃ₗ[K] K :=
    (LinearEquiv.ofInjective (Algebra.linearMap K F)
      (by exact (algebraMap K F).injective)).symm
  rw [hiso.finrank_eq]
  simp

end PreCurve

namespace PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]
variable {C : PreCurve K F P}

lemma IsCurve.deg_pos (hC : C.IsCurve) (p : P) : 0 < C.deg p := by
  haveI := hC.residue_finite p
  have hlt : C.maxIdeal p ≠ ⊤ := by
    intro h
    have h1 : (⟨1, by show ((0 : ℤ) : Zt) ≤ C.ord p 1; simp⟩ : ↥(C.valSub p 0)) ∈
        C.maxIdeal p := by rw [h]; trivial
    have h2 : ((1 : ℤ) : Zt) ≤ C.ord p (1 : F) := h1
    rw [C.ord_one] at h2
    exact absurd h2 (by norm_num)
  haveI : Nontrivial (C.resField p) := Submodule.Quotient.nontrivial_iff.2 hlt
  rw [← hC.residue_finrank p]
  exact Module.finrank_pos

lemma IsCurve.finiteDimensional_LSpace_step (hC : C.IsCurve) (E : P →₀ ℤ) (p : P)
    (h : FiniteDimensional K (C.LSpace (E - Finsupp.single p 1))) :
    FiniteDimensional K (C.LSpace E) := by
  haveI := hC.residue_finite p
  haveI hk : FiniteDimensional K ↥(LinearMap.ker (C.resL E p)) := by
    rw [C.ker_resL E p]
    exact Module.Finite.equiv
      (Submodule.comapSubtypeEquivOfLe (C.LSpace_sub_single_le E p)).symm
  haveI hq : FiniteDimensional K (↥(C.LSpace E) ⧸ LinearMap.ker (C.resL E p)) :=
    Module.Finite.equiv (LinearMap.quotKerEquivRange (C.resL E p)).symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker (C.resL E p))

lemma IsCurve.finiteDimensional_LSpace (hC : C.IsCurve) (D : P →₀ ℤ) :
    FiniteDimensional K (C.LSpace D) := by
  classical
  obtain ⟨p₀⟩ := C.place_nonempty
  have hdegpos : 0 < (C.deg p₀ : ℤ) := by exact_mod_cast hC.deg_pos p₀
  obtain ⟨n, hn⟩ : ∃ n : ℕ, C.degD D - (n : ℤ) * C.deg p₀ < 0 := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((C.degD D : ℚ) / (C.deg p₀ : ℚ))
    refine ⟨n, ?_⟩
    have h1 : (C.degD D : ℚ) < n * (C.deg p₀ : ℚ) := by
      rw [div_lt_iff₀ (by exact_mod_cast hdegpos)] at hn
      exact_mod_cast hn
    have h2 : (C.degD D : ℤ) < (n : ℤ) * C.deg p₀ := by exact_mod_cast h1
    linarith
  have key : ∀ m : ℕ, ∀ E : P →₀ ℤ,
      FiniteDimensional K (C.LSpace (E - Finsupp.single p₀ (m : ℤ))) →
      FiniteDimensional K (C.LSpace E) := by
    intro m
    induction m with
    | zero =>
        intro E h
        have h0 : Finsupp.single p₀ ((0 : ℕ) : ℤ) = 0 := by simp
        rwa [h0, sub_zero] at h
    | succ m ih =>
        intro E h
        refine ih E (hC.finiteDimensional_LSpace_step _ p₀ ?_)
        have hs : E - Finsupp.single p₀ (m : ℤ) - Finsupp.single p₀ 1 =
            E - Finsupp.single p₀ ((m : ℤ) + 1) := by
          rw [sub_sub, ← Finsupp.single_add]
        rw [hs]
        have hc : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [hc]
        exact h
  refine key n D ?_
  have hdeg : C.degD (D - Finsupp.single p₀ (n : ℤ)) < 0 := by
    rw [C.degD_sub, C.degD_single]
    linarith
  rw [C.LSpace_eq_bot_of_degD_neg hdeg]
  infer_instance

end PreCurve

end Math2

/-
The canonical divisor and the duality theorem.
-/
import RequestProject.Math2.Duality

namespace Math2

open Module Submodule

namespace PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]
variable {C : PreCurve K F P}

/-! ### Elementary properties of the action on differentials -/

@[simp] lemma smulDual_zero_left (C : PreCurve K F P) (ω : Module.Dual K C.Adele) :
    C.smulDual (0 : F) ω = 0 := by
  ext α
  have h0 : C.mulAdele (0 : F) α = 0 := by
    apply Adele.val_injective
    funext p
    simp
  simp [smulDual_apply, h0]

lemma smulDual_neg (C : PreCurve K F P) (x : F) (ω : Module.Dual K C.Adele) :
    C.smulDual (-x) ω = -C.smulDual x ω := by
  ext α
  have h0 : C.mulAdele (-x) α = -C.mulAdele x α := by
    apply Adele.val_injective
    funext p
    simp
  simp [smulDual_apply, h0]

/-! ### Numerical consequences of the Riemann inequality -/

lemma IsCurve.ell_ge (hC : C.IsCurve) (D : P →₀ ℤ) :
    C.degD D + 1 - C.genus ≤ (C.ell D : ℤ) := by
  have h := hC.ell_sub_iH D
  have h2 : (0 : ℤ) ≤ C.iH D := Int.natCast_nonneg _
  linarith

lemma IsCurve.iH_eq_of_degD_neg (hC : C.IsCurve) {D : P →₀ ℤ} (h : C.degD D < 0) :
    (C.iH D : ℤ) = -C.degD D - 1 + C.genus := by
  have h1 := hC.ell_sub_iH D
  have h2 : C.ell D = 0 := C.ell_eq_zero_of_degD_neg D h
  rw [h2] at h1
  push_cast at h1
  linarith

/-! ### Multiplying a differential by a function of a Riemann-Roch space -/

/-- If `ω` vanishes on `A(A) + F` and `x ∈ L(A - D)`, then `xω` vanishes on `A(D) + F`. -/
lemma smulDual_mem_OmegaSub_of_mem_LSpace {A D : P →₀ ℤ} {ω : Module.Dual K C.Adele}
    (hω : ω ∈ C.OmegaSub A) {x : F} (hx : x ∈ C.LSpace (A - D)) :
    C.smulDual x ω ∈ C.OmegaSub D := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [C.smulDual_zero_left]
    exact Submodule.zero_mem _
  · have hmem := mem_OmegaSub_smulDual hx0 hω
    refine C.OmegaSub_antitone ?_ hmem
    intro p
    have h := hx p
    rw [C.ord_eq_ordZ hx0] at h
    have h2 : -((A - D) p) ≤ C.ordZ p x := by exact_mod_cast h
    simp only [Finsupp.coe_sub, Pi.sub_apply] at h2
    simp only [Finsupp.coe_add, Pi.add_apply, C.divisorOf_apply hx0 p]
    omega

/-! ### Existence of a nonzero Weil differential -/

lemma IsCurve.exists_nonzero_weil (hC : C.IsCurve) :
    ∃ (A : P →₀ ℤ) (ω : Module.Dual K C.Adele), ω ≠ 0 ∧ ω ∈ C.OmegaSub A := by
  obtain ⟨p₀⟩ := C.place_nonempty
  have hd : 0 < (C.deg p₀ : ℤ) := by exact_mod_cast hC.deg_pos p₀
  set A : P →₀ ℤ := Finsupp.single p₀ (-2) with hA
  have hdeg : C.degD A = -2 * C.deg p₀ := by rw [hA, C.degD_single]
  have hneg : C.degD A < 0 := by rw [hdeg]; linarith
  have hiH : (C.iH A : ℤ) = -C.degD A - 1 + C.genus := hC.iH_eq_of_degD_neg hneg
  have hpos : 0 < C.iH A := by
    have hg : (0 : ℤ) ≤ C.genus := Int.natCast_nonneg _
    have : (0 : ℤ) < C.iH A := by rw [hiH, hdeg]; linarith
    exact_mod_cast this
  haveI := hC.finiteDimensional_OmegaSub A
  have hne : C.OmegaSub A ≠ ⊥ := by
    intro h
    have : finrank K (C.OmegaSub A) = 0 := by rw [h, finrank_bot]
    rw [hC.finrank_OmegaSub A] at this
    omega
  obtain ⟨ω, hω, hω0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨A, ω, hω0, hω⟩

/-! ### The degree of a divisor of a differential is bounded -/

lemma IsCurve.degD_le_of_mem_OmegaSub (hC : C.IsCurve) {A : P →₀ ℤ}
    {ω : Module.Dual K C.Adele} (hω : ω ∈ C.OmegaSub A) (hω0 : ω ≠ 0) :
    C.degD A ≤ 2 * C.genus - 2 := by
  obtain ⟨p₀⟩ := C.place_nonempty
  have hd : 0 < (C.deg p₀ : ℤ) := by exact_mod_cast hC.deg_pos p₀
  set B : P →₀ ℤ := Finsupp.single p₀ 1 with hB
  have hdegB : C.degD B = C.deg p₀ := by rw [hB, C.degD_single]; ring
  have hkey : (C.ell (B + A) : ℤ) ≤ (C.iH (-B) : ℤ) := by
    exact_mod_cast hC.ell_le_iH_neg hω hω0 B
  have h1 : C.degD (B + A) + 1 - C.genus ≤ (C.ell (B + A) : ℤ) := hC.ell_ge _
  have hnegB : C.degD (-B) < 0 := by rw [C.degD_neg, hdegB]; linarith
  have h2 : (C.iH (-B) : ℤ) = -C.degD (-B) - 1 + C.genus := hC.iH_eq_of_degD_neg hnegB
  rw [C.degD_neg, hdegB] at h2
  rw [C.degD_add, hdegB] at h1
  linarith

/-! ### One-dimensionality of the space of Weil differentials -/

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
lemma IsCurve.exists_smul_eq (hC : C.IsCurve) {A A' : P →₀ ℤ}
    {ω ω' : Module.Dual K C.Adele} (hω : ω ∈ C.OmegaSub A) (hω0 : ω ≠ 0)
    (hω' : ω' ∈ C.OmegaSub A') : ∃ x : F, ω' = C.smulDual x ω := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨p₀⟩ := C.place_nonempty
  have hd : 1 ≤ (C.deg p₀ : ℤ) := by exact_mod_cast hC.deg_pos p₀
  have hω'0 : ω' ≠ 0 := by
    intro h
    exact hcon 0 (by rw [h, C.smulDual_zero_left])
  set N : ℤ := 3 * C.genus - 3 - C.degD A - C.degD A' with hN
  have key : ∀ m : ℤ, 1 ≤ m → m * C.deg p₀ ≤ N := by
    intro m hm
    set B : P →₀ ℤ := Finsupp.single p₀ m with hB
    have hdegB : C.degD B = m * C.deg p₀ := by rw [hB, C.degD_single]
    haveI := hC.finiteDimensional_LSpace (B + A)
    haveI := hC.finiteDimensional_LSpace (B + A')
    haveI := hC.finiteDimensional_OmegaSub (-B)
    set g₁ : ↥(C.LSpace (B + A)) →ₗ[K] ↥(C.OmegaSub (-B)) :=
      LinearMap.codRestrict (C.OmegaSub (-B))
        ((C.toDualLin ω).comp (C.LSpace (B + A)).subtype)
        (fun x => smulDual_mem_OmegaSub_neg hω x.2) with hg₁
    set g₂ : ↥(C.LSpace (B + A')) →ₗ[K] ↥(C.OmegaSub (-B)) :=
      LinearMap.codRestrict (C.OmegaSub (-B))
        ((C.toDualLin ω').comp (C.LSpace (B + A')).subtype)
        (fun x => smulDual_mem_OmegaSub_neg hω' x.2) with hg₂
    set f := g₁.coprod g₂ with hf
    have hker : LinearMap.ker f = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      rintro ⟨x, y⟩ hxy
      have hval : C.smulDual (x : F) ω + C.smulDual (y : F) ω' = 0 := by
        have := congrArg (Subtype.val) hxy
        simpa [hf, hg₁, hg₂] using this
      have hy0 : (y : F) = 0 := by
        by_contra hy
        refine hcon (-((y : F)⁻¹ * x)) ?_
        have h1 : C.smulDual ((y : F)⁻¹) (C.smulDual (y : F) ω') = ω' := by
          rw [← C.smulDual_mul, inv_mul_cancel₀ hy, C.smulDual_one]
        have h2 : C.smulDual (y : F) ω' = -C.smulDual (x : F) ω :=
          eq_neg_of_add_eq_zero_right hval
        rw [h2] at h1
        have h3 : C.smulDual ((y : F)⁻¹) (-C.smulDual (x : F) ω)
            = -C.smulDual ((y : F)⁻¹ * (x : F)) ω := by
          rw [C.smulDual_mul]
          ext α
          simp [smulDual_apply]
        rw [h3] at h1
        rw [C.smulDual_neg, h1]
      have hx0 : (x : F) = 0 := by
        by_contra hx
        rw [hy0, C.smulDual_zero_left, add_zero] at hval
        exact hω0 ((C.smulDual_eq_zero_iff hx ω).1 hval)
      exact Prod.ext (Subtype.ext hx0) (Subtype.ext hy0)
    have hinj : Function.Injective f := by
      intro z w hzw
      have hz : z - w ∈ LinearMap.ker f := by
        rw [LinearMap.mem_ker, map_sub, hzw, sub_self]
      rw [hker, Submodule.mem_bot, sub_eq_zero] at hz
      exact hz
    have hrank := LinearMap.finrank_le_finrank_of_injective (f := f) hinj
    rw [Module.finrank_prod, hC.finrank_OmegaSub (-B)] at hrank
    have hrank' : (C.ell (B + A) : ℤ) + (C.ell (B + A') : ℤ) ≤ (C.iH (-B) : ℤ) := by
      exact_mod_cast hrank
    have h1 : C.degD (B + A) + 1 - C.genus ≤ (C.ell (B + A) : ℤ) := hC.ell_ge _
    have h2 : C.degD (B + A') + 1 - C.genus ≤ (C.ell (B + A') : ℤ) := hC.ell_ge _
    have hnegB : C.degD (-B) < 0 := by
      rw [C.degD_neg, hdegB]
      nlinarith
    have h3 : (C.iH (-B) : ℤ) = -C.degD (-B) - 1 + C.genus := hC.iH_eq_of_degD_neg hnegB
    rw [C.degD_neg, hdegB] at h3
    rw [C.degD_add, hdegB] at h1
    rw [C.degD_add, hdegB] at h2
    rw [hN]
    linarith
  have hm := key (max 1 (N + 1)) (le_max_left _ _)
  have h1 : (1 : ℤ) ≤ max 1 (N + 1) := le_max_left _ _
  have h2 : N + 1 ≤ max 1 (N + 1) := le_max_right _ _
  nlinarith

/-! ### Divisors of differentials are closed under `sup` -/

lemma AD_sup_le (C : PreCurve K F P) (A B : P →₀ ℤ) :
    C.AD (A ⊔ B) ≤ C.AD A ⊔ C.AD B := by
  classical
  intro α hα
  have hsup : ∀ p : P, (A ⊔ B) p = max (A p) (B p) := by
    intro p; rw [Finsupp.sup_apply]
  have hmem : (fun p => if B p ≤ A p then α.val p else 0) ∈ C.AdeleF := by
    obtain ⟨S, hS⟩ := α.val_mem
    refine ⟨S, fun p hp => ?_⟩
    by_cases h : B p ≤ A p
    · simpa [h] using hS p hp
    · simp [h]
  set β : C.Adele := Adele.mk C (fun p => if B p ≤ A p then α.val p else 0) hmem with hβ
  have hβA : β ∈ C.AD A := by
    intro p
    have h := hα p
    rw [hsup p] at h
    by_cases hc : B p ≤ A p
    · have : max (A p) (B p) = A p := max_eq_left hc
      rw [this] at h
      simpa [hβ, hc] using h
    · simp [hβ, hc]
  have hγB : α - β ∈ C.AD B := by
    intro p
    have h := hα p
    rw [hsup p] at h
    by_cases hc : B p ≤ A p
    · have : (α - β).val p = 0 := by simp [hβ, hc]
      rw [this]
      simp
    · have hBA : max (A p) (B p) = B p := max_eq_right (le_of_lt (lt_of_not_ge hc))
      rw [hBA] at h
      have hval : (α - β).val p = α.val p := by simp [hβ, hc]
      rw [hval]
      exact h
  have : α = β + (α - β) := by abel
  rw [this]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hβA) (Submodule.mem_sup_right hγB)

lemma OmegaSub_sup {A B : P →₀ ℤ} {ω : Module.Dual K C.Adele}
    (hA : ω ∈ C.OmegaSub A) (hB : ω ∈ C.OmegaSub B) : ω ∈ C.OmegaSub (A ⊔ B) := by
  rw [mem_OmegaSub_iff] at hA hB ⊢
  intro α hα
  rcases Submodule.mem_sup.1 hα with ⟨a, ha, y, hy, rfl⟩
  rcases Submodule.mem_sup.1 (C.AD_sup_le A B ha) with ⟨b, hb, c, hc, rfl⟩
  rw [map_add, map_add, hA b (Submodule.mem_sup_left hb),
    hB c (Submodule.mem_sup_left hc), hA y (Submodule.mem_sup_right hy)]
  simp

lemma IsCurve.degD_pos (hC : C.IsCurve) {E : P →₀ ℤ} (hE : ∀ p, 0 ≤ E p) {p₁ : P}
    (h : 0 < E p₁) : 0 < C.degD E := by
  classical
  have hmem : p₁ ∈ E.support := by
    rw [Finsupp.mem_support_iff]
    omega
  have hsum : C.degD E = ∑ p ∈ E.support, E p * (C.deg p : ℤ) := C.degD_eq_sum (Finset.Subset.refl _)
  have hnonneg : ∀ p ∈ E.support, 0 ≤ E p * (C.deg p : ℤ) := by
    intro p _
    have := hE p
    positivity
  have hle := Finset.single_le_sum (f := fun p => E p * (C.deg p : ℤ)) hnonneg hmem
  have hd : 0 < (C.deg p₁ : ℤ) := by exact_mod_cast hC.deg_pos p₁
  have : 0 < E p₁ * (C.deg p₁ : ℤ) := by positivity
  rw [hsum]
  linarith

/-- Existence of a canonical divisor: a maximal divisor `W` with `ω ∈ Ω(W)`. -/
lemma IsCurve.exists_canonical (hC : C.IsCurve) {ω : Module.Dual K C.Adele} (hω0 : ω ≠ 0)
    {A₀ : P →₀ ℤ} (hA₀ : ω ∈ C.OmegaSub A₀) :
    ∃ W : P →₀ ℤ, ω ∈ C.OmegaSub W ∧ ∀ A : P →₀ ℤ, ω ∈ C.OmegaSub A → A ≤ W := by
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, (∃ A : P →₀ ℤ, ω ∈ C.OmegaSub A ∧ C.degD A = z) → z ≤ b := by
    refine ⟨2 * C.genus - 2, ?_⟩
    rintro z ⟨A, hA, rfl⟩
    exact hC.degD_le_of_mem_OmegaSub hA hω0
  have hne : ∃ z : ℤ, ∃ A : P →₀ ℤ, ω ∈ C.OmegaSub A ∧ C.degD A = z :=
    ⟨C.degD A₀, A₀, hA₀, rfl⟩
  obtain ⟨ub, ⟨W, hW, hWdeg⟩, hmax⟩ := Int.exists_greatest_of_bdd hbdd hne
  refine ⟨W, hW, ?_⟩
  intro A hA
  by_contra hle
  obtain ⟨p₁, hp₁⟩ : ∃ p : P, W p < A p := by
    by_contra h
    push_neg at h
    exact hle (Finsupp.le_def.2 h)
  have hsupmem : ω ∈ C.OmegaSub (A ⊔ W) := OmegaSub_sup hA hW
  have hsup : ∀ p : P, (A ⊔ W) p = max (A p) (W p) := by
    intro p; rw [Finsupp.sup_apply]
  have hEpos : 0 < C.degD ((A ⊔ W) - W) := by
    refine hC.degD_pos (E := (A ⊔ W) - W) (fun p => ?_) (p₁ := p₁) ?_
    · simp only [Finsupp.coe_sub, Pi.sub_apply, hsup p]
      have := le_max_right (A p) (W p)
      omega
    · simp only [Finsupp.coe_sub, Pi.sub_apply, hsup p₁]
      have : max (A p₁) (W p₁) = A p₁ := max_eq_left (le_of_lt hp₁)
      omega
  rw [C.degD_sub] at hEpos
  have h1 := hmax (C.degD (A ⊔ W)) ⟨A ⊔ W, hsupmem, rfl⟩
  omega

/-! ### Duality -/

lemma divisorOf_inv {x : F} (hx : x ≠ 0) : C.divisorOf x⁻¹ = -C.divisorOf x := by
  ext p
  rw [C.divisorOf_apply (inv_ne_zero hx) p]
  simp [C.divisorOf_apply hx p, C.ordZ_inv]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The duality theorem: there is a divisor `W` with `ell (W - D) = i(D)` for all `D`. -/
theorem IsCurve.exists_canonical_ell (hC : C.IsCurve) :
    ∃ W : P →₀ ℤ, ∀ D : P →₀ ℤ, C.ell (W - D) = C.iH D := by
  obtain ⟨A₀, ω, hω0, hω⟩ := hC.exists_nonzero_weil
  obtain ⟨W, hW, hWmax⟩ := hC.exists_canonical hω0 hω
  refine ⟨W, fun D => ?_⟩
  haveI := hC.finiteDimensional_LSpace (W - D)
  haveI := hC.finiteDimensional_OmegaSub D
  set f : ↥(C.LSpace (W - D)) →ₗ[K] ↥(C.OmegaSub D) :=
    LinearMap.codRestrict (C.OmegaSub D)
      ((C.toDualLin ω).comp (C.LSpace (W - D)).subtype)
      (fun x => smulDual_mem_OmegaSub_of_mem_LSpace hW x.2) with hf
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hval : C.smulDual (x : F) ω = 0 := by
      have := congrArg (Subtype.val) hx
      simpa [hf] using this
    by_contra hne
    have hx0 : (x : F) ≠ 0 := fun h => hne (Subtype.ext h)
    exact hω0 ((C.smulDual_eq_zero_iff hx0 ω).1 hval)
  have hinj : Function.Injective f := by
    intro z w hzw
    have hz : z - w ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, map_sub, hzw, sub_self]
    rw [hker, Submodule.mem_bot, sub_eq_zero] at hz
    exact hz
  have hsurj : Function.Surjective f := by
    rintro ⟨ω', hω'⟩
    obtain ⟨x, hx⟩ := hC.exists_smul_eq hW hω0 hω'
    have hxmem : x ∈ C.LSpace (W - D) := by
      rcases eq_or_ne x 0 with rfl | hx0
      · exact Submodule.zero_mem _
      · have hinv : x⁻¹ ≠ 0 := inv_ne_zero hx0
        have h1 : C.smulDual x⁻¹ ω' ∈ C.OmegaSub (D + C.divisorOf x⁻¹) :=
          mem_OmegaSub_smulDual hinv hω'
        have h2 : C.smulDual x⁻¹ ω' = ω := by
          rw [hx, ← C.smulDual_mul, inv_mul_cancel₀ hx0, C.smulDual_one]
        rw [h2, C.divisorOf_inv hx0] at h1
        have h3 := hWmax _ h1
        intro p
        have h4 := Finsupp.le_def.1 h3 p
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_neg, Pi.neg_apply,
          C.divisorOf_apply hx0 p] at h4
        rw [C.ord_eq_ordZ hx0]
        have : -((W - D) p) ≤ C.ordZ p x := by
          simp only [Finsupp.coe_sub, Pi.sub_apply]
          omega
        exact_mod_cast this
    refine ⟨⟨x, hxmem⟩, ?_⟩
    apply Subtype.ext
    simpa [hf] using hx.symm
  have hiso := (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq
  rw [hC.finrank_OmegaSub D] at hiso
  exact hiso

/-- Riemann-Roch for a smooth projective curve. -/
theorem IsCurve.riemann_roch (hC : C.IsCurve) :
    ∃ W : P →₀ ℤ, ∀ D : P →₀ ℤ,
      (C.ell D : ℤ) - (C.ell (W - D) : ℤ) = C.degD D + 1 - C.genus := by
  obtain ⟨W, hWd⟩ := hC.exists_canonical_ell
  refine ⟨W, fun D => ?_⟩
  rw [hWd D]
  exact hC.ell_sub_iH D

end PreCurve

end Math2

/-
Weil differentials.
-/
import RequestProject.Math2.Genus

namespace Math2

open Module Submodule

namespace PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]
variable (C : PreCurve K F P)

/-! ### Multiplication of adeles by functions -/

/-- Multiplication of an adele by an element of the function field. -/
def mulAdele (x : F) : C.Adele →ₗ[K] C.Adele where
  toFun α := Adele.mk C (fun p => x * α.val p) (C.mul_mem_AdeleF x α.val_mem)
  map_add' := by
    intro α β
    apply Adele.val_injective
    funext p
    simp [mul_add]
  map_smul' := by
    intro c α
    apply Adele.val_injective
    funext p
    simp only [Adele.val_mk, Adele.val_smul, Pi.smul_apply, Algebra.smul_def, RingHom.id_apply]
    ring

@[simp] lemma mulAdele_val (x : F) (α : C.Adele) : (C.mulAdele x α).val = fun p => x * α.val p :=
  rfl

lemma mulAdele_diagLin (x y : F) : C.mulAdele x (C.diagLin y) = C.diagLin (x * y) := by
  apply Adele.val_injective
  funext p
  simp

lemma mulAdele_mul (x y : F) (α : C.Adele) :
    C.mulAdele (x * y) α = C.mulAdele x (C.mulAdele y α) := by
  apply Adele.val_injective
  funext p
  simp [mul_assoc]

lemma mulAdele_comm (x y : F) (α : C.Adele) :
    C.mulAdele x (C.mulAdele y α) = C.mulAdele y (C.mulAdele x α) := by
  rw [← C.mulAdele_mul, ← C.mulAdele_mul, mul_comm]

@[simp] lemma mulAdele_one (α : C.Adele) : C.mulAdele 1 α = α := by
  apply Adele.val_injective
  funext p
  simp

lemma ord_mul_ge (p : P) (x y : F) (hx : x ≠ 0) (a : ℤ) (h : ((a : ℤ) : Zt) ≤ C.ord p y) :
    ((a + C.ordZ p x : ℤ) : Zt) ≤ C.ord p (x * y) := by
  rw [C.ord_mul, C.ord_eq_ordZ hx, add_comm (((C.ordZ p x : ℤ)) : Zt)]
  push_cast
  exact add_le_add_left h _

/-! ### Principal divisors -/

open Classical in
/-- The divisor of a nonzero function. -/
noncomputable def divisorOf (x : F) : P →₀ ℤ :=
  if hx : x = 0 then 0
  else Finsupp.onFinset (C.ord_support x hx).choose (fun p => C.ordZ p x) (by
    intro p hp
    by_contra hpS
    exact hp (by simp [ordZ, (C.ord_support x hx).choose_spec p hpS]))

lemma divisorOf_apply {x : F} (hx : x ≠ 0) (p : P) : C.divisorOf x p = C.ordZ p x := by
  classical
  rw [divisorOf, dif_neg hx]
  rfl

lemma degD_divisorOf {x : F} (hx : x ≠ 0) : C.degD (C.divisorOf x) = 0 := by
  classical
  set S := (C.ord_support x hx).choose with hS
  have hsupp : ∀ p ∉ S, C.ord p x = (0 : Zt) := (C.ord_support x hx).choose_spec
  have hsub : (C.divisorOf x).support ⊆ S := by
    intro p hp
    rw [divisorOf, dif_neg hx] at hp
    exact Finsupp.support_onFinset_subset hp
  rw [C.degD_eq_sum hsub]
  have h0 := C.degree_principal x hx S hsupp
  rw [← h0]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [C.divisorOf_apply hx p]
  simp only [ordZ]
  ring

/-! ### Weil differentials -/

/-- The space of Weil differentials with pole divisor bounded by `A`:
linear functionals on the adeles vanishing on `A(A) + F`. -/
def OmegaSub (A : P →₀ ℤ) : Submodule K (Module.Dual K C.Adele) :=
  (C.AD A ⊔ C.FSub).dualAnnihilator

lemma mem_OmegaSub_iff {A : P →₀ ℤ} {ω : Module.Dual K C.Adele} :
    ω ∈ C.OmegaSub A ↔ ∀ α ∈ C.AD A ⊔ C.FSub, ω α = 0 :=
  Submodule.mem_dualAnnihilator ω

lemma OmegaSub_antitone {A B : P →₀ ℤ} (h : A ≤ B) : C.OmegaSub B ≤ C.OmegaSub A := by
  intro ω hω
  rw [mem_OmegaSub_iff] at *
  intro α hα
  exact hω α (le_trans (sup_le_sup_right (C.AD_mono h) _) le_rfl hα)

/-- A Weil differential: a functional vanishing on `A(A) + F` for some divisor `A`. -/
def IsWeil (ω : Module.Dual K C.Adele) : Prop := ∃ A : P →₀ ℤ, ω ∈ C.OmegaSub A

/-- The action of the function field on differentials. -/
def smulDual (x : F) (ω : Module.Dual K C.Adele) : Module.Dual K C.Adele :=
  ω.comp (C.mulAdele x)

@[simp] lemma smulDual_apply (x : F) (ω : Module.Dual K C.Adele) (α : C.Adele) :
    C.smulDual x ω α = ω (C.mulAdele x α) := rfl

@[simp] lemma smulDual_one (ω : Module.Dual K C.Adele) : C.smulDual 1 ω = ω := by
  ext α
  simp

lemma smulDual_mul (x y : F) (ω : Module.Dual K C.Adele) :
    C.smulDual (x * y) ω = C.smulDual x (C.smulDual y ω) := by
  ext α
  simp only [smulDual_apply, C.mulAdele_mul, C.mulAdele_comm x y α]

lemma smulDual_eq_zero_iff {x : F} (hx : x ≠ 0) (ω : Module.Dual K C.Adele) :
    C.smulDual x ω = 0 ↔ ω = 0 := by
  constructor
  · intro h
    have : C.smulDual x⁻¹ (C.smulDual x ω) = 0 := by rw [h]; ext α; simp
    rw [← C.smulDual_mul, inv_mul_cancel₀ hx, C.smulDual_one] at this
    exact this
  · intro h; rw [h]; ext α; simp

end PreCurve

end Math2

/-
Finiteness of all cohomology groups, the genus, and the Riemann part of Riemann-Roch.
-/
import RequestProject.Math2.Chi

namespace Math2

open Module Submodule

namespace PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]
variable (C : PreCurve K F P)

/-- The Euler characteristic `ell(D) - i(D)`. -/
noncomputable def chiD (D : P →₀ ℤ) : ℤ := (C.ell D : ℤ) - C.iH D

/-- The genus of the curve: the dimension of `H¹` of the zero divisor. -/
noncomputable def genus : ℕ := C.iH 0

end PreCurve

namespace PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]
variable {C : PreCurve K F P}

lemma add_single_succ (D : P →₀ ℤ) (a : P) (n : ℤ) :
    D + Finsupp.single a (n + 1) = (D + Finsupp.single a n) + Finsupp.single a 1 := by
  rw [add_assoc, ← Finsupp.single_add]

lemma add_single_pred (D : P →₀ ℤ) (a : P) (n : ℤ) :
    (D + Finsupp.single a (n - 1)) + Finsupp.single a 1 = D + Finsupp.single a n := by
  rw [add_assoc, ← Finsupp.single_add]
  congr 2
  ring

lemma IsCurve.H1_finite_single (hC : C.IsCurve) (D : P →₀ ℤ) (a : P) (b : ℤ)
    (h : Module.Finite K (C.H1 D)) : Module.Finite K (C.H1 (D + Finsupp.single a b)) := by
  induction b using Int.induction_on with
  | zero => rw [Finsupp.single_zero, add_zero]; exact h
  | succ n ih =>
      rw [add_single_succ D a (n : ℤ)]
      exact hC.H1_finite_add _ a ih
  | pred n ih =>
      refine hC.H1_finite_of_add (D + Finsupp.single a (-(n : ℤ) - 1)) a ?_
      rw [add_single_pred D a (-(n : ℤ))]
      exact ih

lemma IsCurve.H1_finite_shift (hC : C.IsCurve) (E : P →₀ ℤ) :
    ∀ D : P →₀ ℤ, Module.Finite K (C.H1 D) → Module.Finite K (C.H1 (D + E)) := by
  induction E using Finsupp.induction with
  | zero => intro D h; rw [add_zero]; exact h
  | single_add a b f _ _ ih =>
      intro D h
      have h1 : Module.Finite K (C.H1 (D + Finsupp.single a b)) :=
        hC.H1_finite_single D a b h
      have h2 := ih (D + Finsupp.single a b) h1
      have hEq : D + Finsupp.single a b + f = D + (Finsupp.single a b + f) := by
        rw [add_assoc]
      rwa [hEq] at h2

/-- All cohomology groups of a curve are finite dimensional. -/
lemma IsCurve.H1_finite (hC : C.IsCurve) (D : P →₀ ℤ) : Module.Finite K (C.H1 D) := by
  obtain ⟨D₀, h₀⟩ := hC.properness
  have h := hC.H1_finite_shift (D - D₀) D₀ h₀
  have hEq : D₀ + (D - D₀) = D := by abel
  rwa [hEq] at h

lemma IsCurve.chiD_add_single (hC : C.IsCurve) (D : P →₀ ℤ) (a : P) (b : ℤ) :
    C.chiD (D + Finsupp.single a b) = C.chiD D + b * C.deg a := by
  induction b using Int.induction_on with
  | zero => rw [Finsupp.single_zero, add_zero]; ring
  | succ n ih =>
      rw [add_single_succ D a (n : ℤ)]
      have hstep := hC.chi_step (D + Finsupp.single a (n : ℤ)) a
        (hC.H1_finite (D + Finsupp.single a (n : ℤ)))
      simp only [chiD] at *
      rw [hstep, ih]
      ring
  | pred n ih =>
      have hstep := hC.chi_step (D + Finsupp.single a (-(n : ℤ) - 1)) a
        (hC.H1_finite (D + Finsupp.single a (-(n : ℤ) - 1)))
      rw [add_single_pred D a (-(n : ℤ))] at hstep
      simp only [chiD] at *
      rw [ih] at hstep
      push_cast at hstep ⊢
      linarith

lemma IsCurve.chiD_add (hC : C.IsCurve) (E : P →₀ ℤ) :
    ∀ D : P →₀ ℤ, C.chiD (D + E) = C.chiD D + C.degD E := by
  induction E using Finsupp.induction with
  | zero => intro D; simp
  | single_add a b f _ _ ih =>
      intro D
      have hEq : D + (Finsupp.single a b + f) = (D + Finsupp.single a b) + f := by
        rw [add_assoc]
      rw [hEq, ih (D + Finsupp.single a b), hC.chiD_add_single D a b, C.degD_add,
        C.degD_single]
      ring

/-- The Riemann part of the Riemann-Roch theorem: `ell(D) - i(D) = deg D + 1 - g`. -/
theorem IsCurve.chiD_eq (hC : C.IsCurve) (D : P →₀ ℤ) :
    C.chiD D = C.degD D + 1 - C.genus := by
  have h := hC.chiD_add D 0
  rw [zero_add] at h
  rw [h, chiD, genus, ell_zero]
  ring

lemma IsCurve.ell_sub_iH (hC : C.IsCurve) (D : P →₀ ℤ) :
    (C.ell D : ℤ) - C.iH D = C.degD D + 1 - C.genus := hC.chiD_eq D

end PreCurve

end Math2

/-
Local theory at a place: uniformizers and residue maps.
-/
import RequestProject.Math2.Setup

namespace Math2

open Module Submodule

namespace PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]
variable (C : PreCurve K F P)

lemma ordZ_zero (p : P) : C.ordZ p 0 = 0 := by simp [ordZ]

lemma ordZ_inv (p : P) (x : F) : C.ordZ p x⁻¹ = - C.ordZ p x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ordZ]
  · have h := C.ord_inv p x
    rw [C.ord_eq_ordZ hx, C.ord_eq_ordZ (inv_ne_zero hx)] at h
    exact_mod_cast h

lemma ordZ_pow (p : P) (x : F) (hx : x ≠ 0) (n : ℕ) : C.ordZ p (x ^ n) = n * C.ordZ p x := by
  induction n with
  | zero => simp [ordZ]
  | succ n ih =>
      rw [pow_succ, C.ordZ_mul (pow_ne_zero n hx) hx, ih]
      push_cast
      ring

lemma ordZ_zpow (p : P) (x : F) (hx : x ≠ 0) (n : ℤ) : C.ordZ p (x ^ n) = n * C.ordZ p x := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg n <;> subst hm
  · rw [zpow_natCast, C.ordZ_pow p x hx m]
  · rw [zpow_neg, zpow_natCast, C.ordZ_inv, C.ordZ_pow p x hx m]
    push_cast
    ring

/-- A chosen uniformizer at a place. -/
noncomputable def unif (p : P) : F := (C.uniformizer p).choose

lemma ord_unif (p : P) : C.ord p (C.unif p) = ((1 : ℤ) : Zt) := (C.uniformizer p).choose_spec

lemma unif_ne_zero (p : P) : C.unif p ≠ 0 := by
  intro h
  have := C.ord_unif p
  rw [h] at this
  simp at this

lemma ordZ_unif (p : P) : C.ordZ p (C.unif p) = 1 := by
  have := C.ord_unif p
  rw [C.ord_eq_ordZ (C.unif_ne_zero p)] at this
  exact_mod_cast this

lemma ord_unif_zpow (p : P) (n : ℤ) : C.ord p (C.unif p ^ n) = ((n : ℤ) : Zt) := by
  have hne : C.unif p ^ n ≠ 0 := zpow_ne_zero _ (C.unif_ne_zero p)
  rw [C.ord_eq_ordZ hne, C.ordZ_zpow p _ (C.unif_ne_zero p) n, C.ordZ_unif p, mul_one]

lemma ord_unif_zpow_mul (p : P) (n : ℤ) (y : F) :
    C.ord p (C.unif p ^ n * y) = ((n : ℤ) : Zt) + C.ord p y := by
  rw [C.ord_mul, C.ord_unif_zpow]

lemma ord_shift_ge (p : P) (n a : ℤ) (y : F) (h : ((a : ℤ) : Zt) ≤ C.ord p y) :
    ((a + n : ℤ) : Zt) ≤ C.ord p (C.unif p ^ n * y) := by
  rw [C.ord_unif_zpow_mul, add_comm ((n : ℤ) : Zt)]
  push_cast
  exact add_le_add_left h _

lemma ord_shift_le (p : P) (n a : ℤ) (y : F)
    (h : ((a : ℤ) : Zt) ≤ C.ord p (C.unif p ^ n * y)) :
    ((a - n : ℤ) : Zt) ≤ C.ord p y := by
  have := C.ord_shift_ge p (-n) a _ h
  rw [← mul_assoc, ← zpow_add₀ (C.unif_ne_zero p)] at this
  simpa using this

/-- The residue map attached to a linear map `f` into `F` whose values have `ord ≥ -n` at `p`. -/
noncomputable def resMap (p : P) (n : ℤ) {V : Type*} [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] F) (hf : ∀ v, ((-n : ℤ) : Zt) ≤ C.ord p (f v)) : V →ₗ[K] C.resField p where
  toFun v := Submodule.Quotient.mk ⟨C.unif p ^ n * f v, by
      show ((0 : ℤ) : Zt) ≤ C.ord p (C.unif p ^ n * f v)
      have := C.ord_shift_ge p n (-n) (f v) (hf v)
      simpa using this⟩
  map_add' := by
    intro v w
    rw [← Submodule.Quotient.mk_add]
    congr 1
    ext
    simp [mul_add]
  map_smul' := by
    intro c v
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    congr 1
    ext
    simp [Algebra.smul_def]
    ring

lemma resMap_eq_zero_iff (p : P) (n : ℤ) {V : Type*} [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] F) (hf : ∀ v, ((-n : ℤ) : Zt) ≤ C.ord p (f v)) (v : V) :
    C.resMap p n f hf v = 0 ↔ (((1 - n : ℤ)) : Zt) ≤ C.ord p (f v) := by
  rw [resMap]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · intro h
    have h1 : ((1 : ℤ) : Zt) ≤ C.ord p (C.unif p ^ n * f v) := h
    exact C.ord_shift_le p n 1 (f v) h1
  · intro h
    show ((1 : ℤ) : Zt) ≤ C.ord p (C.unif p ^ n * f v)
    have := C.ord_shift_ge p n (1 - n) (f v) h
    simpa using this

lemma resMap_surjective (p : P) (n : ℤ) {V : Type*} [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] F) (hf : ∀ v, ((-n : ℤ) : Zt) ≤ C.ord p (f v))
    (hs : ∀ y : F, ((0 : ℤ) : Zt) ≤ C.ord p y → ∃ v : V, f v = C.unif p ^ (-n) * y) :
    Function.Surjective (C.resMap p n f hf) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H y =>
    obtain ⟨y, hy⟩ := y
    obtain ⟨v, hv⟩ := hs y hy
    refine ⟨v, ?_⟩
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    ext
    show C.unif p ^ n * f v = y
    rw [hv, ← mul_assoc, ← zpow_add₀ (C.unif_ne_zero p)]
    simp

end PreCurve

end Math2

/-
Setup for the Riemann-Roch theorem: function fields of one variable, places,
divisors and Riemann-Roch spaces.
-/
import Mathlib

namespace Math2

open Module Submodule

universe u v w

/-- The value group with infinity. -/
abbrev Zt := WithTop ℤ

/-- Basic data of a (smooth projective) algebraic curve, described through its function
field: a field extension `F / K` together with a family of places `P`, each given by a
normalized discrete valuation of `F` which is trivial on `K`. -/
structure PreCurve (K : Type u) (F : Type v) (P : Type w) [Field K] [Field F] [Algebra K F]
    where
  /-- The (additive) valuation attached to a place. -/
  ord : P → AddValuation F Zt
  /-- The degree of a place. -/
  deg : P → ℕ
  /-- Valuations are trivial on the constants. -/
  ord_algebraMap : ∀ (p : P) (c : K), c ≠ 0 → ord p (algebraMap K F c) = (0 : Zt)
  /-- Each valuation is normalized: there is a uniformizer. -/
  uniformizer : ∀ p : P, ∃ t : F, ord p t = ((1 : ℤ) : Zt)
  /-- A nonzero function has nonzero valuation at only finitely many places. -/
  ord_support : ∀ x : F, x ≠ 0 → ∃ S : Finset P, ∀ p ∉ S, ord p x = (0 : Zt)
  /-- A principal divisor has degree zero. -/
  degree_principal : ∀ (x : F), x ≠ 0 → ∀ S : Finset P, (∀ p ∉ S, ord p x = (0 : Zt)) →
    ∑ p ∈ S, (deg p : ℤ) * ((ord p x).untopD 0) = 0
  /-- The functions which are regular everywhere are the constants. -/
  constants : ∀ x : F, (∀ p : P, (0 : Zt) ≤ ord p x) → ∃ c : K, algebraMap K F c = x
  /-- The curve has at least one place. -/
  place_nonempty : Nonempty P

namespace PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]
variable (C : PreCurve K F P)

/-- `ord` of an element, as an integer (junk value `0` at `x = 0`). -/
def ordZ (p : P) (x : F) : ℤ := (C.ord p x).untopD 0

@[simp] lemma ord_eq_top_iff {p : P} {x : F} : C.ord p x = (⊤ : Zt) ↔ x = 0 :=
  AddValuation.top_iff _

lemma ord_ne_top {p : P} {x : F} (hx : x ≠ 0) : C.ord p x ≠ (⊤ : Zt) := by
  simpa using hx

lemma ord_eq_ordZ {p : P} {x : F} (hx : x ≠ 0) : C.ord p x = ((C.ordZ p x : ℤ) : Zt) := by
  unfold ordZ
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (C.ord_ne_top hx)
  rw [← hn]
  simp

lemma ord_mul (p : P) (x y : F) : C.ord p (x * y) = C.ord p x + C.ord p y :=
  AddValuation.map_mul _ _ _

lemma ordZ_mul {p : P} {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    C.ordZ p (x * y) = C.ordZ p x + C.ordZ p y := by
  have h := C.ord_mul p x y
  rw [C.ord_eq_ordZ hx, C.ord_eq_ordZ hy, C.ord_eq_ordZ (mul_ne_zero hx hy)] at h
  exact_mod_cast h

@[simp] lemma ord_one (p : P) : C.ord p 1 = (0 : Zt) := AddValuation.map_one _

@[simp] lemma ord_zero (p : P) : C.ord p 0 = (⊤ : Zt) := AddValuation.map_zero _

lemma ord_inv (p : P) (x : F) : C.ord p x⁻¹ = - C.ord p x :=
  AddValuation.map_inv _

lemma ord_smul (p : P) (c : K) (x : F) (hc : c ≠ 0) : C.ord p (c • x) = C.ord p x := by
  rw [Algebra.smul_def, C.ord_mul, C.ord_algebraMap p c hc, zero_add]

/-! ### Divisors -/

/-- The degree of a divisor. -/
def degD (D : P →₀ ℤ) : ℤ := D.sum fun p n => n * (C.deg p : ℤ)

@[simp] lemma degD_zero : C.degD 0 = 0 := by simp [degD]

lemma degD_add (D E : P →₀ ℤ) : C.degD (D + E) = C.degD D + C.degD E := by
  classical
  simp only [degD]
  rw [Finsupp.sum_add_index'] <;> intros <;> ring

lemma degD_neg (D : P →₀ ℤ) : C.degD (-D) = - C.degD D := by
  classical
  have : C.degD (-D) + C.degD D = 0 := by
    rw [← C.degD_add]; simp
  linarith

lemma degD_sub (D E : P →₀ ℤ) : C.degD (D - E) = C.degD D - C.degD E := by
  rw [sub_eq_add_neg, C.degD_add, C.degD_neg]; ring

lemma degD_single (p : P) (n : ℤ) : C.degD (Finsupp.single p n) = n * C.deg p := by
  classical
  simp [degD, Finsupp.sum_single_index]

lemma degD_eq_sum {D : P →₀ ℤ} {S : Finset P} (hS : D.support ⊆ S) :
    C.degD D = ∑ p ∈ S, D p * (C.deg p : ℤ) := by
  classical
  rw [degD, Finsupp.sum_of_support_subset D hS _ (by intros; simp)]

/-! ### Riemann-Roch spaces -/

/-- The Riemann-Roch space `L(D) = {x : ord_p x ≥ -D p for all p}`. -/
def LSpace (D : P →₀ ℤ) : Submodule K F where
  carrier := {x : F | ∀ p : P, ((-(D p) : ℤ) : Zt) ≤ C.ord p x}
  zero_mem' := by intro p; simp
  add_mem' := by
    intro x y hx hy p
    exact le_trans (le_min (hx p) (hy p)) (AddValuation.map_add _ _ _)
  smul_mem' := by
    intro c x hx p
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · rw [C.ord_smul p c x hc]; exact hx p

lemma mem_LSpace_iff {D : P →₀ ℤ} {x : F} :
    x ∈ C.LSpace D ↔ ∀ p : P, ((-(D p) : ℤ) : Zt) ≤ C.ord p x := Iff.rfl

lemma LSpace_mono {D E : P →₀ ℤ} (h : D ≤ E) : C.LSpace D ≤ C.LSpace E := by
  intro x hx p
  refine le_trans ?_ (hx p)
  exact_mod_cast neg_le_neg (h p)

/-- The Riemann-Roch space of the zero divisor is the field of constants. -/
lemma LSpace_zero : C.LSpace 0 = LinearMap.range (Algebra.linearMap K F) := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := C.constants x (by intro p; simpa using hx p)
    exact ⟨c, hc⟩
  · rintro ⟨c, rfl⟩ p
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · simp [C.ord_algebraMap p c hc]

lemma degD_nonneg_of_mem_LSpace {D : P →₀ ℤ} {x : F} (hx : x ≠ 0) (hxD : x ∈ C.LSpace D) :
    0 ≤ C.degD D := by
  classical
  obtain ⟨S₀, hS₀⟩ := C.ord_support x hx
  set S : Finset P := S₀ ∪ D.support with hSdef
  have hsupp : ∀ p ∉ S, C.ord p x = (0 : Zt) := by
    intro p hp
    exact hS₀ p fun h => hp (Finset.mem_union_left _ h)
  have h0 := C.degree_principal x hx S hsupp
  have hle : ∀ p ∈ S, (C.deg p : ℤ) * (-(D p)) ≤ (C.deg p : ℤ) * C.ordZ p x := by
    intro p _
    have h := hxD p
    rw [C.ord_eq_ordZ hx] at h
    have : -(D p) ≤ C.ordZ p x := by exact_mod_cast h
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hsum : ∑ p ∈ S, (C.deg p : ℤ) * (-(D p)) ≤ ∑ p ∈ S, (C.deg p : ℤ) * C.ordZ p x :=
    Finset.sum_le_sum hle
  have hdeg : C.degD D = ∑ p ∈ S, D p * (C.deg p : ℤ) :=
    C.degD_eq_sum (by intro p hp; exact Finset.mem_union_right _ hp)
  have h0' : ∑ p ∈ S, (C.deg p : ℤ) * C.ordZ p x = 0 := by
    rw [← h0]; rfl
  have : ∑ p ∈ S, (C.deg p : ℤ) * (-(D p)) = - C.degD D := by
    rw [hdeg, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [this, h0'] at hsum
  linarith

lemma LSpace_eq_bot_of_degD_neg {D : P →₀ ℤ} (hD : C.degD D < 0) : C.LSpace D = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  by_contra hne
  exact absurd (C.degD_nonneg_of_mem_LSpace (by simpa using hne) hx) (by linarith)

/-! ### Local structure at a place -/

/-- `{x : F | n ≤ ord_p x}`, a `K`-subspace of `F`. -/
def valSub (p : P) (n : ℤ) : Submodule K F where
  carrier := {x : F | ((n : ℤ) : Zt) ≤ C.ord p x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at *
    exact le_trans (le_min hx hy) (AddValuation.map_add _ _ _)
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at *
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · rw [C.ord_smul p c x hc]; exact hx

lemma mem_valSub_iff {p : P} {n : ℤ} {x : F} :
    x ∈ C.valSub p n ↔ ((n : ℤ) : Zt) ≤ C.ord p x := Iff.rfl

/-- The maximal ideal of the valuation ring at `p`, viewed inside the valuation ring. -/
def maxIdeal (p : P) : Submodule K ↑(C.valSub p 0) :=
  (C.valSub p 1).comap (C.valSub p 0).subtype

/-- The residue field at a place, as a `K`-vector space. -/
abbrev resField (p : P) : Type _ := ↑(C.valSub p 0) ⧸ C.maxIdeal p

/-! ### Adeles -/

open Classical in
/-- The adele space (restricted product of the completions, realized inside `P → F`). -/
def AdeleF : Submodule K (P → F) where
  carrier := {α : P → F | ∃ S : Finset P, ∀ p ∉ S, (0 : Zt) ≤ C.ord p (α p)}
  zero_mem' := ⟨∅, by simp⟩
  add_mem' := by
    rintro α β ⟨S, hS⟩ ⟨T, hT⟩
    refine ⟨S ∪ T, fun p hp => ?_⟩
    have h1 := hS p fun h => hp (Finset.mem_union_left _ h)
    have h2 := hT p fun h => hp (Finset.mem_union_right _ h)
    exact le_trans (le_min h1 h2) (AddValuation.map_add _ _ _)
  smul_mem' := by
    rintro c α ⟨S, hS⟩
    rcases eq_or_ne c 0 with rfl | hc
    · exact ⟨∅, by simp⟩
    refine ⟨S, fun p hp => ?_⟩
    have h1 := hS p hp
    have h2 : C.ord p (c • α p) = C.ord p (α p) := C.ord_smul p c _ hc
    simpa [h2] using h1

lemma mem_AdeleF_iff {α : P → F} :
    α ∈ C.AdeleF ↔ ∃ S : Finset P, ∀ p ∉ S, (0 : Zt) ≤ C.ord p (α p) := Iff.rfl

open Classical in
/-- Multiplication of an adele by a function of `F`. -/
lemma mul_mem_AdeleF (x : F) {α : P → F} (hα : α ∈ C.AdeleF) :
    (fun p => x * α p) ∈ C.AdeleF := by
  obtain ⟨S, hS⟩ := hα
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨∅, by simp⟩
  obtain ⟨T, hT⟩ := C.ord_support x hx
  refine ⟨S ∪ T, fun p hp => ?_⟩
  have h1 := hS p fun h => hp (Finset.mem_union_left _ h)
  have h2 := hT p fun h => hp (Finset.mem_union_right _ h)
  have h3 : C.ord p (x * α p) = C.ord p x + C.ord p (α p) := C.ord_mul p _ _
  simp only [h3, h2, zero_add]
  exact h1

/-- The adele space of the curve, as a type. -/
def Adele : Type (max v w) := ↥C.AdeleF

instance : AddCommGroup C.Adele := inferInstanceAs (AddCommGroup ↥C.AdeleF)

instance : Module K C.Adele := inferInstanceAs (Module K ↥C.AdeleF)

/-- The family of local components of an adele. -/
def Adele.val {C : PreCurve K F P} (α : C.Adele) : P → F := Subtype.val α

/-- An adele from a function and a proof of almost-everywhere integrality. -/
def Adele.mk (C : PreCurve K F P) (f : P → F) (h : f ∈ C.AdeleF) : C.Adele :=
  (⟨f, h⟩ : ↥C.AdeleF)

@[simp] lemma Adele.val_mk (f : P → F) (h : f ∈ C.AdeleF) : (Adele.mk C f h).val = f := rfl

lemma Adele.val_mem (α : C.Adele) : α.val ∈ C.AdeleF := Subtype.property α

@[simp] lemma Adele.val_add (α β : C.Adele) : (α + β).val = α.val + β.val := rfl

@[simp] lemma Adele.val_zero : (0 : C.Adele).val = 0 := rfl

@[simp] lemma Adele.val_neg (α : C.Adele) : (-α).val = -α.val := rfl

@[simp] lemma Adele.val_sub (α β : C.Adele) : (α - β).val = α.val - β.val := rfl

@[simp] lemma Adele.val_smul (c : K) (α : C.Adele) : (c • α).val = c • α.val := rfl

lemma Adele.val_injective : Function.Injective (Adele.val (C := C)) :=
  fun _ _ h => Subtype.ext h

/-- The `K`-subspace `A(D)` of adeles with poles bounded by the divisor `D`. -/
def AD (D : P →₀ ℤ) : Submodule K C.Adele where
  carrier := {α | ∀ p : P, ((-(D p) : ℤ) : Zt) ≤ C.ord p (α.val p)}
  zero_mem' := by intro p; simp
  add_mem' := by
    intro α β hα hβ p
    simp only [Set.mem_setOf_eq, Adele.val_add, Pi.add_apply] at *
    exact le_trans (le_min (hα p) (hβ p)) (AddValuation.map_add _ _ _)
  smul_mem' := by
    intro c α hα p
    simp only [Set.mem_setOf_eq, Adele.val_smul, Pi.smul_apply] at *
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · rw [C.ord_smul p c _ hc]
      exact hα p

lemma mem_AD_iff {D : P →₀ ℤ} {α : C.Adele} :
    α ∈ C.AD D ↔ ∀ p : P, ((-(D p) : ℤ) : Zt) ≤ C.ord p (α.val p) := Iff.rfl

/-- The constant adele attached to a function. -/
def diagLin : F →ₗ[K] C.Adele where
  toFun x := Adele.mk C (fun _ => x) (by
    rcases eq_or_ne x 0 with rfl | hx
    · exact ⟨∅, by simp⟩
    · obtain ⟨S, hS⟩ := C.ord_support x hx
      exact ⟨S, fun p hp => by rw [hS p hp]⟩)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The image of the function field inside the adeles. -/
def FSub : Submodule K C.Adele := LinearMap.range C.diagLin

/-- The first cohomology `H¹(D) = A / (A(D) + F)`. -/
abbrev H1 (D : P →₀ ℤ) : Type _ := C.Adele ⧸ (C.AD D ⊔ C.FSub)

/-- The additional axioms making a `PreCurve` into a (smooth projective) curve: the residue
field at each place is a finite extension of `K` whose degree is the degree of the place,
and the curve is proper, i.e. some first cohomology group is finite dimensional. -/
structure IsCurve : Prop where
  /-- Each residue field is a finite extension of `K`. -/
  residue_finite : ∀ p : P, Module.Finite K (C.resField p)
  /-- The degree of a place is the degree of its residue field. -/
  residue_finrank : ∀ p : P, Module.finrank K (C.resField p) = C.deg p
  /-- Properness: some cohomology group is finite dimensional. -/
  properness : ∃ D : P →₀ ℤ, Module.Finite K (C.H1 D)

end PreCurve

end Math2

/-
The key step: comparing `H¹(D)` and `H¹(D + p)`.
-/
import RequestProject.Math2.Adeles

namespace Math2

open Module Submodule

namespace PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]
variable (C : PreCurve K F P)

/-- The map `A(E) → H¹(D)`. -/
noncomputable def psi (D E : P →₀ ℤ) : ↥(C.AD E) →ₗ[K] C.H1 D :=
  (Submodule.mkQ (C.AD D ⊔ C.FSub)).comp (C.AD E).subtype

/-- The map `A(E) → resField p / (image of L(E))`. -/
noncomputable def resQuotMap (E : P →₀ ℤ) (p : P) :
    ↥(C.AD E) →ₗ[K] (C.resField p ⧸ LinearMap.range (C.resL E p)) :=
  (Submodule.mkQ (LinearMap.range (C.resL E p))).comp (C.resA E p)

lemma resQuotMap_surjective (E : P →₀ ℤ) (p : P) : Function.Surjective (C.resQuotMap E p) := by
  intro z
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (C.resL E p)) z
  obtain ⟨α, rfl⟩ := C.resA_surjective E p y
  exact ⟨α, rfl⟩

lemma le_add_single (D : P →₀ ℤ) (p : P) : D ≤ D + Finsupp.single p 1 := by
  intro q
  rcases eq_or_ne q p with rfl | hq
  · simp
  · simp [Finsupp.single_apply, hq]

@[simp] lemma add_single_sub_single (D : P →₀ ℤ) (p : P) :
    (D + Finsupp.single p 1) - Finsupp.single p 1 = D := by
  simp

lemma resA_diagLin (E : P →₀ ℤ) (p : P) (x : ↥(C.LSpace E)) :
    C.resA E p ⟨C.diagLin (x : F), (C.diagLin_mem_AD_iff E _).2 x.2⟩ = C.resL E p x := rfl

lemma ker_resQuotMap_eq_ker_psi (D : P →₀ ℤ) (p : P) :
    LinearMap.ker (C.resQuotMap (D + Finsupp.single p 1) p) =
      LinearMap.ker (C.psi D (D + Finsupp.single p 1)) := by
  ext α
  simp only [LinearMap.mem_ker, resQuotMap, psi, LinearMap.coe_comp, Function.comp_apply,
    Submodule.mkQ_apply, Submodule.coe_subtype]
  rw [Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨x, hx⟩
    have hβmem : C.diagLin (x : F) ∈ C.AD (D + Finsupp.single p 1) :=
      (C.diagLin_mem_AD_iff _ _).2 x.2
    have hres : C.resA (D + Finsupp.single p 1) p
        (α - ⟨C.diagLin (x : F), hβmem⟩) = 0 := by
      simp only [map_sub, C.resA_diagLin _ p x, hx, sub_self]
    rw [C.resA_eq_zero_iff] at hres
    have hmem : (α : C.Adele) - C.diagLin (x : F) ∈ C.AD D := by
      simpa using hres
    have hsplit : (α : C.Adele) = ((α : C.Adele) - C.diagLin (x : F)) + C.diagLin (x : F) :=
      (sub_add_cancel _ _).symm
    rw [hsplit]
    exact Submodule.add_mem_sup hmem ⟨(x : F), rfl⟩
  · intro h
    rw [Submodule.mem_sup] at h
    obtain ⟨a, ha, f, hf, haf⟩ := h
    obtain ⟨x, hx⟩ := hf
    subst hx
    have hamem : a ∈ C.AD (D + Finsupp.single p 1) := C.AD_mono (le_add_single D p) ha
    have hfmemE : C.diagLin x ∈ C.AD (D + Finsupp.single p 1) := by
      have hval : C.diagLin x = (α : C.Adele) - a := by rw [← haf]; abel
      rw [hval]
      exact Submodule.sub_mem _ α.2 hamem
    have hxL : x ∈ C.LSpace (D + Finsupp.single p 1) := (C.diagLin_mem_AD_iff _ x).1 hfmemE
    have hsplit : α = ⟨a, hamem⟩ + ⟨C.diagLin x, hfmemE⟩ := by
      apply Subtype.ext
      exact haf.symm
    have hzero : C.resA (D + Finsupp.single p 1) p ⟨a, hamem⟩ = 0 := by
      rw [C.resA_eq_zero_iff]
      simpa using ha
    refine ⟨⟨x, hxL⟩, ?_⟩
    rw [hsplit, map_add, hzero, zero_add]
    exact (C.resA_diagLin _ p ⟨x, hxL⟩).symm

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- `range ψ ≅ resField p / L(E)`. -/
noncomputable def rangePsiEquiv (D : P →₀ ℤ) (p : P) :
    ↥(LinearMap.range (C.psi D (D + Finsupp.single p 1))) ≃ₗ[K]
      (C.resField p ⧸ LinearMap.range (C.resL (D + Finsupp.single p 1) p)) :=
  let e1 : ↥(LinearMap.range (C.psi D (D + Finsupp.single p 1))) ≃ₗ[K]
      (↥(C.AD (D + Finsupp.single p 1)) ⧸ LinearMap.ker (C.psi D (D + Finsupp.single p 1))) :=
    (LinearMap.quotKerEquivRange (C.psi D (D + Finsupp.single p 1))).symm
  let e2 : (↥(C.AD (D + Finsupp.single p 1)) ⧸ LinearMap.ker (C.psi D (D + Finsupp.single p 1)))
      ≃ₗ[K] (↥(C.AD (D + Finsupp.single p 1)) ⧸
        LinearMap.ker (C.resQuotMap (D + Finsupp.single p 1) p)) :=
    Submodule.quotEquivOfEq _ _ (C.ker_resQuotMap_eq_ker_psi D p).symm
  let e3 : (↥(C.AD (D + Finsupp.single p 1)) ⧸ LinearMap.ker (C.resQuotMap (D + Finsupp.single p 1) p))
      ≃ₗ[K] (C.resField p ⧸ LinearMap.range (C.resL (D + Finsupp.single p 1) p)) :=
    LinearMap.quotKerEquivOfSurjective _ (C.resQuotMap_surjective (D + Finsupp.single p 1) p)
  e1.trans (e2.trans e3)

lemma map_mkQ_eq_range_psi (D : P →₀ ℤ) (p : P) :
    Submodule.map (C.AD D ⊔ C.FSub).mkQ (C.AD (D + Finsupp.single p 1) ⊔ C.FSub) =
      LinearMap.range (C.psi D (D + Finsupp.single p 1)) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    simp only [SetLike.mem_coe] at hz
    rw [Submodule.mem_sup] at hz
    obtain ⟨a, ha, f, hf, rfl⟩ := hz
    refine ⟨⟨a, ha⟩, ?_⟩
    simp only [psi, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    have hneg : a - (a + f) = -f := by abel
    rw [hneg]
    exact Submodule.neg_mem _ (Submodule.mem_sup_right hf)
  · rintro ⟨z, rfl⟩
    exact ⟨(z : C.Adele), Submodule.mem_sup_left z.2, rfl⟩

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- `H¹(D) / range ψ ≅ H¹(D + p)`. -/
noncomputable def H1QuotEquiv (D : P →₀ ℤ) (p : P) :
    (C.H1 D ⧸ LinearMap.range (C.psi D (D + Finsupp.single p 1))) ≃ₗ[K]
      C.H1 (D + Finsupp.single p 1) :=
  let e1 : (C.H1 D ⧸ LinearMap.range (C.psi D (D + Finsupp.single p 1))) ≃ₗ[K]
      (C.H1 D ⧸ Submodule.map (C.AD D ⊔ C.FSub).mkQ
        (C.AD (D + Finsupp.single p 1) ⊔ C.FSub)) :=
    Submodule.quotEquivOfEq _ _ (C.map_mkQ_eq_range_psi D p).symm
  e1.trans (Submodule.quotientQuotientEquivQuotient _ _
    (sup_le_sup_right (C.AD_mono (le_add_single D p)) _))

end PreCurve

end Math2

/-
Basic properties of the adele spaces `A(D)`.
-/
import RequestProject.Math2.Ell

namespace Math2

open Module Submodule

namespace PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]
variable (C : PreCurve K F P)

lemma AD_mono {D E : P →₀ ℤ} (h : D ≤ E) : C.AD D ≤ C.AD E := by
  intro α hα p
  refine le_trans ?_ (hα p)
  exact_mod_cast neg_le_neg (h p)

/-- The `p`-th component of an adele. -/
def compLin (p : P) : C.Adele →ₗ[K] F where
  toFun α := α.val p
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] lemma compLin_apply (p : P) (α : C.Adele) : C.compLin p α = α.val p := rfl

/-- The residue map on `A(E)` at a place `p`. -/
noncomputable def resA (E : P →₀ ℤ) (p : P) : ↥(C.AD E) →ₗ[K] C.resField p :=
  C.resMap p (E p) (((C.compLin p).comp (C.AD E).subtype : ↥(C.AD E) →ₗ[K] F))
    (fun v : ↥(C.AD E) => v.2 p)

lemma resA_eq_zero_iff (E : P →₀ ℤ) (p : P) (α : ↥(C.AD E)) :
    C.resA E p α = 0 ↔ (α : C.Adele) ∈ C.AD (E - Finsupp.single p 1) := by
  rw [resA, C.resMap_eq_zero_iff]
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, compLin_apply]
  constructor
  · intro h q
    rcases eq_or_ne q p with rfl | hq
    · simpa using h
    · have := α.2 q
      simpa [Finsupp.single_apply, hq] using this
  · intro h
    have := h p
    simpa using this

open Classical in
/-- The adele which is `y` at `p` and zero elsewhere. -/
noncomputable def spike (p : P) (y : F) : C.Adele :=
  Adele.mk C (fun q => if q = p then y else 0) ⟨{p}, fun q hq => by
      have hne : q ≠ p := by simpa using hq
      simp [hne]⟩

open Classical in
lemma spike_val (p : P) (y : F) :
    (C.spike p y).val = fun q => if q = p then y else 0 := rfl

@[simp] lemma spike_val_self (p : P) (y : F) : (C.spike p y).val p = y := by
  rw [spike_val]
  simp

lemma spike_val_ne {p q : P} (h : q ≠ p) (y : F) : (C.spike p y).val q = 0 := by
  rw [spike_val]
  simp [h]

lemma spike_mem_AD (E : P →₀ ℤ) (p : P) (y : F)
    (hy : ((-(E p) : ℤ) : Zt) ≤ C.ord p y) : C.spike p y ∈ C.AD E := by
  intro q
  rcases eq_or_ne q p with rfl | hq
  · simpa using hy
  · rw [C.spike_val_ne hq]
    simp

lemma resA_surjective (E : P →₀ ℤ) (p : P) : Function.Surjective (C.resA E p) := by
  refine C.resMap_surjective _ _ _ _ ?_
  intro y hy
  have hmem : C.spike p (C.unif p ^ (-(E p)) * y) ∈ C.AD E := by
    refine C.spike_mem_AD E p _ ?_
    have := C.ord_shift_ge p (-(E p)) 0 y hy
    simpa using this
  exact ⟨⟨_, hmem⟩, by simp⟩

@[simp] lemma diagLin_val (x : F) : (C.diagLin x).val = fun _ : P => x := rfl

lemma diagLin_mem_AD_iff (D : P →₀ ℤ) (x : F) :
    C.diagLin x ∈ C.AD D ↔ x ∈ C.LSpace D := Iff.rfl

lemma diagLin_injective : Function.Injective C.diagLin := by
  intro x y h
  have h2 := congrArg Adele.val h
  obtain ⟨p⟩ := C.place_nonempty
  simpa using congrFun h2 p

/-- Every adele lies in `A(D)` for some divisor `D`. -/
lemma exists_mem_AD (α : C.Adele) (D₀ : P →₀ ℤ) : ∃ D : P →₀ ℤ, D₀ ≤ D ∧ α ∈ C.AD D := by
  classical
  obtain ⟨S, hS⟩ := α.val_mem
  set f : P → ℤ := fun p => max (D₀ p) (max 0 (- C.ordZ p (α.val p))) with hf
  have hordnn : ∀ p ∉ S, 0 ≤ C.ordZ p (α.val p) := by
    intro p hpS
    rcases eq_or_ne (α.val p) 0 with h0 | h0
    · simp [ordZ, h0]
    · have h := hS p hpS
      rw [C.ord_eq_ordZ h0] at h
      exact_mod_cast h
  have hsupp : ∀ p ∉ (S ∪ D₀.support), f p = 0 := by
    intro p hp
    simp only [Finset.mem_union, not_or] at hp
    obtain ⟨hpS, hpD⟩ := hp
    have h1 : D₀ p = 0 := by simpa using hpD
    have h2 := hordnn p hpS
    simp only [hf, h1]
    omega
  refine ⟨Finsupp.onFinset (S ∪ D₀.support) f
    (fun p hp => by by_contra h; exact hp (hsupp p h)), ?_, ?_⟩
  · intro p
    simp only [Finsupp.onFinset_apply, hf]
    exact le_max_left _ _
  · intro p
    rcases eq_or_ne (α.val p) 0 with h0 | h0
    · simp [h0]
    · rw [C.ord_eq_ordZ h0]
      have hfp : - (f p) ≤ C.ordZ p (α.val p) := by
        simp only [hf]
        omega
      have hle : -((Finsupp.onFinset (S ∪ D₀.support) f
          (fun p hp => by by_contra h; exact hp (hsupp p h))) p) ≤ C.ordZ p (α.val p) := by
        simpa [Finsupp.onFinset_apply] using hfp
      exact_mod_cast hle

end PreCurve

end Math2

/-
The Euler characteristic `ell - i` and its behaviour under adding a place.
-/
import RequestProject.Math2.Step

namespace Math2

open Module Submodule

namespace PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]
variable (C : PreCurve K F P)

/-- The dimension of the first cohomology group of a divisor. -/
noncomputable def iH (D : P →₀ ℤ) : ℕ := finrank K (C.H1 D)

end PreCurve

namespace PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]
variable {C : PreCurve K F P}

lemma IsCurve.finrank_range_resL (hC : C.IsCurve) (E : P →₀ ℤ) (p : P) :
    finrank K (LinearMap.range (C.resL E p)) + C.ell (E - Finsupp.single p 1) = C.ell E := by
  haveI := hC.finiteDimensional_LSpace E
  have h := LinearMap.finrank_range_add_finrank_ker (C.resL E p)
  rw [C.ker_resL E p] at h
  have hker : finrank K ((C.LSpace (E - Finsupp.single p 1)).comap (C.LSpace E).subtype)
      = C.ell (E - Finsupp.single p 1) :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (C.LSpace_sub_single_le E p))
  rw [hker] at h
  exact h

lemma IsCurve.finrank_resField_quot (hC : C.IsCurve) (E : P →₀ ℤ) (p : P) :
    finrank K (C.resField p ⧸ LinearMap.range (C.resL E p)) +
      finrank K (LinearMap.range (C.resL E p)) = C.deg p := by
  haveI := hC.residue_finite p
  rw [Submodule.finrank_quotient_add_finrank, hC.residue_finrank p]

/-- The image of `A(D + p)` in `H¹(D)` is finite dimensional. -/
lemma IsCurve.finiteDimensional_rangePsi (hC : C.IsCurve) (D : P →₀ ℤ) (p : P) :
    FiniteDimensional K (LinearMap.range (C.psi D (D + Finsupp.single p 1))) := by
  haveI := hC.residue_finite p
  exact Module.Finite.equiv (C.rangePsiEquiv D p).symm

lemma IsCurve.H1_finite_add (hC : C.IsCurve) (D : P →₀ ℤ) (p : P)
    (h : Module.Finite K (C.H1 D)) : Module.Finite K (C.H1 (D + Finsupp.single p 1)) :=
  Module.Finite.equiv (C.H1QuotEquiv D p)

lemma IsCurve.H1_finite_of_add (hC : C.IsCurve) (D : P →₀ ℤ) (p : P)
    (h : Module.Finite K (C.H1 (D + Finsupp.single p 1))) : Module.Finite K (C.H1 D) := by
  haveI := hC.finiteDimensional_rangePsi D p
  haveI : Module.Finite K (C.H1 D ⧸ LinearMap.range (C.psi D (D + Finsupp.single p 1))) :=
    Module.Finite.equiv (C.H1QuotEquiv D p).symm
  exact Module.Finite.of_submodule_quotient
    (LinearMap.range (C.psi D (D + Finsupp.single p 1)))

lemma IsCurve.finrank_H1_add (hC : C.IsCurve) (D : P →₀ ℤ) (p : P)
    (h : Module.Finite K (C.H1 D)) :
    C.iH (D + Finsupp.single p 1) +
      finrank K (LinearMap.range (C.psi D (D + Finsupp.single p 1))) = C.iH D := by
  have h1 := Submodule.finrank_quotient_add_finrank
    (R := K) (LinearMap.range (C.psi D (D + Finsupp.single p 1)))
  rw [LinearEquiv.finrank_eq (C.H1QuotEquiv D p)] at h1
  exact h1

/-- The key step: the Euler characteristic `ell - i` increases by `deg p` when adding `p`. -/
lemma IsCurve.chi_step (hC : C.IsCurve) (D : P →₀ ℤ) (p : P) (h : Module.Finite K (C.H1 D)) :
    (C.ell (D + Finsupp.single p 1) : ℤ) - C.iH (D + Finsupp.single p 1)
      = (C.ell D : ℤ) - C.iH D + C.deg p := by
  haveI := hC.residue_finite p
  have h1 := hC.finrank_H1_add D p h
  have h2 : finrank K (LinearMap.range (C.psi D (D + Finsupp.single p 1))) =
      finrank K (C.resField p ⧸ LinearMap.range (C.resL (D + Finsupp.single p 1) p)) :=
    LinearEquiv.finrank_eq (C.rangePsiEquiv D p)
  have h3 := hC.finrank_resField_quot (D + Finsupp.single p 1) p
  have h4 := hC.finrank_range_resL (D + Finsupp.single p 1) p
  rw [add_single_sub_single D p] at h4
  rw [h2] at h1
  omega

end PreCurve

end Math2

/-
The residue fields of the projective line.
-/
import RequestProject.P1.Curve

namespace Math2

namespace P1

open Polynomial RatFunc Module Submodule

universe u

variable {K : Type u} [Field K]

lemma ordP_eq (p : Place K) : (projectiveLine K).ord p = ordP p := rfl

lemma mem_valSub_iff' (p : Place K) (n : ℤ) (x : RatFunc K) :
    x ∈ (projectiveLine K).valSub p n ↔ (x = 0 ∨ n ≤ ordZP p x) := by
  rw [PreCurve.mem_valSub_iff, ordP_eq]
  constructor
  · intro h
    rcases eq_or_ne x 0 with rfl | hx
    · exact Or.inl rfl
    · rw [ordP_of_ne_zero p hx] at h
      exact Or.inr (by exact_mod_cast h)
  · rintro (rfl | h)
    · simp
    · rcases eq_or_ne x 0 with rfl | hx
      · simp
      · rw [ordP_of_ne_zero p hx]
        exact_mod_cast h

lemma mem_maxIdeal_iff (p : Place K) (x : ↥((projectiveLine K).valSub p 0)) :
    x ∈ (projectiveLine K).maxIdeal p ↔ ((x : RatFunc K) = 0 ∨ 1 ≤ ordZP p (x : RatFunc K)) := by
  rw [PreCurve.maxIdeal, Submodule.mem_comap, Submodule.coe_subtype, mem_valSub_iff']

/-! ### The residue field at a finite place -/

variable (q : FinPlace K)

lemma algebraMap_mem_valSub_zero (a : K[X]) :
    algebraMap K[X] (RatFunc K) a ∈ (projectiveLine K).valSub (some q) 0 := by
  rw [mem_valSub_iff']
  rcases eq_or_ne a 0 with rfl | ha
  · exact Or.inl (by simp)
  · exact Or.inr (by simp [ordZP, ordFinZ_algebraMap])

/-- Polynomials, as elements of the local ring at a finite place. -/
noncomputable def polyToLocal : K[X] →ₗ[K] ↥((projectiveLine K).valSub (some q) 0) :=
  LinearMap.codRestrict _ (IsScalarTower.toAlgHom K K[X] (RatFunc K)).toLinearMap
    (algebraMap_mem_valSub_zero q)

@[simp] lemma polyToLocal_coe (a : K[X]) :
    ((polyToLocal q a : ↥((projectiveLine K).valSub (some q) 0)) : RatFunc K)
      = algebraMap K[X] (RatFunc K) a := rfl

/-- The reduction map from polynomials to the residue field at a finite place. -/
noncomputable def polyToRes : K[X] →ₗ[K] (projectiveLine K).resField (some q) :=
  ((projectiveLine K).maxIdeal (some q)).mkQ ∘ₗ polyToLocal q

lemma polyToRes_eq_zero_iff (a : K[X]) : polyToRes q a = 0 ↔ q.poly ∣ a := by
  rw [polyToRes, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    mem_maxIdeal_iff]
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have hne : algebraMap K[X] (RatFunc K) a ≠ 0 := fun hh =>
      ha (RatFunc.algebraMap_injective K (hh.trans (map_zero _).symm))
    rw [polyToLocal_coe]
    constructor
    · rintro (h | h)
      · exact absurd h hne
      · simp only [ordZP, ordFinZ_algebraMap] at h
        exact dvd_of_cnt_ne_zero q (by omega)
    · intro hdvd
      refine Or.inr ?_
      simp only [ordZP, ordFinZ_algebraMap]
      have : cnt q a ≠ 0 := fun hc => (cnt_eq_zero_iff q a).1 hc hdvd
      omega

lemma polyToRes_surjective : Function.Surjective (polyToRes q) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective ((projectiveLine K).maxIdeal (some q)) y
  obtain ⟨x, hx⟩ := x
  rcases eq_or_ne x 0 with rfl | hx0
  · refine ⟨0, ?_⟩
    rw [polyToRes, LinearMap.comp_apply, map_zero]
    rfl
  · have hord : 0 ≤ ordZP (some q) x := by
      rcases (mem_valSub_iff' (some q) 0 x).1 hx with h | h
      · exact absurd h hx0
      · exact h
    have hordfin : (cnt q x.denom : ℤ) ≤ cnt q x.num := by
      simpa [ordZP, ordFinZ] using hord
    have hqden : ¬ q.poly ∣ x.denom := by
      intro hdvd
      have hcd : cnt q x.denom ≠ 0 := fun hc => (cnt_eq_zero_iff q x.denom).1 hc hdvd
      have hcn : cnt q x.num ≠ 0 := by omega
      obtain ⟨u, v, huv⟩ := RatFunc.isCoprime_num_denom x
      have hone : q.poly ∣ (1 : K[X]) := by
        rw [← huv]
        exact dvd_add (Dvd.dvd.mul_left (dvd_of_cnt_ne_zero q hcn) u)
          (Dvd.dvd.mul_left hdvd v)
      exact q.not_isUnit (isUnit_of_dvd_one hone)
    obtain ⟨u, v, huv⟩ := (q.irred.coprime_iff_not_dvd).2 hqden
    refine ⟨x.num * v, ?_⟩
    -- the difference `algebraMap (num * v) - x` lies in the maximal ideal
    have hdenne : algebraMap K[X] (RatFunc K) x.denom ≠ 0 := fun hh =>
      (RatFunc.denom_ne_zero x) (RatFunc.algebraMap_injective K (hh.trans (map_zero _).symm))
    have hkey : algebraMap K[X] (RatFunc K) (x.num * v) - x
        = algebraMap K[X] (RatFunc K) (x.num * (-(u * q.poly)))
          / algebraMap K[X] (RatFunc K) x.denom := by
      have hxd : algebraMap K[X] (RatFunc K) x.num
          = x * algebraMap K[X] (RatFunc K) x.denom :=
        (div_eq_iff hdenne).1 (RatFunc.num_div_denom x)
      have huvA : algebraMap K[X] (RatFunc K) u * algebraMap K[X] (RatFunc K) q.poly
          + algebraMap K[X] (RatFunc K) v * algebraMap K[X] (RatFunc K) x.denom = 1 := by
        rw [← map_mul, ← map_mul, ← map_add, huv, map_one]
      rw [eq_div_iff hdenne]
      simp only [map_mul, map_neg]
      linear_combination hxd + algebraMap K[X] (RatFunc K) x.num * huvA
    rw [polyToRes, LinearMap.comp_apply]
    simp only [Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq, mem_maxIdeal_iff]
    have hcoe : ((polyToLocal q (x.num * v) - ⟨x, hx⟩ :
        ↥((projectiveLine K).valSub (some q) 0)) : RatFunc K)
        = algebraMap K[X] (RatFunc K) (x.num * v) - x := rfl
    rw [hcoe, hkey]
    rcases eq_or_ne (x.num * (-(u * q.poly))) 0 with h0 | h0
    · left
      rw [h0]
      simp
    · right
      rw [ordZP, ordFinZ_div q h0 (RatFunc.denom_ne_zero x)]
      have hnum : x.num ≠ 0 := RatFunc.num_ne_zero hx0
      have huq : (-(u * q.poly)) ≠ 0 := by
        intro h
        exact h0 (by rw [h, mul_zero])
      have hu : u ≠ 0 := by
        intro h
        apply huq
        rw [h, zero_mul, neg_zero]
      rw [cnt_mul q hnum huq]
      have hcq : cnt q (-(u * q.poly)) = cnt q u + 1 := by
        rw [show (-(u * q.poly)) = (-u) * q.poly by ring,
          cnt_mul q (neg_ne_zero.2 hu) q.ne_zero, cnt_self]
        congr 1
        rcases eq_or_ne u 0 with rfl | hu' 
        · simp
        · have h1 : cnt q (-u) = cnt q u := by
            have : (-u : K[X]) = (-1 : K[X]) * u := by ring
            rw [this, cnt_mul q (by simp) hu, cnt_of_isUnit q (isUnit_one.neg)]
            simp
          exact h1
      rw [hcq]
      omega

/-- The residue field at a finite place has dimension the degree of the place. -/
lemma finrank_resField_some :
    finrank K ((projectiveLine K).resField (some q)) = q.poly.natDegree := by
  classical
  set n := q.poly.natDegree with hn
  have hmonic := q.monic
  -- the restriction of `polyToRes` to polynomials of degree `< n` is bijective
  set f : ↥(Polynomial.degreeLT K n) →ₗ[K] (projectiveLine K).resField (some q) :=
    (polyToRes q).comp (Polynomial.degreeLT K n).subtype with hf
  have hinj : Function.Injective f := by
    intro a b hab
    have h0 : polyToRes q ((a : K[X]) - b) = 0 := by
      rw [map_sub]
      simpa [hf] using sub_eq_zero.2 hab
    have hdvd : q.poly ∣ ((a : K[X]) - b) := (polyToRes_eq_zero_iff q _).1 h0
    have hdeg : ((a : K[X]) - b).degree < q.poly.degree := by
      have ha := a.2
      have hb := b.2
      rw [Polynomial.mem_degreeLT] at ha hb
      have := lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ha hb)
      rwa [Polynomial.degree_eq_natDegree q.ne_zero, ← hn]
    have : (a : K[X]) - b = 0 := by
      by_contra hne
      exact absurd (Polynomial.degree_le_of_dvd hdvd hne) (not_le.2 hdeg)
    exact Subtype.ext (sub_eq_zero.1 this)
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := polyToRes_surjective q y
    refine ⟨⟨a %ₘ q.poly, ?_⟩, ?_⟩
    · rw [Polynomial.mem_degreeLT]
      have := Polynomial.degree_modByMonic_lt a hmonic
      rwa [Polynomial.degree_eq_natDegree q.ne_zero] at this
    · have hsub : a - a %ₘ q.poly = q.poly * (a /ₘ q.poly) := by
        have := Polynomial.modByMonic_add_div a hmonic
        linear_combination -this
      have : polyToRes q (a - a %ₘ q.poly) = 0 := by
        rw [polyToRes_eq_zero_iff, hsub]
        exact Dvd.intro _ rfl
      rw [map_sub, sub_eq_zero] at this
      simpa [hf] using this.symm
  have hiso := (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq
  rw [← hiso, (Polynomial.degreeLTEquiv K n).finrank_eq, Module.finrank_pi]
  simp

/-! ### The residue field at infinity -/

lemma C_mem_valSub_zero (c : K) :
    (RatFunc.C c : RatFunc K) ∈ (projectiveLine K).valSub (none : Place K) 0 := by
  rw [mem_valSub_iff']
  rcases eq_or_ne c 0 with rfl | hc
  · exact Or.inl (by simp)
  · refine Or.inr ?_
    simp [ordZP, ordInfZ]

/-- Constants, as elements of the local ring at infinity. -/
noncomputable def constToLocal : K →ₗ[K] ↥((projectiveLine K).valSub (none : Place K) 0) :=
  LinearMap.codRestrict _ (Algebra.linearMap K (RatFunc K)) (by
    intro c
    simpa [RatFunc.algebraMap_eq_C] using C_mem_valSub_zero c)

/-- The reduction map from constants to the residue field at infinity. -/
noncomputable def constToRes : K →ₗ[K] (projectiveLine K).resField (none : Place K) :=
  ((projectiveLine K).maxIdeal (none : Place K)).mkQ ∘ₗ constToLocal

lemma finrank_resField_none :
    finrank K ((projectiveLine K).resField (none : Place K)) = 1 := by
  have hinj : Function.Injective (constToRes (K := K)) := by
    intro c d hcd
    by_contra hne
    have hsub : c - d ≠ 0 := sub_ne_zero.2 hne
    have h0 : constToRes (c - d) = 0 := by
      rw [map_sub, hcd, sub_self]
    rw [constToRes, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, mem_maxIdeal_iff] at h0
    have hcoe : ((constToLocal (c - d) : ↥((projectiveLine K).valSub (none : Place K) 0)) :
        RatFunc K) = algebraMap K (RatFunc K) (c - d) := rfl
    rw [hcoe] at h0
    have hinj0 : Function.Injective (algebraMap K (RatFunc K)) :=
      (algebraMap K (RatFunc K)).injective
    have hne0 : algebraMap K (RatFunc K) (c - d) ≠ 0 := fun hh =>
      hsub (hinj0 (hh.trans (map_zero _).symm))
    rcases h0 with h | h
    · exact hne0 h
    · rw [RatFunc.algebraMap_eq_C] at h
      simp only [ordZP, ordInfZ, RatFunc.intDegree_C] at h
      omega
  have hsurj : Function.Surjective (constToRes (K := K)) := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective ((projectiveLine K).maxIdeal (none : Place K)) y
    obtain ⟨x, hx⟩ := x
    rcases eq_or_ne x 0 with rfl | hx0
    · refine ⟨0, ?_⟩
      rw [constToRes, LinearMap.comp_apply, map_zero]
      rfl
    · have hord : (0 : ℤ) ≤ ordZP (none : Place K) x := by
        rcases (mem_valSub_iff' (none : Place K) 0 x).1 hx with h | h
        · exact absurd h hx0
        · exact h
      have hdeg : x.num.natDegree ≤ x.denom.natDegree := by
        simp only [ordZP, ordInfZ, RatFunc.intDegree] at hord
        omega
      have hnum : x.num ≠ 0 := RatFunc.num_ne_zero hx0
      have hden : x.denom ≠ 0 := RatFunc.denom_ne_zero x
      have hdenne : algebraMap K[X] (RatFunc K) x.denom ≠ 0 := fun hh =>
        hden (RatFunc.algebraMap_injective K (hh.trans (map_zero _).symm))
      have key : ∀ c : K, (algebraMap K (RatFunc K) c - x = 0 ∨
          1 ≤ ordZP (none : Place K) (algebraMap K (RatFunc K) c - x)) →
          constToRes c = Submodule.Quotient.mk ⟨x, hx⟩ := by
        intro c hc
        rw [constToRes, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
          mem_maxIdeal_iff]
        have hcoe : ((constToLocal c - ⟨x, hx⟩ :
            ↥((projectiveLine K).valSub (none : Place K) 0)) : RatFunc K)
            = algebraMap K (RatFunc K) c - x := rfl
        rw [hcoe]
        exact hc
      rcases lt_or_eq_of_le hdeg with hlt | heq
      · refine ⟨0, key 0 (Or.inr ?_)⟩
        rw [map_zero, zero_sub]
        have hnegd : ordZP (none : Place K) (-x) = ordZP (none : Place K) x := by
          simp only [ordZP, ordInfZ, RatFunc.intDegree_neg]
        rw [hnegd]
        simp only [ordZP, ordInfZ, RatFunc.intDegree]
        omega
      · set c : K := x.num.leadingCoeff / x.denom.leadingCoeff with hc
        have hlcd : x.denom.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hden
        have hlcn : x.num.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hnum
        have hcne : c ≠ 0 := div_ne_zero hlcn hlcd
        set w : K[X] := Polynomial.C c * x.denom - x.num with hw
        have hxeq : algebraMap K (RatFunc K) c - x
            = algebraMap K[X] (RatFunc K) w / algebraMap K[X] (RatFunc K) x.denom := by
          have hxd : algebraMap K[X] (RatFunc K) x.num
              = x * algebraMap K[X] (RatFunc K) x.denom :=
            (div_eq_iff hdenne).1 (RatFunc.num_div_denom x)
          have hCc : algebraMap K[X] (RatFunc K) (Polynomial.C c)
              = algebraMap K (RatFunc K) c := by
            rw [RatFunc.algebraMap_eq_C, RatFunc.algebraMap_C]
          rw [eq_div_iff hdenne, hw, map_sub, map_mul, hCc]
          linear_combination hxd
        refine ⟨c, key c ?_⟩
        rcases eq_or_ne w 0 with hw0 | hw0
        · left
          rw [hxeq, hw0]
          simp
        · right
          have hdd : (Polynomial.C c * x.denom).degree = x.num.degree := by
            rw [Polynomial.degree_C_mul hcne, Polynomial.degree_eq_natDegree hden,
              Polynomial.degree_eq_natDegree hnum, heq]
          have hlc : (Polynomial.C c * x.denom).leadingCoeff = x.num.leadingCoeff := by
            rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc]
            field_simp
          have hdegw : w.degree < x.num.degree := by
            rw [hw, ← hdd]
            exact Polynomial.degree_sub_lt hdd (mul_ne_zero (by simpa using hcne) hden) hlc
          have hdegw' : w.natDegree < x.num.natDegree := by
            have h1 : w.degree = (w.natDegree : WithBot ℕ) :=
              Polynomial.degree_eq_natDegree hw0
            have h2 : x.num.degree = (x.num.natDegree : WithBot ℕ) :=
              Polynomial.degree_eq_natDegree hnum
            rw [h1, h2] at hdegw
            exact_mod_cast hdegw
          have hwne : algebraMap K[X] (RatFunc K) w ≠ 0 := fun hh =>
            hw0 (RatFunc.algebraMap_injective K (hh.trans (map_zero _).symm))
          rw [hxeq]
          simp only [ordZP, ordInfZ, div_eq_mul_inv,
            RatFunc.intDegree_mul hwne (inv_ne_zero hdenne), RatFunc.intDegree_inv,
            RatFunc.intDegree_polynomial]
          omega
  have hiso := (LinearEquiv.ofBijective (constToRes (K := K)) ⟨hinj, hsurj⟩).finrank_eq
  rw [← hiso]
  simp

end P1

end Math2

/-
Multiplicities of monic irreducible polynomials: the local invariants of the projective line.
-/
import Mathlib

namespace Math2

namespace P1

open Polynomial

universe u

variable {K : Type u} [Field K]

/-- A finite place of the projective line over `K`: a monic irreducible polynomial. -/
structure FinPlace (K : Type u) [Field K] where
  /-- The monic irreducible polynomial defining the place. -/
  poly : K[X]
  /-- The polynomial is monic. -/
  monic : poly.Monic
  /-- The polynomial is irreducible. -/
  irred : Irreducible poly

namespace FinPlace

lemma ne_zero (q : FinPlace K) : q.poly ≠ 0 := q.monic.ne_zero

lemma not_isUnit (q : FinPlace K) : ¬ IsUnit q.poly := q.irred.not_isUnit

lemma prime (q : FinPlace K) : Prime q.poly := q.irred.prime

lemma natDegree_pos (q : FinPlace K) : 0 < q.poly.natDegree := by
  rcases Nat.eq_zero_or_pos q.poly.natDegree with h | h
  · exact absurd (q.monic.natDegree_eq_zero.1 h ▸ isUnit_one) q.not_isUnit
  · exact h

lemma ext' {q r : FinPlace K} (h : q.poly = r.poly) : q = r := by
  cases q; cases r; simpa using h

end FinPlace

/-- The multiplicity of the place `q` in the polynomial `a`. -/
noncomputable def cnt (q : FinPlace K) (a : K[X]) : ℕ := multiplicity q.poly a

lemma finiteMultiplicity_poly (q : FinPlace K) {a : K[X]} (ha : a ≠ 0) :
    FiniteMultiplicity q.poly a :=
  FiniteMultiplicity.of_not_isUnit q.not_isUnit ha

lemma pow_cnt_dvd (q : FinPlace K) (a : K[X]) : q.poly ^ cnt q a ∣ a :=
  pow_multiplicity_dvd q.poly a

lemma pow_dvd_iff_le_cnt (q : FinPlace K) {a : K[X]} (ha : a ≠ 0) (n : ℕ) :
    q.poly ^ n ∣ a ↔ n ≤ cnt q a :=
  (finiteMultiplicity_poly q ha).pow_dvd_iff_le_multiplicity

lemma cnt_mul (q : FinPlace K) {a b : K[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    cnt q (a * b) = cnt q a + cnt q b :=
  multiplicity_mul q.prime (finiteMultiplicity_poly q (mul_ne_zero ha hb))

lemma cnt_eq_zero_iff (q : FinPlace K) (a : K[X]) : cnt q a = 0 ↔ ¬ q.poly ∣ a :=
  multiplicity_eq_zero

lemma cnt_eq_zero_of_not_dvd (q : FinPlace K) {a : K[X]} (h : ¬ q.poly ∣ a) : cnt q a = 0 :=
  (cnt_eq_zero_iff q a).2 h

lemma dvd_of_cnt_ne_zero (q : FinPlace K) {a : K[X]} (h : cnt q a ≠ 0) : q.poly ∣ a := by
  by_contra hd
  exact h (cnt_eq_zero_of_not_dvd q hd)

lemma cnt_self (q : FinPlace K) : cnt q q.poly = 1 := multiplicity_self

lemma cnt_of_isUnit (q : FinPlace K) {a : K[X]} (ha : IsUnit a) : cnt q a = 0 :=
  cnt_eq_zero_of_not_dvd q (fun h => q.not_isUnit (isUnit_of_dvd_unit h ha))

lemma cnt_one (q : FinPlace K) : cnt q 1 = 0 := cnt_of_isUnit q isUnit_one

lemma cnt_C (q : FinPlace K) {c : K} (hc : c ≠ 0) : cnt q (C c) = 0 :=
  cnt_of_isUnit q (isUnit_C.2 hc.isUnit)

lemma cnt_other (q r : FinPlace K) (h : q ≠ r) : cnt q r.poly = 0 := by
  refine cnt_eq_zero_of_not_dvd q fun hd => h (FinPlace.ext' ?_)
  exact Polynomial.eq_of_monic_of_associated q.monic r.monic
    (q.irred.associated_of_dvd r.irred hd)

lemma cnt_pow_self (q : FinPlace K) (n : ℕ) : cnt q (q.poly ^ n) = n := by
  induction n with
  | zero => simpa using cnt_one q
  | succ n ih =>
      rw [pow_succ, cnt_mul q (pow_ne_zero n q.ne_zero) q.ne_zero, ih, cnt_self]

/-- The `q`-free part of a nonzero polynomial. -/
lemma exists_cnt_factor (q : FinPlace K) {a : K[X]} (ha : a ≠ 0) :
    ∃ b : K[X], a = q.poly ^ cnt q a * b ∧ ¬ q.poly ∣ b := by
  obtain ⟨b, hb⟩ := pow_cnt_dvd q a
  refine ⟨b, hb, fun hdvd => ?_⟩
  obtain ⟨c, hc⟩ := hdvd
  have hdvd2 : q.poly ^ (cnt q a + 1) ∣ a := by
    refine ⟨c, ?_⟩
    conv_lhs => rw [hb, hc]
    ring
  have := (pow_dvd_iff_le_cnt q ha (cnt q a + 1)).1 hdvd2
  omega

/-- Two nonzero polynomials with the same multiplicity data: only finitely many places
divide a given nonzero polynomial. -/
lemma exists_finset_cnt (a : K[X]) (ha : a ≠ 0) :
    ∃ S : Finset (FinPlace K), ∀ q : FinPlace K, q ∉ S → cnt q a = 0 := by
  classical
  refine UniqueFactorizationMonoid.induction_on_prime
    (P := fun a : K[X] => a ≠ 0 → ∃ S : Finset (FinPlace K), ∀ q : FinPlace K, q ∉ S → cnt q a = 0)
    a (fun h => absurd rfl h) (fun u hu _ => ⟨∅, fun q _ => cnt_of_isUnit q hu⟩) ?_ ha
  intro b p hb hp ih _
  obtain ⟨S, hS⟩ := ih hb
  have hpne : p ≠ 0 := hp.ne_zero
  have hunit : IsUnit (C (p.leadingCoeff⁻¹) : K[X]) :=
    isUnit_C.2 (Ne.isUnit (inv_ne_zero (leadingCoeff_ne_zero.2 hpne)))
  have hassoc0 : Associated p (p * C (p.leadingCoeff⁻¹)) :=
    (associated_mul_isUnit_right_iff hunit).2 (Associated.refl p)
  refine ⟨insert ⟨p * C (p.leadingCoeff⁻¹), monic_mul_leadingCoeff_inv hpne,
    hassoc0.irreducible hp.irreducible⟩ S, ?_⟩
  intro q hq
  have hqS : q ∉ S := fun h => hq (Finset.mem_insert_of_mem h)
  have hqp : q.poly ≠ p * C (p.leadingCoeff⁻¹) := fun h =>
    hq (by rw [Finset.mem_insert]; exact Or.inl (FinPlace.ext' h))
  rw [cnt_mul q hpne hb, hS q hqS, add_zero]
  refine cnt_eq_zero_of_not_dvd q fun hdvd => hqp ?_
  have hassoc : Associated q.poly p := q.irred.associated_of_dvd hp.irreducible hdvd
  exact Polynomial.eq_of_monic_of_associated q.monic (monic_mul_leadingCoeff_inv hpne)
    (hassoc.trans hassoc0)

end P1

end Math2

/-
Strong approximation for the projective line: every adele is congruent, modulo the
everywhere-integral adeles, to a (diagonal) rational function.  Equivalently
`A(0) + F = A`, so that `H¹(0) = 0`.
-/
import RequestProject.P1.Residue

namespace Math2

namespace P1

open Polynomial RatFunc Module Submodule

universe u

variable {K : Type u} [Field K]

lemma cnt_pow_other (q r : FinPlace K) (h : r ≠ q) (n : ℕ) : cnt r (q.poly ^ n) = 0 := by
  refine cnt_eq_zero_of_not_dvd r ?_
  intro hdvd
  exact (cnt_eq_zero_iff r q.poly).1 (cnt_other r q h) (r.prime.dvd_of_dvd_pow hdvd)

/-- Local approximation at a finite place: any rational function can be approximated at `q`
by one which is integral at every other finite place. -/
lemma exists_local_approx (q : FinPlace K) (x : RatFunc K) :
    ∃ y : RatFunc K, x - y ∈ (projectiveLine K).valSub (some q) 0 ∧
      ∀ r : FinPlace K, r ≠ q → y ∈ (projectiveLine K).valSub (some r) 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simpa using Submodule.zero_mem _, fun r _ => Submodule.zero_mem _⟩
  set N := x.num with hN
  set D := x.denom with hD
  have hden : D ≠ 0 := RatFunc.denom_ne_zero x
  have hnum : N ≠ 0 := RatFunc.num_ne_zero hx0
  set n := cnt q D with hn
  obtain ⟨b, hb, hqb⟩ := exists_cnt_factor q hden
  have hbne : b ≠ 0 := by
    intro h
    exact hden (by rw [hb, h, mul_zero])
  have hcop : IsCoprime (q.poly ^ n) b := ((q.irred.coprime_iff_not_dvd).2 hqb).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have hqn : q.poly ^ n ≠ 0 := pow_ne_zero _ q.ne_zero
  have hmapne : ∀ a : K[X], a ≠ 0 → algebraMap K[X] (RatFunc K) a ≠ 0 := fun a ha hh =>
    ha (RatFunc.algebraMap_injective K (hh.trans (map_zero _).symm))
  have hQn := hmapne _ hqn
  have hB := hmapne _ hbne
  have hDne := hmapne _ hden
  have hxd : algebraMap K[X] (RatFunc K) N = x * algebraMap K[X] (RatFunc K) D :=
    (div_eq_iff hDne).1 (RatFunc.num_div_denom x)
  have hDsplit : algebraMap K[X] (RatFunc K) D
      = algebraMap K[X] (RatFunc K) (q.poly ^ n) * algebraMap K[X] (RatFunc K) b := by
    rw [← map_mul, ← hb]
  have huvA : algebraMap K[X] (RatFunc K) u * algebraMap K[X] (RatFunc K) (q.poly ^ n)
      + algebraMap K[X] (RatFunc K) v * algebraMap K[X] (RatFunc K) b = 1 := by
    rw [← map_mul, ← map_mul, ← map_add, huv, map_one]
  refine ⟨algebraMap K[X] (RatFunc K) (N * v) / algebraMap K[X] (RatFunc K) (q.poly ^ n), ?_, ?_⟩
  · have hkey : x - algebraMap K[X] (RatFunc K) (N * v) / algebraMap K[X] (RatFunc K) (q.poly ^ n)
        = algebraMap K[X] (RatFunc K) (N * u) / algebraMap K[X] (RatFunc K) b := by
      rw [div_eq_div_iff hQn hB] at *
      field_simp
      rw [hDsplit] at hxd
      simp only [map_mul]
      linear_combination (algebraMap K[X] (RatFunc K) b) * hxd
        - (algebraMap K[X] (RatFunc K) N) * huvA
    rw [mem_valSub_iff', hkey]
    rcases eq_or_ne (N * u) 0 with h0 | h0
    · exact Or.inl (by rw [h0]; simp)
    · refine Or.inr ?_
      rw [ordZP, ordFinZ_div q h0 hbne, cnt_eq_zero_of_not_dvd q hqb]
      simp
  · intro r hr
    rw [mem_valSub_iff']
    rcases eq_or_ne (N * v) 0 with h0 | h0
    · exact Or.inl (by rw [h0]; simp)
    · refine Or.inr ?_
      rw [ordZP, ordFinZ_div r h0 hqn, cnt_pow_other q r hr]
      simp

/-- Approximation at a finite set of finite places. -/
lemma exists_finset_approx (f : FinPlace K → RatFunc K) (T : Finset (FinPlace K)) :
    ∃ y : RatFunc K, (∀ q ∈ T, f q - y ∈ (projectiveLine K).valSub (some q) 0) ∧
      (∀ q ∉ T, y ∈ (projectiveLine K).valSub (some q) 0) := by
  classical
  induction T using Finset.induction with
  | empty => exact ⟨0, by simp, fun q _ => Submodule.zero_mem _⟩
  | insert q₀ T' hq₀ ih =>
    obtain ⟨y', hy'1, hy'2⟩ := ih
    obtain ⟨w, hw1, hw2⟩ := exists_local_approx q₀ (f q₀ - y')
    refine ⟨y' + w, ?_, ?_⟩
    · intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hq'
      · simpa [sub_add_eq_sub_sub] using hw1
      · have h1 := hy'1 q hq'
        have hne : q ≠ q₀ := by rintro rfl; exact hq₀ hq'
        have h2 := hw2 q hne
        have : f q - (y' + w) = (f q - y') - w := by ring
        rw [this]
        exact Submodule.sub_mem _ h1 h2
    · intro q hq
      have hq' : q ∉ T' := fun h => hq (Finset.mem_insert_of_mem h)
      have hne : q ≠ q₀ := by rintro rfl; exact hq (Finset.mem_insert_self _ _)
      exact Submodule.add_mem _ (hy'2 q hq') (hw2 q hne)

/-- Approximation at the place at infinity by a polynomial. -/
lemma exists_poly_approx_inf (z : RatFunc K) :
    ∃ g : K[X], z - algebraMap K[X] (RatFunc K) g
      ∈ (projectiveLine K).valSub (none : Place K) 0 := by
  set g : K[X] := z.num /ₘ z.denom with hg
  set r : K[X] := z.num %ₘ z.denom with hrdef
  have hmon : z.denom.Monic := RatFunc.monic_denom z
  have hden : z.denom ≠ 0 := RatFunc.denom_ne_zero z
  have hmapne : ∀ a : K[X], a ≠ 0 → algebraMap K[X] (RatFunc K) a ≠ 0 := fun a ha hh =>
    ha (RatFunc.algebraMap_injective K (hh.trans (map_zero _).symm))
  have hDne := hmapne _ hden
  have hxd : algebraMap K[X] (RatFunc K) z.num = z * algebraMap K[X] (RatFunc K) z.denom :=
    (div_eq_iff hDne).1 (RatFunc.num_div_denom z)
  have hsum : r + z.denom * g = z.num := Polynomial.modByMonic_add_div z.num hmon
  have hr : r = z.num - z.denom * g := by linear_combination hsum
  have hkey : z - algebraMap K[X] (RatFunc K) g
      = algebraMap K[X] (RatFunc K) r / algebraMap K[X] (RatFunc K) z.denom := by
    rw [eq_div_iff hDne, hr, map_sub, map_mul]
    linear_combination hxd
  refine ⟨g, ?_⟩
  rw [mem_valSub_iff', hkey]
  rcases eq_or_ne r 0 with h0 | h0
  · exact Or.inl (by rw [h0]; simp)
  · refine Or.inr ?_
    have hdeg : r.natDegree < z.denom.natDegree := by
      have h1 := Polynomial.degree_modByMonic_lt z.num hmon
      rw [← hrdef, Polynomial.degree_eq_natDegree h0,
        Polynomial.degree_eq_natDegree hden] at h1
      exact_mod_cast h1
    have hrne := hmapne _ h0
    simp only [ordZP, ordInfZ, div_eq_mul_inv,
      RatFunc.intDegree_mul hrne (inv_ne_zero hDne), RatFunc.intDegree_inv,
      RatFunc.intDegree_polynomial]
    omega

/-- **Strong approximation** for the projective line: the everywhere-integral adeles
together with the rational functions span the whole adele space. -/
lemma AD_zero_sup_FSub_eq_top :
    (projectiveLine K).AD 0 ⊔ (projectiveLine K).FSub = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro α -
  obtain ⟨S, hS⟩ := α.val_mem
  set T : Finset (FinPlace K) := S.preimage some (Option.some_injective _).injOn with hT
  obtain ⟨y, hy1, hy2⟩ := exists_finset_approx (fun q => α.val (some q)) T
  have hfin : ∀ q : FinPlace K,
      α.val (some q) - y ∈ (projectiveLine K).valSub (some q) 0 := by
    intro q
    by_cases hq : q ∈ T
    · exact hy1 q hq
    · have hnot : (some q : Place K) ∉ S := by
        intro h
        exact hq (Finset.mem_preimage.2 h)
      have h1 : α.val (some q) ∈ (projectiveLine K).valSub (some q) 0 := by
        have := hS (some q) hnot
        rw [PreCurve.mem_valSub_iff]
        simpa using this
      exact Submodule.sub_mem _ h1 (hy2 q hq)
  obtain ⟨g, hg⟩ := exists_poly_approx_inf (α.val none - y)
  refine Submodule.mem_sup.2
    ⟨α - (projectiveLine K).diagLin (y + algebraMap K[X] (RatFunc K) g), ?_,
      (projectiveLine K).diagLin (y + algebraMap K[X] (RatFunc K) g), ⟨_, rfl⟩, by ring⟩
  rw [PreCurve.mem_AD_iff]
  intro p
  have hmem : α.val p - (y + algebraMap K[X] (RatFunc K) g)
      ∈ (projectiveLine K).valSub p 0 := by
    cases p with
    | none =>
      have : α.val none - (y + algebraMap K[X] (RatFunc K) g)
          = (α.val none - y) - algebraMap K[X] (RatFunc K) g := by ring
      rw [this]
      exact hg
    | some q =>
      have : α.val (some q) - (y + algebraMap K[X] (RatFunc K) g)
          = (α.val (some q) - y) - algebraMap K[X] (RatFunc K) g := by ring
      rw [this]
      exact Submodule.sub_mem _ (hfin q) (algebraMap_mem_valSub_zero q g)
  rw [PreCurve.mem_valSub_iff] at hmem
  simpa using hmem

end P1

end Math2

/-
The projective line as a `PreCurve`.
-/
import RequestProject.P1.OrdInf
import RequestProject.Math2.Setup

namespace Math2

namespace P1

open Polynomial RatFunc

universe u

variable {K : Type u} [Field K]

/-- A place of the projective line over `K`: either a finite place (a monic irreducible
polynomial) or the place at infinity. -/
abbrev Place (K : Type u) [Field K] := Option (FinPlace K)

/-- The valuation attached to a place. -/
noncomputable def ordP : Place K → AddValuation (RatFunc K) (WithTop ℤ)
  | none => ordInf
  | some q => ordFin q

/-- The degree of a place. -/
def degP : Place K → ℕ
  | none => 1
  | some q => q.poly.natDegree

/-- The integer-valued order function at a place. -/
noncomputable def ordZP : Place K → RatFunc K → ℤ
  | none => ordInfZ
  | some q => ordFinZ q

lemma degP_pos (p : Place K) : 0 < degP p := by
  cases p with
  | none => exact Nat.one_pos
  | some q => exact q.natDegree_pos

lemma ordP_of_ne_zero (p : Place K) {x : RatFunc K} (hx : x ≠ 0) :
    ordP p x = ((ordZP p x : ℤ) : WithTop ℤ) := by
  cases p with
  | none => simpa [ordP, ordZP] using ordInfFun_of_ne_zero hx
  | some q => simpa [ordP, ordZP] using ordFinFun_of_ne_zero q hx

lemma ordZP_eq_zero_of_ordP_eq_zero {p : Place K} {x : RatFunc K} (hx : x ≠ 0)
    (h : ordP p x = (0 : WithTop ℤ)) : ordZP p x = 0 := by
  rw [ordP_of_ne_zero p hx] at h
  exact_mod_cast h

lemma ordP_eq_zero_of_ordZP_eq_zero {p : Place K} {x : RatFunc K} (hx : x ≠ 0)
    (h : ordZP p x = 0) : ordP p x = (0 : WithTop ℤ) := by
  rw [ordP_of_ne_zero p hx, h]
  rfl

lemma ordZP_mul (p : Place K) {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordZP p (x * y) = ordZP p x + ordZP p y := by
  cases p with
  | none => exact ordInfZ_mul hx hy
  | some q => exact ordFinZ_mul q hx hy

/-! ### The degree of a polynomial is the sum of the degrees of its places -/

lemma sum_natDegree_cnt (a : K[X]) (ha : a ≠ 0) (S : Finset (FinPlace K))
    (hS : ∀ q : FinPlace K, q ∉ S → cnt q a = 0) :
    ∑ q ∈ S, (q.poly.natDegree : ℤ) * (cnt q a : ℤ) = (a.natDegree : ℤ) := by
  classical
  induction a using UniqueFactorizationMonoid.induction_on_prime generalizing S with
  | h₁ => exact absurd rfl ha
  | h₂ u hu =>
      have hzero : ∀ q ∈ S, ((q.poly.natDegree : ℤ) * (cnt q u : ℤ)) = 0 := by
        intro q _
        rw [cnt_of_isUnit q hu]
        simp
      rw [Finset.sum_congr rfl hzero]
      simp [Polynomial.natDegree_eq_zero_of_isUnit hu]
  | h₃ b p hb hp ih =>
      have hpne : p ≠ 0 := hp.ne_zero
      have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hpne
      have hunit : IsUnit (Polynomial.C (p.leadingCoeff⁻¹) : K[X]) :=
        isUnit_C.2 (Ne.isUnit (inv_ne_zero hlc))
      have hassoc0 : Associated p (p * Polynomial.C (p.leadingCoeff⁻¹)) :=
        (associated_mul_isUnit_right_iff hunit).2 (Associated.refl p)
      set q₀ : FinPlace K := ⟨p * Polynomial.C (p.leadingCoeff⁻¹), monic_mul_leadingCoeff_inv hpne,
        hassoc0.irreducible hp.irreducible⟩ with hq₀
      have hp_eq : p = q₀.poly * Polynomial.C p.leadingCoeff := by
        rw [hq₀]
        show p = p * Polynomial.C (p.leadingCoeff⁻¹) * Polynomial.C p.leadingCoeff
        rw [mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hlc, Polynomial.C_1, mul_one]
      have hcntp : ∀ r : FinPlace K, cnt r p = if r = q₀ then 1 else 0 := by
        intro r
        rw [hp_eq, cnt_mul r q₀.ne_zero (by simpa using hlc), cnt_C r hlc, add_zero]
        by_cases hr : r = q₀
        · rw [if_pos hr, hr, cnt_self]
        · rw [if_neg hr, cnt_other r q₀ hr]
      have hcnt : ∀ r : FinPlace K, cnt r (p * b) = cnt r p + cnt r b := fun r =>
        cnt_mul r hpne hb
      have hSb : ∀ r : FinPlace K, r ∉ S → cnt r b = 0 := by
        intro r hr
        have h := hS r hr
        rw [hcnt r] at h
        omega
      have hq₀S : q₀ ∈ S := by
        by_contra h
        have h2 := hS q₀ h
        rw [hcnt, hcntp q₀, if_pos rfl] at h2
        omega
      have hsum : ∑ r ∈ S, (r.poly.natDegree : ℤ) * (cnt r (p * b) : ℤ)
          = (∑ r ∈ S, (r.poly.natDegree : ℤ) * (cnt r p : ℤ))
            + ∑ r ∈ S, (r.poly.natDegree : ℤ) * (cnt r b : ℤ) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hcnt r]
        push_cast
        ring
      have h1 : ∑ r ∈ S, (r.poly.natDegree : ℤ) * (cnt r p : ℤ) = (q₀.poly.natDegree : ℤ) := by
        rw [Finset.sum_eq_single q₀]
        · rw [hcntp q₀, if_pos rfl]
          simp
        · intro r _ hr
          rw [hcntp r, if_neg hr]
          simp
        · intro h
          exact absurd hq₀S h
      have h2 := ih hb S hSb
      have hdeg : q₀.poly.natDegree = p.natDegree := by
        rw [hq₀]
        show (p * Polynomial.C (p.leadingCoeff⁻¹)).natDegree = p.natDegree
        rw [Polynomial.natDegree_mul_C (inv_ne_zero hlc)]
      rw [hsum, h1, h2, Polynomial.natDegree_mul hpne hb, hdeg]
      push_cast
      ring

/-! ### Supports -/

/-- A finite set of finite places containing all zeros and poles of a nonzero rational
function. -/
lemma exists_finPlace_support (x : RatFunc K) (hx : x ≠ 0) :
    ∃ T : Finset (FinPlace K), ∀ q : FinPlace K, q ∉ T →
      cnt q x.num = 0 ∧ cnt q x.denom = 0 := by
  classical
  obtain ⟨T₁, hT₁⟩ := exists_finset_cnt x.num (RatFunc.num_ne_zero hx)
  obtain ⟨T₂, hT₂⟩ := exists_finset_cnt x.denom (RatFunc.denom_ne_zero x)
  refine ⟨T₁ ∪ T₂, fun q hq => ⟨hT₁ q ?_, hT₂ q ?_⟩⟩
  · exact fun h => hq (Finset.mem_union_left _ h)
  · exact fun h => hq (Finset.mem_union_right _ h)

open Classical in
/-- The canonical finite set of places carrying the divisor of a nonzero rational function. -/
noncomputable def canonSupport (x : RatFunc K) (hx : x ≠ 0) : Finset (Place K) :=
  insert none (((exists_finPlace_support x hx).choose).map ⟨some, Option.some_injective _⟩)

lemma mem_canonSupport_of_ne {x : RatFunc K} (hx : x ≠ 0) {p : Place K}
    (hp : p ∉ canonSupport x hx) :
    ∃ q : FinPlace K, p = some q ∧ cnt q x.num = 0 ∧ cnt q x.denom = 0 := by
  classical
  cases p with
  | none => exact absurd (Finset.mem_insert_self _ _) hp
  | some q =>
      refine ⟨q, rfl, ?_, ?_⟩ <;>
      · have hq : q ∉ (exists_finPlace_support x hx).choose := by
          intro h
          exact hp (Finset.mem_insert_of_mem (by
            simpa using Finset.mem_map_of_mem ⟨some, Option.some_injective _⟩ h))
        have := (exists_finPlace_support x hx).choose_spec q hq
        simp [this.1, this.2]

lemma ordP_eq_zero_outside_canonSupport {x : RatFunc K} (hx : x ≠ 0) {p : Place K}
    (hp : p ∉ canonSupport x hx) : ordP p x = (0 : WithTop ℤ) := by
  obtain ⟨q, rfl, h1, h2⟩ := mem_canonSupport_of_ne hx hp
  refine ordP_eq_zero_of_ordZP_eq_zero hx ?_
  simp [ordZP, ordFinZ, h1, h2]

lemma ord_support_P1 (x : RatFunc K) (hx : x ≠ 0) :
    ∃ S : Finset (Place K), ∀ p ∉ S, ordP p x = (0 : WithTop ℤ) :=
  ⟨canonSupport x hx, fun _ hp => ordP_eq_zero_outside_canonSupport hx hp⟩

/-! ### The degree of a principal divisor -/

lemma sum_eq_of_subset {x : RatFunc K} (hx : x ≠ 0) {S T : Finset (Place K)} (hST : S ⊆ T)
    (hS : ∀ p ∉ S, ordP p x = (0 : WithTop ℤ)) :
    ∑ p ∈ T, (degP p : ℤ) * ordZP p x = ∑ p ∈ S, (degP p : ℤ) * ordZP p x :=
  (Finset.sum_subset hST (fun p _ hpS => by
    rw [ordZP_eq_zero_of_ordP_eq_zero hx (hS p hpS), mul_zero])).symm

lemma sum_canonSupport (x : RatFunc K) (hx : x ≠ 0) :
    ∑ p ∈ canonSupport x hx, (degP p : ℤ) * ordZP p x = 0 := by
  classical
  set T := (exists_finPlace_support x hx).choose with hT
  have hTspec := (exists_finPlace_support x hx).choose_spec
  have hnotmem : (none : Place K) ∉ T.map ⟨some, Option.some_injective _⟩ := by
    simp
  rw [canonSupport, Finset.sum_insert hnotmem, Finset.sum_map]
  have hnum : ∑ q ∈ T, (q.poly.natDegree : ℤ) * (cnt q x.num : ℤ) = (x.num.natDegree : ℤ) :=
    sum_natDegree_cnt x.num (RatFunc.num_ne_zero hx) T (fun q hq => (hTspec q hq).1)
  have hden : ∑ q ∈ T, (q.poly.natDegree : ℤ) * (cnt q x.denom : ℤ) = (x.denom.natDegree : ℤ) :=
    sum_natDegree_cnt x.denom (RatFunc.denom_ne_zero x) T (fun q hq => (hTspec q hq).2)
  have hsplit : ∑ q ∈ T, (degP (some q) : ℤ) * ordZP (some q) x
      = (∑ q ∈ T, (q.poly.natDegree : ℤ) * (cnt q x.num : ℤ))
        - ∑ q ∈ T, (q.poly.natDegree : ℤ) * (cnt q x.denom : ℤ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [degP, ordZP, ordFinZ]
    ring
  simp only [Function.Embedding.coeFn_mk]
  rw [hsplit, hnum, hden]
  simp only [degP, ordZP, ordInfZ, RatFunc.intDegree, Nat.cast_one, one_mul]
  ring

lemma degree_principal_P1 (x : RatFunc K) (hx : x ≠ 0) (S : Finset (Place K))
    (hS : ∀ p ∉ S, ordP p x = (0 : WithTop ℤ)) :
    ∑ p ∈ S, (degP p : ℤ) * ordZP p x = 0 := by
  classical
  have h1 : ∑ p ∈ S ∪ canonSupport x hx, (degP p : ℤ) * ordZP p x
      = ∑ p ∈ S, (degP p : ℤ) * ordZP p x :=
    sum_eq_of_subset hx Finset.subset_union_left hS
  have h2 : ∑ p ∈ S ∪ canonSupport x hx, (degP p : ℤ) * ordZP p x
      = ∑ p ∈ canonSupport x hx, (degP p : ℤ) * ordZP p x :=
    sum_eq_of_subset hx Finset.subset_union_right
      (fun p hp => ordP_eq_zero_outside_canonSupport hx hp)
  rw [← h1, h2, sum_canonSupport]

/-! ### Constants -/

lemma constants_P1 (x : RatFunc K) (h : ∀ p : Place K, (0 : WithTop ℤ) ≤ ordP p x) :
    ∃ c : K, algebraMap K (RatFunc K) c = x := by
  classical
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, by simp⟩
  have hden : x.denom = 1 := by
    by_cases hu : IsUnit x.denom
    · exact (RatFunc.monic_denom x).eq_one_of_isUnit hu
    obtain ⟨q, hqm, hqi, hqd⟩ := Polynomial.exists_monic_irreducible_factor x.denom hu
    set r : FinPlace K := ⟨q, hqm, hqi⟩ with hr
    have hcd : cnt r x.denom ≠ 0 := fun hc => (cnt_eq_zero_iff r x.denom).1 hc hqd
    have hge := h (some r)
    rw [ordP_of_ne_zero (some r) hx] at hge
    have hge' : (0 : ℤ) ≤ ordZP (some r) x := by exact_mod_cast hge
    simp only [ordZP, ordFinZ] at hge'
    have hcn : cnt r x.num ≠ 0 := by omega
    have hqn : q ∣ x.num := dvd_of_cnt_ne_zero r hcn
    obtain ⟨u, v, huv⟩ := RatFunc.isCoprime_num_denom x
    have : q ∣ (1 : K[X]) := by
      rw [← huv]
      exact dvd_add (Dvd.dvd.mul_left hqn u) (Dvd.dvd.mul_left hqd v)
    exact absurd (isUnit_of_dvd_one this) hqi.not_isUnit
  have hxpoly : x = algebraMap K[X] (RatFunc K) x.num := by
    conv_lhs => rw [← RatFunc.num_div_denom x]
    rw [hden]
    simp
  have hinf := h none
  rw [ordP_of_ne_zero none hx] at hinf
  have hinf' : (0 : ℤ) ≤ ordZP (none : Place K) x := by exact_mod_cast hinf
  simp only [ordZP, ordInfZ, RatFunc.intDegree, hden, Polynomial.natDegree_one] at hinf'
  have hdeg : x.num.natDegree = 0 := by omega
  refine ⟨x.num.coeff 0, ?_⟩
  rw [RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, ← Polynomial.eq_C_of_natDegree_eq_zero hdeg,
    ← hxpoly]

/-! ### The projective line as a `PreCurve` -/

/-- The projective line over `K`, as a `PreCurve`. -/
noncomputable def projectiveLine (K : Type u) [Field K] :
    PreCurve K (RatFunc K) (Place K) where
  ord := ordP
  deg := degP
  ord_algebraMap := by
    intro p c hc
    have hne : algebraMap K (RatFunc K) c ≠ 0 := by
      simp [RatFunc.algebraMap_eq_C, hc]
    refine ordP_eq_zero_of_ordZP_eq_zero hne ?_
    have hpoly : algebraMap K (RatFunc K) c = algebraMap K[X] (RatFunc K) (Polynomial.C c) := by
      rw [RatFunc.algebraMap_eq_C, RatFunc.algebraMap_C]
    cases p with
    | none =>
        simp only [ordZP, hpoly, ordInfZ_algebraMap, Polynomial.natDegree_C]
        simp
    | some q =>
        simp only [ordZP, hpoly, ordFinZ_algebraMap]
        simp [cnt_C q hc]
  uniformizer := by
    intro p
    cases p with
    | none =>
        refine ⟨(RatFunc.X : RatFunc K)⁻¹, ?_⟩
        have hne : (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := inv_ne_zero RatFunc.X_ne_zero
        rw [ordP_of_ne_zero none hne]
        norm_cast
        simp [ordZP, ordInfZ, RatFunc.intDegree_inv]
    | some q =>
        refine ⟨algebraMap K[X] (RatFunc K) q.poly, ?_⟩
        have hne : algebraMap K[X] (RatFunc K) q.poly ≠ 0 := fun hh =>
          q.ne_zero (RatFunc.algebraMap_injective K (hh.trans (map_zero _).symm))
        rw [ordP_of_ne_zero (some q) hne]
        norm_cast
        simp [ordZP, ordFinZ_algebraMap, cnt_self]
  ord_support := ord_support_P1
  degree_principal := by
    intro x hx S hS
    have := degree_principal_P1 x hx S hS
    rw [← this]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ordP_of_ne_zero p hx]
    simp
  constants := constants_P1
  place_nonempty := ⟨none⟩

end P1

end Math2

/-
The valuation of the projective line at the place at infinity.
-/
import RequestProject.P1.OrdFin

namespace Math2

namespace P1

open Polynomial RatFunc

universe u

variable {K : Type u} [Field K]

/-- The order of vanishing at infinity of a rational function. -/
noncomputable def ordInfZ (x : RatFunc K) : ℤ := -x.intDegree

@[simp] lemma ordInfZ_one : ordInfZ (1 : RatFunc K) = 0 := by simp [ordInfZ]

lemma ordInfZ_mul {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordInfZ (x * y) = ordInfZ x + ordInfZ y := by
  simp only [ordInfZ, RatFunc.intDegree_mul hx hy]
  ring

lemma ordInfZ_add_ge {x y : RatFunc K} (hxy : x + y ≠ 0) :
    min (ordInfZ x) (ordInfZ y) ≤ ordInfZ (x + y) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [zero_add] at hxy ⊢
    exact min_le_right _ _
  rcases eq_or_ne y 0 with rfl | hy
  · simp only [add_zero] at hxy ⊢
    exact min_le_left _ _
  have h := RatFunc.intDegree_add_le hy hxy
  simp only [ordInfZ]
  rcases max_cases x.intDegree y.intDegree with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at h <;> omega

lemma ordInfZ_algebraMap (p : K[X]) :
    ordInfZ (algebraMap K[X] (RatFunc K) p) = -(p.natDegree : ℤ) := by
  simp [ordInfZ]

open Classical in
/-- The order function at the place at infinity, with value `⊤` at `0`. -/
noncomputable def ordInfFun (x : RatFunc K) : WithTop ℤ :=
  if x = 0 then (⊤ : WithTop ℤ) else ((ordInfZ x : ℤ) : WithTop ℤ)

@[simp] lemma ordInfFun_zero : ordInfFun (0 : RatFunc K) = (⊤ : WithTop ℤ) := by
  simp [ordInfFun]

lemma ordInfFun_of_ne_zero {x : RatFunc K} (hx : x ≠ 0) :
    ordInfFun x = ((ordInfZ x : ℤ) : WithTop ℤ) := by
  simp [ordInfFun, hx]

/-- The additive valuation of the rational function field at the place at infinity. -/
noncomputable def ordInf : AddValuation (RatFunc K) (WithTop ℤ) :=
  AddValuation.of ordInfFun (by simp) (by simp [ordInfFun_of_ne_zero (one_ne_zero (α := RatFunc K))])
    (by
      intro x y
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      rcases eq_or_ne y 0 with rfl | hy
      · simp
      rcases eq_or_ne (x + y) 0 with h | hxy
      · simp [h]
      · rw [ordInfFun_of_ne_zero hx, ordInfFun_of_ne_zero hy, ordInfFun_of_ne_zero hxy,
          min_le_iff]
        have h2 := ordInfZ_add_ge hxy
        rw [min_le_iff] at h2
        rcases h2 with h2 | h2
        · exact Or.inl (by exact_mod_cast h2)
        · exact Or.inr (by exact_mod_cast h2))
    (by
      intro x y
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      rcases eq_or_ne y 0 with rfl | hy
      · simp
      rw [ordInfFun_of_ne_zero hx, ordInfFun_of_ne_zero hy,
        ordInfFun_of_ne_zero (mul_ne_zero hx hy), ordInfZ_mul hx hy]
      norm_cast)

@[simp] lemma ordInf_apply (x : RatFunc K) : (ordInf : AddValuation (RatFunc K) (WithTop ℤ)) x
    = ordInfFun x := rfl

end P1

end Math2

/-
The valuation of the projective line at a finite place.
-/
import RequestProject.P1.Count

namespace Math2

namespace P1

open Polynomial RatFunc

universe u

variable {K : Type u} [Field K]

/-- The order of vanishing of a rational function at a finite place. -/
noncomputable def ordFinZ (q : FinPlace K) (x : RatFunc K) : ℤ :=
  (cnt q x.num : ℤ) - (cnt q x.denom : ℤ)

lemma cnt_add_ge (q : FinPlace K) {u v : K[X]} (huv : u + v ≠ 0) :
    min (cnt q u) (cnt q v) ≤ cnt q (u + v) := by
  refine (pow_dvd_iff_le_cnt q huv _).1 ?_
  refine dvd_add ?_ ?_
  · exact dvd_trans (pow_dvd_pow _ (min_le_left _ _)) (pow_cnt_dvd q u)
  · exact dvd_trans (pow_dvd_pow _ (min_le_right _ _)) (pow_cnt_dvd q v)

@[simp] lemma ordFinZ_one (q : FinPlace K) : ordFinZ q 1 = 0 := by
  simp [ordFinZ, cnt_one]

lemma ordFinZ_mul (q : FinPlace K) {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordFinZ q (x * y) = ordFinZ q x + ordFinZ q y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hkey := RatFunc.num_denom_mul x y
  have h1 : cnt q ((x * y).num * (x.denom * y.denom))
      = cnt q (x.num * y.num * (x * y).denom) := by rw [hkey]
  rw [cnt_mul q (RatFunc.num_ne_zero hxy)
      (mul_ne_zero (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y)),
    cnt_mul q (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y),
    cnt_mul q (mul_ne_zero (RatFunc.num_ne_zero hx) (RatFunc.num_ne_zero hy))
      (RatFunc.denom_ne_zero (x * y)),
    cnt_mul q (RatFunc.num_ne_zero hx) (RatFunc.num_ne_zero hy)] at h1
  simp only [ordFinZ]
  omega

lemma ordFinZ_add_ge (q : FinPlace K) {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) : min (ordFinZ q x) (ordFinZ q y) ≤ ordFinZ q (x + y) := by
  have hkey : (x + y).num * (x.denom * y.denom)
      = (x.num * y.denom + x.denom * y.num) * (x + y).denom := RatFunc.num_denom_add x y
  have hune : x.num * y.denom ≠ 0 :=
    mul_ne_zero (RatFunc.num_ne_zero hx) (RatFunc.denom_ne_zero y)
  have hvne : x.denom * y.num ≠ 0 :=
    mul_ne_zero (RatFunc.denom_ne_zero x) (RatFunc.num_ne_zero hy)
  have huv : x.num * y.denom + x.denom * y.num ≠ 0 := by
    intro h
    apply RatFunc.num_ne_zero hxy
    have h2 : (x + y).num * (x.denom * y.denom) = 0 := by rw [hkey, h, zero_mul]
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · exact absurd h3 (mul_ne_zero (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y))
  have h1 : cnt q ((x + y).num * (x.denom * y.denom))
      = cnt q ((x.num * y.denom + x.denom * y.num) * (x + y).denom) := by rw [hkey]
  rw [cnt_mul q (RatFunc.num_ne_zero hxy)
      (mul_ne_zero (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y)),
    cnt_mul q (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y),
    cnt_mul q huv (RatFunc.denom_ne_zero (x + y))] at h1
  have h2 := cnt_add_ge q huv
  rw [cnt_mul q (RatFunc.num_ne_zero hx) (RatFunc.denom_ne_zero y),
    cnt_mul q (RatFunc.denom_ne_zero x) (RatFunc.num_ne_zero hy), min_le_iff] at h2
  simp only [ordFinZ, min_le_iff]
  rcases h2 with h2 | h2
  · left; omega
  · right; omega

lemma ordFinZ_algebraMap (q : FinPlace K) (a : K[X]) :
    ordFinZ q (algebraMap K[X] (RatFunc K) a) = cnt q a := by
  simp [ordFinZ, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, cnt_one]

lemma ordFinZ_inv (q : FinPlace K) {x : RatFunc K} (hx : x ≠ 0) :
    ordFinZ q x⁻¹ = -ordFinZ q x := by
  have h := ordFinZ_mul q hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, ordFinZ_one] at h
  omega

lemma ordFinZ_div (q : FinPlace K) {a b : K[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    ordFinZ q (algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) b)
      = (cnt q a : ℤ) - cnt q b := by
  have hane : algebraMap K[X] (RatFunc K) a ≠ 0 := fun h =>
    ha (RatFunc.algebraMap_injective K (h.trans (map_zero _).symm))
  have hbne : algebraMap K[X] (RatFunc K) b ≠ 0 := fun h =>
    hb (RatFunc.algebraMap_injective K (h.trans (map_zero _).symm))
  rw [div_eq_mul_inv, ordFinZ_mul q hane (inv_ne_zero hbne), ordFinZ_inv q hbne,
    ordFinZ_algebraMap, ordFinZ_algebraMap]
  ring

open Classical in
/-- The additive valuation at a finite place. -/
noncomputable def ordFinFun (q : FinPlace K) (x : RatFunc K) : WithTop ℤ :=
  if x = 0 then (⊤ : WithTop ℤ) else ((ordFinZ q x : ℤ) : WithTop ℤ)

@[simp] lemma ordFinFun_zero (q : FinPlace K) : ordFinFun q 0 = (⊤ : WithTop ℤ) := by
  simp [ordFinFun]

lemma ordFinFun_of_ne_zero (q : FinPlace K) {x : RatFunc K} (hx : x ≠ 0) :
    ordFinFun q x = ((ordFinZ q x : ℤ) : WithTop ℤ) := by
  simp [ordFinFun, hx]

/-- The additive valuation of the rational function field at a finite place. -/
noncomputable def ordFin (q : FinPlace K) : AddValuation (RatFunc K) (WithTop ℤ) :=
  AddValuation.of (ordFinFun q) (by simp) (by simp [ordFinFun_of_ne_zero q one_ne_zero])
    (by
      intro x y
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      rcases eq_or_ne y 0 with rfl | hy
      · simp
      rcases eq_or_ne (x + y) 0 with h | hxy
      · simp [h]
      · rw [ordFinFun_of_ne_zero q hx, ordFinFun_of_ne_zero q hy, ordFinFun_of_ne_zero q hxy,
          min_le_iff]
        have h2 := ordFinZ_add_ge q hx hy hxy
        rw [min_le_iff] at h2
        rcases h2 with h2 | h2
        · exact Or.inl (by exact_mod_cast h2)
        · exact Or.inr (by exact_mod_cast h2))
    (by
      intro x y
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      rcases eq_or_ne y 0 with rfl | hy
      · simp
      rw [ordFinFun_of_ne_zero q hx, ordFinFun_of_ne_zero q hy,
        ordFinFun_of_ne_zero q (mul_ne_zero hx hy), ordFinZ_mul q hx hy]
      norm_cast)

@[simp] lemma ordFin_apply (q : FinPlace K) (x : RatFunc K) : ordFin q x = ordFinFun q x := rfl

end P1

end Math2

