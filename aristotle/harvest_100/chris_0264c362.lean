import Mathlib

/-!
# Voevodsky Milnor: definitions and supporting results

Supporting development for `Frontier.voevodsky_milnor` (see `RequestProject/Main.lean`):
mod-2 Milnor K-theory, mod-2 Galois cohomology, the statement of the Milnor conjecture, the
degree-zero base case, the separably closed case, and the degree-one identifications.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false

namespace Frontier

/-!
## Mod-2 Milnor K-theory

For a field `F`, the `n`-th Milnor K-group `K^M_n(F)` is the degree-`n` part of the quotient of
the tensor algebra of the abelian group `Fˣ` by the Steinberg relations `a ⊗ (1 - a) = 0`.
Reducing mod 2, `k^M_n(F) = K^M_n(F)/2` is therefore the quotient of the free `ZMod 2`-module on
`n`-tuples of units by
* multilinearity in each slot, and
* the Steinberg relations (in adjacent slots).

This is the definition used below.
-/

section Milnor

variable (F : Type) [Field F]

/-- The defining relations of mod-2 Milnor K-theory in degree `n`: multilinearity in each slot,
and the Steinberg relation `{a, 1 - a} = 0` in adjacent slots. -/
def milnorRelSet (n : ℕ) : Set ((Fin n → Fˣ) →₀ ZMod 2) :=
  {x | (∃ (i : Fin n) (v : Fin n → Fˣ) (a b : Fˣ),
          x = Finsupp.single (Function.update v i (a * b)) 1
              - Finsupp.single (Function.update v i a) 1
              - Finsupp.single (Function.update v i b) 1) ∨
       (∃ (i : Fin n) (h : (i : ℕ) + 1 < n) (v : Fin n → Fˣ),
          ((v i : F) + (v ⟨(i : ℕ) + 1, h⟩ : F) = 1) ∧ x = Finsupp.single v 1)}

/-- Mod-2 Milnor K-theory `k^M_n(F) = K^M_n(F)/2` of a field `F`, in degree `n`. -/
abbrev MilnorK2 (n : ℕ) : Type :=
  ((Fin n → Fˣ) →₀ ZMod 2) ⧸ Submodule.span (ZMod 2) (milnorRelSet F n)

end Milnor

/-!
## Mod-2 Galois cohomology

`H^n(F, ℤ/2)` is the continuous (i.e. locally constant) cochain cohomology of the absolute
Galois group `Gal(F^sep/F)`, equipped with its Krull topology, acting trivially on `ℤ/2`.

The differential is the usual inhomogeneous cochain differential (borrowed from Mathlib's group
cohomology, for the trivial representation); over `ℤ/2` with trivial action all the signs in it
disappear, so `d f (g₀,…,gₙ)` is the plain sum of the faces.
-/

section GaloisCohomology

open groupCohomology

/-- The absolute Galois group of `F`, with its Krull topology. -/
abbrev AbsGal (F : Type) [Field F] : Type := SeparableClosure F ≃ₐ[F] SeparableClosure F

/-- The inhomogeneous cochain differential with `ℤ/2` coefficients and trivial action. -/
noncomputable def dd (G : Type) [Group G] (n : ℕ) :
    ((Fin n → G) → ZMod 2) →ₗ[ZMod 2] ((Fin (n + 1) → G) → ZMod 2) :=
  (inhomogeneousCochains.d (Rep.trivial (ZMod 2) G (ZMod 2)) n).hom

lemma dd_apply (G : Type) [Group G] (n : ℕ) (f : (Fin n → G) → ZMod 2) (g : Fin (n + 1) → G) :
    dd G n f g = f (fun i => g i.succ) + ∑ j : Fin (n + 1), f (Fin.contractNth j (· * ·) g) := by
  simp [dd, inhomogeneousCochains.d_hom_apply]

lemma dd_dd (G : Type) [Group G] (n : ℕ) (f : (Fin n → G) → ZMod 2) :
    dd G (n + 1) (dd G n f) = 0 := by
  have h := inhomogeneousCochains.d_comp_d (A := Rep.trivial (ZMod 2) G (ZMod 2)) (n := n)
  have := congrArg (fun m => ModuleCat.Hom.hom m f) h
  simpa [dd] using this

lemma dd_subsingleton (G : Type) [Group G] [Subsingleton G] (n : ℕ)
    (f : (Fin n → G) → ZMod 2) (g : Fin (n + 1) → G) (g' : Fin n → G) :
    dd G n f g = (n : ZMod 2) * f g' := by
  rw [dd_apply]
  have h : ∀ g'' : Fin n → G, f g'' = f g' := fun g'' => by
    congr 1; exact Subsingleton.elim _ _
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : ((n : ZMod 2) + 1 + 1) = (n : ZMod 2) := by
    rw [add_assoc, show ((1 : ZMod 2) + 1) = 0 from rfl, add_zero]
  push_cast
  linear_combination (f g') * h2

variable (F : Type) [Field F]

/-- The submodule of continuous (= locally constant) `n`-cochains. -/
def contCochains (n : ℕ) : Submodule (ZMod 2) ((Fin n → AbsGal F) → ZMod 2) where
  carrier := {f | IsLocallyConstant f}
  add_mem' hf hg := IsLocallyConstant.comp₂ hf hg (· + ·)
  zero_mem' := IsLocallyConstant.const 0
  smul_mem' c _ hf := hf.comp (c * ·)

lemma continuous_contractNth {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {n : ℕ} (j : Fin (n + 1)) :
    Continuous fun g : Fin (n + 1) → G => Fin.contractNth j (· * ·) g := by
  refine continuous_pi fun k => ?_
  unfold Fin.contractNth
  split_ifs
  · exact continuous_apply _
  · exact (continuous_apply _).mul (continuous_apply _)
  · exact continuous_apply _

lemma dd_mem_contCochains {n : ℕ} {f : (Fin n → AbsGal F) → ZMod 2}
    (hf : f ∈ contCochains F n) : dd (AbsGal F) n f ∈ contCochains F (n + 1) := by
  have hf' : IsLocallyConstant f := hf
  have h1 : IsLocallyConstant fun g : Fin (n + 1) → AbsGal F => f fun i => g i.succ :=
    hf'.comp_continuous (continuous_pi fun i => continuous_apply _)
  have h2 : ∀ j : Fin (n + 1),
      IsLocallyConstant fun g : Fin (n + 1) → AbsGal F => f (Fin.contractNth j (· * ·) g) :=
    fun j => hf'.comp_continuous (continuous_contractNth j)
  have : IsLocallyConstant fun g : Fin (n + 1) → AbsGal F =>
      f (fun i => g i.succ) + ∑ j : Fin (n + 1), f (Fin.contractNth j (· * ·) g) := by
    refine IsLocallyConstant.comp₂ h1 ?_ (· + ·)
    classical
    induction (Finset.univ : Finset (Fin (n + 1))) using Finset.induction with
    | empty => simpa using IsLocallyConstant.const (0 : ZMod 2)
    | insert a s ha ih =>
        simpa [Finset.sum_insert ha] using IsLocallyConstant.comp₂ (h2 a) ih (· + ·)
  simpa [contCochains, Set.mem_setOf_eq, funext fun g => dd_apply (AbsGal F) n f g] using this

/-- Continuous `n`-cocycles. -/
def contCocycles (n : ℕ) : Submodule (ZMod 2) ((Fin n → AbsGal F) → ZMod 2) :=
  contCochains F n ⊓ LinearMap.ker (dd (AbsGal F) n)

/-- Continuous `n`-coboundaries. -/
noncomputable def contCoboundaries : ∀ n : ℕ, Submodule (ZMod 2) ((Fin n → AbsGal F) → ZMod 2)
  | 0 => ⊥
  | n + 1 => Submodule.map (dd (AbsGal F) n) (contCochains F n)

lemma contCoboundaries_le_contCocycles (n : ℕ) :
    contCoboundaries F n ≤ contCocycles F n := by
  cases n with
  | zero => simp [contCoboundaries]
  | succ m =>
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨dd_mem_contCochains F hf, dd_dd (AbsGal F) m f⟩

/-- Mod-2 Galois cohomology `H^n(F, ℤ/2)`: continuous cochain cohomology of the absolute Galois
group of `F` with trivial `ℤ/2` coefficients. -/
abbrev GaloisCohomologyMod2 (n : ℕ) : Type :=
  contCocycles F n ⧸ Submodule.comap (contCocycles F n).subtype (contCoboundaries F n)

end GaloisCohomology

/-!
## The statement of the Milnor conjecture
-/

/-- The Milnor conjecture (Voevodsky's theorem) in degree `n` for the field `F`: mod-2 Milnor
K-theory in degree `n` agrees with mod-2 Galois cohomology in degree `n`.

(The full theorem asserts moreover that the comparison is induced by the norm-residue / Galois
symbol map; here we only record the existence of an isomorphism of `ℤ/2`-vector spaces.) -/
def NormResidueIso (F : Type) [Field F] (n : ℕ) : Prop :=
  Nonempty (MilnorK2 F n ≃ₗ[ZMod 2] GaloisCohomologyMod2 F n)

/-- The Milnor conjecture, proved by Voevodsky: for every field of characteristic `≠ 2` and every
degree `n`, mod-2 Milnor K-theory agrees with mod-2 Galois cohomology. -/
def MilnorConjectureMod2 : Prop :=
  ∀ (F : Type) [Field F], ringChar F ≠ 2 → ∀ n : ℕ, NormResidueIso F n

/-!
## Degree zero, for an arbitrary field
-/

section DegreeZero

variable (F : Type) [Field F]

lemma milnorRelSet_zero : milnorRelSet F 0 = ∅ := by
  ext x
  simp only [milnorRelSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro (⟨i, -⟩ | ⟨i, -⟩) <;> exact i.elim0

/-- In degree `0`, mod-2 Milnor K-theory is `ℤ/2`. -/
noncomputable def milnorK2Zero : MilnorK2 F 0 ≃ₗ[ZMod 2] ZMod 2 :=
  (Submodule.quotEquivOfEqBot _ (by rw [milnorRelSet_zero]; simp)).trans
    ((Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) (Fin 0 → Fˣ)).trans
      (LinearEquiv.funUnique _ _ _))

lemma contCochains_zero_eq_top : contCochains F 0 = ⊤ := by
  refine eq_top_iff.2 fun f _ => ?_
  exact IsLocallyConstant.of_constant f fun x y => by rw [Subsingleton.elim x y]

lemma dd_zero_eq_zero (f : (Fin 0 → AbsGal F) → ZMod 2) : dd (AbsGal F) 0 f = 0 := by
  funext g
  rw [dd_apply]
  have h : ∀ g' : Fin 0 → AbsGal F, f g' = f (fun i => g i.succ) := fun g' => by
    congr 1
    exact Subsingleton.elim _ _
  have key : (f fun i => g i.succ) + (f fun i => g i.succ) = 0 := by
    generalize (f fun i => g i.succ) = x
    revert x
    decide
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Pi.zero_apply]
  simpa using key

lemma contCocycles_zero_eq_top : contCocycles F 0 = ⊤ := by
  rw [contCocycles, contCochains_zero_eq_top]
  refine eq_top_iff.2 fun f _ => ⟨trivial, ?_⟩
  simpa using dd_zero_eq_zero F f

/-- In degree `0`, mod-2 Galois cohomology is `ℤ/2`. -/
noncomputable def galoisCohomologyMod2Zero : GaloisCohomologyMod2 F 0 ≃ₗ[ZMod 2] ZMod 2 :=
  (Submodule.quotEquivOfEqBot _ (by simp [contCoboundaries])).trans
    (((LinearEquiv.ofEq _ _ (contCocycles_zero_eq_top F)).trans (Submodule.topEquiv)).trans
      (LinearEquiv.funUnique _ _ _))

/-- **Base case of the Milnor conjecture**: in degree `0` it holds for every field. -/
theorem normResidueIso_zero : NormResidueIso F 0 :=
  ⟨(milnorK2Zero F).trans (galoisCohomologyMod2Zero F).symm⟩

end DegreeZero

/-!
## Separably closed fields: the conjecture in all degrees
-/

section SepClosed

variable (F : Type) [Field F] [IsSepClosed F]

/-- Over `ℤ/2`, casting an even natural number gives `0`. -/
lemma natCast_add_self_zmod_two (k : ℕ) : ((k + k : ℕ) : ZMod 2) = 0 := by
  push_cast
  rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]

omit [IsSepClosed F] in
lemma two_ne_zero_of_ringChar_ne_two (hchar : ringChar F ≠ 2) : (2 : F) ≠ 0 := by
  intro h
  have hd : ringChar F ∣ 2 := ringChar.dvd (x := 2) (by exact_mod_cast h)
  have hle := Nat.le_of_dvd (by norm_num) hd
  have h1 : ringChar F = 1 ∨ ringChar F = 2 := by
    interval_cases hc : ringChar F <;> simp_all
  rcases h1 with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · exact hchar h1

/-- In a separably closed field of characteristic `≠ 2` every unit is a square. -/
lemma exists_sq (hchar : ringChar F ≠ 2) (a : Fˣ) : ∃ b : Fˣ, b * b = a := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_ringChar_ne_two F hchar
  have hsep : (Polynomial.X ^ 2 - Polynomial.C (a : F)).Separable :=
    Polynomial.separable_X_pow_sub_C (n := 2) (a : F) (by simpa using h2) a.ne_zero
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C (a : F)).degree ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C (by norm_num)]
    simp
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root _ hdeg hsep
  have hx2 : x ^ 2 = (a : F) := by
    have hr := hx
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero] at hr
    exact hr
  have hxne : x ≠ 0 := by
    intro h
    apply a.ne_zero
    rw [← hx2, h]; ring
  refine ⟨Units.mk0 x hxne, ?_⟩
  ext
  simpa [pow_two] using hx2

/-- The absolute Galois group of a separably closed field is trivial. -/
instance absGal_subsingleton : Subsingleton (AbsGal F) := by
  have hs : Function.Surjective (algebraMap F (SeparableClosure F)) :=
    IsSepClosed.algebraMap_surjective F (SeparableClosure F)
  refine ⟨fun σ τ => ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := hs x
  simp

/-- Mod-2 Milnor K-theory of a separably closed field of characteristic `≠ 2` vanishes in
positive degrees. -/
lemma milnorK2_succ_subsingleton (hchar : ringChar F ≠ 2) (n : ℕ) :
    Subsingleton (MilnorK2 F (n + 1)) := by
  rw [Submodule.Quotient.subsingleton_iff]
  refine eq_top_iff.2 fun x _ => ?_
  have key : ∀ v : Fin (n + 1) → Fˣ,
      Finsupp.single v (1 : ZMod 2) ∈ Submodule.span (ZMod 2) (milnorRelSet F (n + 1)) := by
    intro v
    obtain ⟨b, hb⟩ := exists_sq F hchar (v 0)
    have hmem : Finsupp.single (Function.update v 0 (b * b)) (1 : ZMod 2)
        - Finsupp.single (Function.update v 0 b) 1
        - Finsupp.single (Function.update v 0 b) 1 ∈ milnorRelSet F (n + 1) :=
      Or.inl ⟨0, v, b, b, rfl⟩
    have h1 : Function.update v 0 (b * b) = v := by rw [hb]; exact Function.update_eq_self _ _
    have h2 : Finsupp.single (Function.update v 0 b) (1 : ZMod 2)
        + Finsupp.single (Function.update v 0 b) (1 : ZMod 2) = 0 := by
      rw [← Finsupp.single_add]
      simp only [show (1 : ZMod 2) + 1 = 0 from rfl, Finsupp.single_zero]
    have hspan := Submodule.subset_span (R := ZMod 2) hmem
    rwa [h1, sub_sub, h2, sub_zero] at hspan
  induction x using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add f g hf hg => exact Submodule.add_mem _ (hf trivial) (hg trivial)
  | single v c =>
      have hc : Finsupp.single v c = c • Finsupp.single v (1 : ZMod 2) := by
        simp [Finsupp.smul_single]
      rw [hc]
      exact Submodule.smul_mem _ _ (key v)

lemma contCochains_eq_top_of_isSepClosed (n : ℕ) : contCochains F n = ⊤ :=
  eq_top_iff.2 fun f _ =>
    IsLocallyConstant.of_constant f fun x y => by rw [Subsingleton.elim x y]

/-- Mod-2 Galois cohomology of a separably closed field vanishes in positive degrees. -/
lemma galoisCohomologyMod2_succ_subsingleton (n : ℕ) :
    Subsingleton (GaloisCohomologyMod2 F (n + 1)) := by
  rw [Submodule.Quotient.subsingleton_iff]
  refine eq_top_iff.2 fun x _ => ?_
  show (x : (Fin (n + 1) → AbsGal F) → ZMod 2) ∈ contCoboundaries F (n + 1)
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- `n` is even, so `n + 1` is odd: the differential out of degree `n + 1` is injective.
    have hker : dd (AbsGal F) (n + 1) (x : (Fin (n + 1) → AbsGal F) → ZMod 2) = 0 := x.2.2
    have hcast : ((n + 1 : ℕ) : ZMod 2) = 1 := by
      rw [hk, Nat.cast_add, natCast_add_self_zmod_two, Nat.cast_one, zero_add]
    have hx0 : (x : (Fin (n + 1) → AbsGal F) → ZMod 2) = 0 := by
      funext g
      have hg := congrFun hker (fun _ => 1)
      rw [dd_subsingleton (AbsGal F) (n + 1) _ _ g, hcast, one_mul] at hg
      simpa using hg
    rw [hx0]
    exact Submodule.zero_mem _
  · -- `n` is odd: the differential into degree `n + 1` is surjective.
    have hcast : ((n : ℕ) : ZMod 2) = 1 := by
      rw [hk, show 2 * k + 1 = (k + k) + 1 by ring, Nat.cast_add, natCast_add_self_zmod_two,
        Nat.cast_one, zero_add]
    refine ⟨fun _ => (x : (Fin (n + 1) → AbsGal F) → ZMod 2) (fun _ => 1), ?_, ?_⟩
    · rw [contCochains_eq_top_of_isSepClosed]; trivial
    · funext g
      rw [dd_subsingleton (AbsGal F) n _ _ (fun _ => 1), hcast, one_mul]
      exact congrArg (x : (Fin (n + 1) → AbsGal F) → ZMod 2) (Subsingleton.elim _ _)

/-- **The Milnor conjecture holds for separably closed fields of characteristic `≠ 2`**, in every
degree: both sides vanish in positive degrees, and both are `ℤ/2` in degree `0`. -/
theorem normResidueIso_of_isSepClosed (hchar : ringChar F ≠ 2) (n : ℕ) : NormResidueIso F n := by
  cases n with
  | zero => exact normResidueIso_zero F
  | succ m =>
      have h1 := milnorK2_succ_subsingleton F hchar m
      have h2 := galoisCohomologyMod2_succ_subsingleton F m
      exact ⟨{ toFun := fun _ => 0, map_add' := by intros; simp
               map_smul' := by intros; simp
               invFun := fun _ => 0
               left_inv := fun _ => Subsingleton.elim _ _
               right_inv := fun _ => Subsingleton.elim _ _ }⟩

end SepClosed

/-!
## Degree one on the Milnor side: `k^M_1(F) = Fˣ/(Fˣ)²`

A sanity check on the definition of mod-2 Milnor K-theory: in degree `1` it is the group of
square classes of `F`.
-/

section DegreeOne

variable (F : Type) [Field F]

lemma add_self_eq_zero_zmod2 {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (x : M) :
    x + x = 0 := by
  have h : (2 : ZMod 2) • x = 0 := by rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
  simpa [two_smul] using h

/-- The group of square classes `Fˣ/(Fˣ)²`, written additively. -/
abbrev SquareClasses : Type := Additive (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range)

lemma two_nsmul_squareClasses (x : SquareClasses F) : (2 : ℕ) • x = 0 := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    change Additive.ofMul (QuotientGroup.mk (a ^ 2)) = 0
    have h : (QuotientGroup.mk (a ^ 2) : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ⟨a, rfl⟩
    simp [h]

noncomputable instance : Module (ZMod 2) (SquareClasses F) :=
  @AddCommGroup.zmodModule 2 (SquareClasses F) inferInstance (two_nsmul_squareClasses F)

lemma update_fin_one (v : Fin 1 → Fˣ) (c : Fˣ) : Function.update v 0 c = fun _ => c := by
  funext j
  rw [Subsingleton.elim j 0]
  simp

/-- The degree-one symbol `{a} ∈ k^M_1(F)` of a unit `a`. -/
noncomputable def sym1 (a : Fˣ) : MilnorK2 F 1 :=
  Submodule.Quotient.mk (Finsupp.single (fun _ => a) 1)

lemma sym1_mul (a b : Fˣ) : sym1 F (a * b) = sym1 F a + sym1 F b := by
  have hmem : Finsupp.single (Function.update (fun _ => a) (0 : Fin 1) (a * b)) (1 : ZMod 2)
      - Finsupp.single (Function.update (fun _ => a) (0 : Fin 1) a) 1
      - Finsupp.single (Function.update (fun _ => a) (0 : Fin 1) b) 1 ∈ milnorRelSet F 1 :=
    Or.inl ⟨0, fun _ => a, a, b, rfl⟩
  have h := Submodule.subset_span (R := ZMod 2) hmem
  rw [update_fin_one, update_fin_one, update_fin_one] at h
  have h0 := (Submodule.Quotient.mk_eq_zero _).2 h
  rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, sub_sub, sub_eq_zero] at h0
  exact h0

lemma sym1_one : sym1 F 1 = 0 := by
  have h := sym1_mul F 1 1
  rw [mul_one] at h
  have h2 : sym1 F 1 + 0 = sym1 F 1 + sym1 F 1 := by simpa using h
  exact (add_left_cancel h2).symm

lemma sym1_sq (a : Fˣ) : sym1 F (a ^ 2) = 0 := by
  rw [pow_two, sym1_mul]
  exact add_self_eq_zero_zmod2 _

/-- The comparison map `k^M_1(F) → Fˣ/(Fˣ)²`. -/
noncomputable def milnorK2OneToSquareClasses : MilnorK2 F 1 →ₗ[ZMod 2] SquareClasses F := by
  refine Submodule.liftQ _
    (Finsupp.linearCombination (ZMod 2)
      (fun v : Fin 1 → Fˣ => (Additive.ofMul (QuotientGroup.mk (v 0)) : SquareClasses F))) ?_
  rw [Submodule.span_le]
  rintro x (⟨i, v, a, b, rfl⟩ | ⟨i, h, v, -, rfl⟩)
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, Finsupp.linearCombination_single,
      one_smul, Function.update_self]
    rw [QuotientGroup.mk_mul, ofMul_mul]
    abel
  · omega

lemma milnorK2OneToSquareClasses_sym1 (a : Fˣ) :
    milnorK2OneToSquareClasses F (sym1 F a) = Additive.ofMul (QuotientGroup.mk a) := by
  simp [sym1, milnorK2OneToSquareClasses]

/-- The symbol map `Fˣ → k^M_1(F)`, written multiplicatively on the source. -/
noncomputable def sym1Hom : Fˣ →* Multiplicative (MilnorK2 F 1) where
  toFun a := Multiplicative.ofAdd (sym1 F a)
  map_one' := by simp [sym1_one]
  map_mul' a b := by simp [sym1_mul]

/-- The comparison map `Fˣ/(Fˣ)² → k^M_1(F)`. -/
noncomputable def squareClassesToMilnorK2One : SquareClasses F →ₗ[ZMod 2] MilnorK2 F 1 :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun x =>
        Multiplicative.toAdd
          (QuotientGroup.lift _ (sym1Hom F)
            (by rintro _ ⟨c, rfl⟩; exact sym1_sq F c) (Additive.toMul x))
      map_zero' := by simp
      map_add' := fun x y => by
        have h : Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y := rfl
        rw [h, map_mul]
        rfl }

lemma squareClassesToMilnorK2One_mk (a : Fˣ) :
    squareClassesToMilnorK2One F (Additive.ofMul (QuotientGroup.mk a)) = sym1 F a := rfl

/-- **Mod-2 Milnor K-theory in degree one is the group of square classes `Fˣ/(Fˣ)²`.** -/
noncomputable def milnorK2OneEquiv : MilnorK2 F 1 ≃ₗ[ZMod 2] SquareClasses F :=
  LinearEquiv.ofLinear (milnorK2OneToSquareClasses F) (squareClassesToMilnorK2One F)
    (by
      refine LinearMap.ext fun x => ?_
      induction x using QuotientGroup.induction_on with
      | H a =>
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
        show milnorK2OneToSquareClasses F
            (squareClassesToMilnorK2One F (Additive.ofMul (QuotientGroup.mk a)))
          = Additive.ofMul (QuotientGroup.mk a)
        rw [squareClassesToMilnorK2One_mk, milnorK2OneToSquareClasses_sym1])
    (by
      refine LinearMap.ext fun x => ?_
      induction x using Submodule.Quotient.induction_on with
      | H f =>
        induction f using Finsupp.induction_linear with
        | zero => simp
        | add f g hf hg =>
            simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at *
            rw [Submodule.Quotient.mk_add, map_add, map_add, hf, hg]
        | single v c =>
            have hv : (fun _ => v 0) = v := by funext j; rw [Subsingleton.elim j 0]
            have hs : Submodule.Quotient.mk (Finsupp.single v (1 : ZMod 2)) = sym1 F (v 0) := by
              rw [sym1, hv]
            have h1 : Finsupp.single v c = c • Finsupp.single v (1 : ZMod 2) := by
              simp [Finsupp.smul_single]
            simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
            rw [h1, Submodule.Quotient.mk_smul, map_smul, map_smul, hs,
              milnorK2OneToSquareClasses_sym1, squareClassesToMilnorK2One_mk])

end DegreeOne

/-!
## Degree one on the Galois side, and a Lean-checked reduction to Kummer theory

In degree `1` the continuous cochain description makes `H^1(F, ℤ/2)` the group of continuous
homomorphisms `Gal(F^sep/F) → ℤ/2` (there are no coboundaries in degree one, because the
differential out of degree zero vanishes for trivial coefficients).

Combining this with `k^M_1(F) = Fˣ/(Fˣ)²` reduces the degree-one Milnor conjecture to Kummer
theory: `NormResidueIso F 1` holds if and only if `Fˣ/(Fˣ)²` is isomorphic to the group of
continuous homomorphisms `Gal(F^sep/F) → ℤ/2`.
-/

section GaloisDegreeOne

variable (F : Type) [Field F]

lemma dd_one_apply (G : Type) [Group G] (f : (Fin 1 → G) → ZMod 2) (g : Fin 2 → G) :
    dd G 1 f g = f (fun _ => g 1) + (f (fun _ => g 0 * g 1) + f (fun _ => g 0)) := by
  rw [dd_apply, Fin.sum_univ_two]
  have h0 : (fun i : Fin 1 => g i.succ) = fun _ => g 1 := by
    funext i; rw [Subsingleton.elim i 0]; rfl
  have h1 : Fin.contractNth 0 (· * ·) g = fun _ => g 0 * g 1 := by
    funext k; rw [Subsingleton.elim k 0]; simp [Fin.contractNth]
  have h2 : Fin.contractNth 1 (· * ·) g = fun _ => g 0 := by
    funext k; rw [Subsingleton.elim k 0]; simp [Fin.contractNth]
  rw [h0, h1, h2]

/-- The `ℤ/2`-vector space of continuous homomorphisms `Gal(F^sep/F) → ℤ/2`. -/
def contHom1 : Submodule (ZMod 2) (AbsGal F → ZMod 2) where
  carrier := {f | IsLocallyConstant f ∧ ∀ g h, f (g * h) = f g + f h}
  add_mem' := fun {f f'} hf hf' =>
    ⟨IsLocallyConstant.comp₂ hf.1 hf'.1 (· + ·), fun g h => by
      simp only [Pi.add_apply, hf.2, hf'.2]; abel⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ _ => by simp⟩
  smul_mem' := fun c f hf =>
    ⟨hf.1.comp (c * ·), fun g h => by simp only [Pi.smul_apply, smul_eq_mul, hf.2]; ring⟩

/-- Degree-one cochains are the same thing as functions on the Galois group. -/
def ev1 : ((Fin 1 → AbsGal F) → ZMod 2) ≃ₗ[ZMod 2] (AbsGal F → ZMod 2) where
  toFun f g := f (fun _ => g)
  invFun u v := u (v 0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by
    funext v
    show f (fun _ => v 0) = f v
    congr 1
    funext j
    rw [Subsingleton.elim j 0]
  right_inv u := rfl

lemma mem_contCocycles_one_iff (f : (Fin 1 → AbsGal F) → ZMod 2) :
    f ∈ contCocycles F 1 ↔ ev1 F f ∈ contHom1 F := by
  constructor
  · rintro ⟨hlc, hker⟩
    refine ⟨hlc.comp_continuous (continuous_pi fun _ => continuous_id), fun a b => ?_⟩
    have h := congrFun hker ![a, b]
    rw [dd_one_apply] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h
    have h2 : f (fun _ => a * b) + (f (fun _ => a) + f (fun _ => b)) = 0 := by
      rw [← h]; abel
    have h3 := congrArg (fun x => x + (f (fun _ => a) + f (fun _ => b))) h2
    simp only [zero_add] at h3
    rw [add_assoc, add_self_eq_zero_zmod2, add_zero] at h3
    exact h3
  · rintro ⟨hlc, hhom⟩
    have hf : IsLocallyConstant f := by
      have : f = (ev1 F f) ∘ (fun v : Fin 1 → AbsGal F => v 0) := by
        funext v
        show f v = f (fun _ => v 0)
        congr 1
        funext j
        rw [Subsingleton.elim j 0]
      rw [this]
      exact hlc.comp_continuous (continuous_apply 0)
    refine ⟨hf, ?_⟩
    funext g
    rw [dd_one_apply]
    have h := hhom (g 0) (g 1)
    show f (fun _ => g 1) + (f (fun _ => g 0 * g 1) + f (fun _ => g 0)) = 0
    rw [show f (fun _ => g 0 * g 1) = f (fun _ => g 0) + f (fun _ => g 1) from h]
    rw [show f (fun _ => g 1) + (f (fun _ => g 0) + f (fun _ => g 1) + f (fun _ => g 0))
        = (f (fun _ => g 1) + f (fun _ => g 1)) + (f (fun _ => g 0) + f (fun _ => g 0)) by abel,
      add_self_eq_zero_zmod2, add_self_eq_zero_zmod2, add_zero]

lemma contCoboundaries_one : contCoboundaries F 1 = ⊥ := by
  refine eq_bot_iff.2 ?_
  rintro _ ⟨f, -, rfl⟩
  simpa using dd_zero_eq_zero F f

lemma map_contCocycles_one :
    Submodule.map (ev1 F).toLinearMap (contCocycles F 1) = contHom1 F := by
  ext u
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact (mem_contCocycles_one_iff F f).1 hf
  · intro hu
    refine ⟨(ev1 F).symm u, ?_, by simp⟩
    have h : ev1 F ((ev1 F).symm u) = u := by simp
    exact (mem_contCocycles_one_iff F _).2 (by rw [h]; exact hu)

/-- **Mod-2 Galois cohomology in degree one is the group of continuous homomorphisms
`Gal(F^sep/F) → ℤ/2`.** -/
noncomputable def galoisCohomologyMod2OneEquiv :
    GaloisCohomologyMod2 F 1 ≃ₗ[ZMod 2] contHom1 F :=
  (Submodule.quotEquivOfEqBot _ (by rw [contCoboundaries_one]; simp)).trans
    (((ev1 F).submoduleMap (contCocycles F 1)).trans
      (LinearEquiv.ofEq _ _ (map_contCocycles_one F)))

/-- **A Lean-checked reduction**: the Milnor conjecture in degree one for `F` is equivalent to
Kummer theory for `F`, i.e. to the statement that the square classes `Fˣ/(Fˣ)²` are isomorphic to
the continuous characters `Gal(F^sep/F) → ℤ/2`. -/
theorem normResidueIso_one_iff_kummer :
    NormResidueIso F 1 ↔ Nonempty (SquareClasses F ≃ₗ[ZMod 2] contHom1 F) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨((milnorK2OneEquiv F).symm.trans e).trans (galoisCohomologyMod2OneEquiv F)⟩
  · rintro ⟨e⟩
    exact ⟨((milnorK2OneEquiv F).trans e).trans (galoisCohomologyMod2OneEquiv F).symm⟩

end GaloisDegreeOne

end Frontier

import RequestProject.Core

/-!
# Kummer theory in degree one

The degree-one Milnor conjecture is Kummer theory: the square classes `Fˣ/(Fˣ)²` of a field of
characteristic `≠ 2` are the continuous characters `Gal(F^sep/F) → ℤ/2`.

This file constructs the Kummer character of a unit and proves that the resulting map
`Fˣ/(Fˣ)² → H^1(F, ℤ/2)` is a well-defined injective `ℤ/2`-linear map.
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

namespace Frontier

section Kummer

variable {F : Type} [Field F]

open scoped Classical in
/-- The Kummer character attached to an element `s` of the separable closure: it records, for each
element of the absolute Galois group, whether `s` is moved. -/
noncomputable def kummerCharOf (s : SeparableClosure F) : AbsGal F → ZMod 2 :=
  fun σ => if σ s = s then 0 else 1

lemma sigma_eq_or_eq_neg {s : SeparableClosure F}
    (hs : ∃ a : F, s ^ 2 = algebraMap F (SeparableClosure F) a) (σ : AbsGal F) :
    σ s = s ∨ σ s = -s := by
  obtain ⟨a, ha⟩ := hs
  have h : (σ s) ^ 2 = s ^ 2 := by
    rw [← map_pow, ha, AlgEquiv.commutes]
  have h0 : (σ s - s) * (σ s + s) = 0 := by ring_nf; linear_combination h
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact Or.inl (by linear_combination h1)
  · exact Or.inr (by linear_combination h1)

lemma kummerCharOf_eq_zero_iff (s : SeparableClosure F) (σ : AbsGal F) :
    kummerCharOf s σ = 0 ↔ σ s = s := by
  unfold kummerCharOf
  split_ifs with h
  · simp [h]
  · simp [h]

lemma kummerCharOf_mul_eq {s : SeparableClosure F}
    (hs : ∃ a : F, s ^ 2 = algebraMap F (SeparableClosure F) a) (σ τ : AbsGal F) :
    kummerCharOf s (σ * τ) = kummerCharOf s σ + kummerCharOf s τ := by
  by_cases hz : s = -s
  · have hall : ∀ ρ : AbsGal F, ρ s = s := by
      intro ρ
      rcases sigma_eq_or_eq_neg hs ρ with h | h
      · exact h
      · rw [h, ← hz]
    simp [kummerCharOf, hall]
  · have hne : (-s) ≠ s := fun h => hz h.symm
    have hmul : (σ * τ) s = σ (τ s) := rfl
    rcases sigma_eq_or_eq_neg hs σ with hσ | hσ <;> rcases sigma_eq_or_eq_neg hs τ with hτ | hτ
    · simp [kummerCharOf, hmul, hτ, hσ]
    · have h : (σ * τ) s = -s := by rw [hmul, hτ, map_neg, hσ]
      simp [kummerCharOf, h, hτ, hσ, hne]
    · have h : (σ * τ) s = -s := by rw [hmul, hτ, hσ]
      simp [kummerCharOf, h, hτ, hσ, hne]
    · have h : (σ * τ) s = s := by rw [hmul, hτ, map_neg, hσ, neg_neg]
      simp [kummerCharOf, h, hτ, hσ, hne]
      rfl

lemma kummerCharOf_isLocallyConstant (s : SeparableClosure F) :
    IsLocallyConstant (kummerCharOf s) := by
  have hopen : IsOpen ((MulAction.stabilizer (AbsGal F) s : Subgroup (AbsGal F)) :
      Set (AbsGal F)) := stabilizer_isOpen_of_isIntegral s
  have hset0 : {σ : AbsGal F | kummerCharOf s σ = 0}
      = ((MulAction.stabilizer (AbsGal F) s : Subgroup (AbsGal F)) : Set (AbsGal F)) := by
    ext σ
    simp only [Set.mem_setOf_eq, kummerCharOf_eq_zero_iff, SetLike.mem_coe,
      MulAction.mem_stabilizer_iff]
    rfl
  have hset1 : {σ : AbsGal F | kummerCharOf s σ = 1}
      = ((MulAction.stabilizer (AbsGal F) s : Subgroup (AbsGal F)) : Set (AbsGal F))ᶜ := by
    ext σ
    rw [← hset0]
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    unfold kummerCharOf
    split_ifs with h
    · simp
    · simp
  have hopen1 : IsOpen {σ : AbsGal F | kummerCharOf s σ = 1} := by
    rw [hset1]
    exact (OpenSubgroup.isClosed ⟨MulAction.stabilizer (AbsGal F) s, hopen⟩).isOpen_compl
  have hopen0 : IsOpen {σ : AbsGal F | kummerCharOf s σ = 0} := by rw [hset0]; exact hopen
  intro U
  have hval : ∀ σ : AbsGal F, kummerCharOf s σ = 0 ∨ kummerCharOf s σ = 1 := by
    intro σ
    unfold kummerCharOf
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  by_cases h0 : (0 : ZMod 2) ∈ U <;> by_cases h1 : (1 : ZMod 2) ∈ U
  · have : kummerCharOf s ⁻¹' U = Set.univ := by
      ext σ
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      rcases hval σ with h | h <;> rw [h] <;> assumption
    rw [this]; exact isOpen_univ
  · have : kummerCharOf s ⁻¹' U = {σ : AbsGal F | kummerCharOf s σ = 0} := by
      ext σ
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · intro hmem
        rcases hval σ with h | h
        · exact h
        · exact absurd (h ▸ hmem) h1
      · intro h; rw [h]; exact h0
    rw [this]; exact hopen0
  · have : kummerCharOf s ⁻¹' U = {σ : AbsGal F | kummerCharOf s σ = 1} := by
      ext σ
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · intro hmem
        rcases hval σ with h | h
        · exact absurd (h ▸ hmem) h0
        · exact h
      · intro h; rw [h]; exact h1
    rw [this]; exact hopen1
  · have : kummerCharOf s ⁻¹' U = ∅ := by
      ext σ
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      intro hmem
      rcases hval σ with h | h
      · exact h0 (h ▸ hmem)
      · exact h1 (h ▸ hmem)
    rw [this]; exact isOpen_empty

lemma kummerCharOf_mem_contHom1 {s : SeparableClosure F}
    (hs : ∃ a : F, s ^ 2 = algebraMap F (SeparableClosure F) a) :
    kummerCharOf s ∈ contHom1 F :=
  ⟨kummerCharOf_isLocallyConstant s, kummerCharOf_mul_eq hs⟩

lemma two_ne_zero_sepClosure (h2 : (2 : F) ≠ 0) : (2 : SeparableClosure F) ≠ 0 := by
  intro h
  apply h2
  have hmap : algebraMap F (SeparableClosure F) 2 = 0 := by rw [map_ofNat]; exact h
  exact (map_eq_zero_iff _ (algebraMap F (SeparableClosure F)).injective).1 hmap

lemma ringChar_sepClosure_ne_two (h2 : (2 : F) ≠ 0) : ringChar (SeparableClosure F) ≠ 2 := by
  intro hc
  apply two_ne_zero_sepClosure h2
  have h := (ringChar.spec (SeparableClosure F) 2).2 (by rw [hc])
  simpa using h

lemma ne_neg_self {s : SeparableClosure F} (h2 : (2 : F) ≠ 0) (hs : s ≠ 0) : s ≠ -s := by
  intro h
  apply hs
  have h0 : (2 : SeparableClosure F) * s = 0 := by
    have : s + s = 0 := by
      nth_rewrite 2 [h]
      ring
    linear_combination this
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact absurd h1 (two_ne_zero_sepClosure h2)
  · exact h1

lemma kummerCharOf_eq_one_iff {s : SeparableClosure F} (h2 : (2 : F) ≠ 0) (hs0 : s ≠ 0)
    (hs : ∃ a : F, s ^ 2 = algebraMap F (SeparableClosure F) a) (σ : AbsGal F) :
    kummerCharOf s σ = 1 ↔ σ s = -s := by
  constructor
  · intro h
    rcases sigma_eq_or_eq_neg hs σ with hσ | hσ
    · rw [(kummerCharOf_eq_zero_iff s σ).2 hσ] at h
      exact absurd h (by decide)
    · exact hσ
  · intro hσ
    unfold kummerCharOf
    rw [if_neg]
    rw [hσ]
    exact fun h => (ne_neg_self h2 hs0) h.symm

lemma kummerCharOf_neg (s : SeparableClosure F) : kummerCharOf (-s) = kummerCharOf s := by
  funext σ
  have hcond : (σ (-s) = -s) ↔ (σ s = s) := by
    constructor
    · intro h
      rw [map_neg] at h
      exact neg_inj.1 h
    · intro h
      rw [map_neg, h]
  simp only [kummerCharOf]
  by_cases hh : σ s = s
  · rw [if_pos (hcond.2 hh), if_pos hh]
  · rw [if_neg (fun h => hh (hcond.1 h)), if_neg hh]

lemma kummerCharOf_eq_of_sq_eq {s t : SeparableClosure F} (h : s ^ 2 = t ^ 2) :
    kummerCharOf s = kummerCharOf t := by
  have h0 : (t - s) * (t + s) = 0 := by linear_combination -h
  rcases mul_eq_zero.1 h0 with h1 | h1
  · have : t = s := by linear_combination h1
    rw [this]
  · have : t = -s := by linear_combination h1
    rw [this, kummerCharOf_neg]

lemma kummerCharOf_mul {s t : SeparableClosure F} (h2 : (2 : F) ≠ 0) (hs0 : s ≠ 0) (ht0 : t ≠ 0)
    (hs : ∃ a : F, s ^ 2 = algebraMap F (SeparableClosure F) a)
    (ht : ∃ a : F, t ^ 2 = algebraMap F (SeparableClosure F) a) :
    kummerCharOf (s * t) = kummerCharOf s + kummerCharOf t := by
  have hst : ∃ a : F, (s * t) ^ 2 = algebraMap F (SeparableClosure F) a := by
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := ht
    exact ⟨a * b, by rw [mul_pow, ha, hb, map_mul]⟩
  have hst0 : s * t ≠ 0 := mul_ne_zero hs0 ht0
  funext σ
  rcases sigma_eq_or_eq_neg hs σ with hσs | hσs <;> rcases sigma_eq_or_eq_neg ht σ with hσt | hσt
  · have h : σ (s * t) = s * t := by rw [map_mul, hσs, hσt]
    rw [Pi.add_apply, (kummerCharOf_eq_zero_iff _ σ).2 h, (kummerCharOf_eq_zero_iff _ σ).2 hσs,
      (kummerCharOf_eq_zero_iff _ σ).2 hσt]
    decide
  · have h : σ (s * t) = -(s * t) := by rw [map_mul, hσs, hσt]; ring
    rw [Pi.add_apply, (kummerCharOf_eq_one_iff h2 hst0 hst σ).2 h,
      (kummerCharOf_eq_zero_iff _ σ).2 hσs, (kummerCharOf_eq_one_iff h2 ht0 ht σ).2 hσt]
    decide
  · have h : σ (s * t) = -(s * t) := by rw [map_mul, hσs, hσt]; ring
    rw [Pi.add_apply, (kummerCharOf_eq_one_iff h2 hst0 hst σ).2 h,
      (kummerCharOf_eq_one_iff h2 hs0 hs σ).2 hσs, (kummerCharOf_eq_zero_iff _ σ).2 hσt]
    decide
  · have h : σ (s * t) = s * t := by rw [map_mul, hσs, hσt]; ring
    rw [Pi.add_apply, (kummerCharOf_eq_zero_iff _ σ).2 h,
      (kummerCharOf_eq_one_iff h2 hs0 hs σ).2 hσs, (kummerCharOf_eq_one_iff h2 ht0 ht σ).2 hσt]
    decide

lemma kummerCharOf_algebraMap (y : F) : kummerCharOf (algebraMap F (SeparableClosure F) y) = 0 := by
  funext σ
  rw [(kummerCharOf_eq_zero_iff _ σ).2 (AlgEquiv.commutes σ y)]
  rfl

end Kummer

section KummerMap

variable {F : Type} [Field F] (h2 : (2 : F) ≠ 0)

include h2 in
lemma exists_sqrt (a : Fˣ) :
    ∃ s : SeparableClosure F, s ≠ 0 ∧ s ^ 2 = algebraMap F (SeparableClosure F) (a : F) := by
  obtain ⟨b, hb⟩ := exists_sq (SeparableClosure F) (ringChar_sepClosure_ne_two h2)
    (Units.map (algebraMap F (SeparableClosure F)).toMonoidHom a)
  refine ⟨(b : SeparableClosure F), b.ne_zero, ?_⟩
  have hb' := congrArg Units.val hb
  simpa [pow_two] using hb'

/-- A chosen square root of a unit inside the separable closure. -/
noncomputable def kummerRoot (a : Fˣ) : SeparableClosure F := (exists_sqrt h2 a).choose

lemma kummerRoot_ne_zero (a : Fˣ) : kummerRoot h2 a ≠ 0 := (exists_sqrt h2 a).choose_spec.1

lemma kummerRoot_sq (a : Fˣ) :
    (kummerRoot h2 a) ^ 2 = algebraMap F (SeparableClosure F) (a : F) :=
  (exists_sqrt h2 a).choose_spec.2

lemma kummerRoot_sq_mem (a : Fˣ) :
    ∃ c : F, (kummerRoot h2 a) ^ 2 = algebraMap F (SeparableClosure F) c :=
  ⟨(a : F), kummerRoot_sq h2 a⟩

/-- The Kummer character of a unit: the continuous character `σ ↦ σ(√a)/√a`. -/
noncomputable def kummerChar (a : Fˣ) : AbsGal F → ZMod 2 := kummerCharOf (kummerRoot h2 a)

lemma kummerChar_mem (a : Fˣ) : kummerChar h2 a ∈ contHom1 F :=
  kummerCharOf_mem_contHom1 (kummerRoot_sq_mem h2 a)

lemma kummerChar_mul (a b : Fˣ) :
    kummerChar h2 (a * b) = kummerChar h2 a + kummerChar h2 b := by
  have hsq : (kummerRoot h2 (a * b)) ^ 2 = (kummerRoot h2 a * kummerRoot h2 b) ^ 2 := by
    rw [kummerRoot_sq, mul_pow, kummerRoot_sq, kummerRoot_sq, ← map_mul]
    norm_cast
  rw [kummerChar, kummerCharOf_eq_of_sq_eq hsq,
    kummerCharOf_mul h2 (kummerRoot_ne_zero h2 a) (kummerRoot_ne_zero h2 b)
      (kummerRoot_sq_mem h2 a) (kummerRoot_sq_mem h2 b)]
  rfl

lemma kummerChar_sq (c : Fˣ) : kummerChar h2 (c ^ 2) = 0 := by
  have hsq : (kummerRoot h2 (c ^ 2)) ^ 2
      = (algebraMap F (SeparableClosure F) (c : F)) ^ 2 := by
    rw [kummerRoot_sq, ← map_pow]
    norm_cast
  rw [kummerChar, kummerCharOf_eq_of_sq_eq hsq, kummerCharOf_algebraMap]

lemma kummerChar_one : kummerChar h2 1 = 0 := by
  simpa using kummerChar_sq h2 1

/-- The Kummer character as a homomorphism out of `Fˣ`. -/
noncomputable def kummerHom : Fˣ →* Multiplicative (contHom1 F) where
  toFun a := Multiplicative.ofAdd ⟨kummerChar h2 a, kummerChar_mem h2 a⟩
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    exact Subtype.ext (kummerChar_one h2)
  map_mul' a b := by
    apply congrArg Multiplicative.ofAdd
    exact Subtype.ext (kummerChar_mul h2 a b)

/-- **The Kummer map** `Fˣ/(Fˣ)² → H^1(F, ℤ/2)`, landing in the continuous characters. -/
noncomputable def kummerMap : SquareClasses F →ₗ[ZMod 2] contHom1 F :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun x =>
        Multiplicative.toAdd
          (QuotientGroup.lift _ (kummerHom h2)
            (by
              rintro _ ⟨c, rfl⟩
              apply congrArg Multiplicative.ofAdd
              exact Subtype.ext (kummerChar_sq h2 c)) (Additive.toMul x))
      map_zero' := by simp
      map_add' := fun x y => by
        have h : Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y := rfl
        rw [h, map_mul]
        rfl }

lemma kummerMap_mk (a : Fˣ) :
    kummerMap h2 (Additive.ofMul (QuotientGroup.mk a)) = ⟨kummerChar h2 a, kummerChar_mem h2 a⟩ :=
  rfl

lemma kummerMap_eq_zero (x : SquareClasses F) (hx : kummerMap h2 x = 0) : x = 0 := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    have hchar : kummerChar h2 a = 0 := congrArg Subtype.val (kummerMap_mk h2 a ▸ hx)
    have hfix : ∀ σ : AbsGal F, σ (kummerRoot h2 a) = kummerRoot h2 a := by
      intro σ
      exact (kummerCharOf_eq_zero_iff _ σ).1 (congrFun hchar σ)
    obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (kummerRoot h2 a)).2 hfix
    have hy2 : algebraMap F (SeparableClosure F) (y ^ 2) = algebraMap F _ (a : F) := by
      rw [map_pow, hy, kummerRoot_sq]
    have hy2' : y ^ 2 = (a : F) :=
      (algebraMap F (SeparableClosure F)).injective hy2
    have hyne : y ≠ 0 := by
      intro h
      apply a.ne_zero
      rw [← hy2', h]
      ring
    have : (Units.mk0 y hyne) ^ 2 = a := by
      ext
      simpa using hy2'
    show Additive.ofMul (QuotientGroup.mk a) = 0
    have hmk : (QuotientGroup.mk a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ⟨Units.mk0 y hyne, this⟩
    simp [hmk]

/-- **The Kummer map is injective**: a unit whose Kummer character is trivial is a square. -/
theorem kummerMap_injective : Function.Injective (kummerMap h2) := by
  intro x y hxy
  have h : kummerMap h2 (x - y) = 0 := by
    have hsub := map_sub (kummerMap h2) x y
    rw [hsub, hxy, sub_self]
  exact sub_eq_zero.1 (kummerMap_eq_zero h2 (x - y) h)

end KummerMap

/-!
## Surjectivity of the Kummer map
-/

section Surjectivity

variable {F : Type} [Field F]

/-- A continuous character of the absolute Galois group, as a group homomorphism. -/
def charHom (χ : contHom1 F) : AbsGal F →* Multiplicative (ZMod 2) where
  toFun σ := Multiplicative.ofAdd ((χ : AbsGal F → ZMod 2) σ)
  map_one' := by
    have h := χ.2.2 1 1
    rw [mul_one] at h
    have h0 : (χ : AbsGal F → ZMod 2) 1 = 0 := by
      have h1 : (χ : AbsGal F → ZMod 2) 1 + 0 = (χ : AbsGal F → ZMod 2) 1
          + (χ : AbsGal F → ZMod 2) 1 := by simpa using h
      exact (add_left_cancel h1).symm
    exact congrArg Multiplicative.ofAdd h0
  map_mul' σ τ := by
    have h := χ.2.2 σ τ
    exact congrArg Multiplicative.ofAdd h

lemma charHom_apply (χ : contHom1 F) (σ : AbsGal F) :
    charHom χ σ = Multiplicative.ofAdd ((χ : AbsGal F → ZMod 2) σ) := rfl

lemma mem_ker_charHom_iff (χ : contHom1 F) (σ : AbsGal F) :
    σ ∈ (charHom χ).ker ↔ (χ : AbsGal F → ZMod 2) σ = 0 := by
  simp [MonoidHom.mem_ker, charHom_apply]

lemma ker_charHom_isOpen (χ : contHom1 F) :
    IsOpen (((charHom χ).ker : Subgroup (AbsGal F)) : Set (AbsGal F)) := by
  have hset : (((charHom χ).ker : Subgroup (AbsGal F)) : Set (AbsGal F))
      = (χ : AbsGal F → ZMod 2) ⁻¹' {0} := by
    ext σ
    simpa using mem_ker_charHom_iff χ σ
  rw [hset]
  exact χ.2.1 {0}

/-- The `ℤ/2`-valued characters take only the values `0` and `1`. -/
lemma char_eq_zero_or_one (χ : contHom1 F) (σ : AbsGal F) :
    (χ : AbsGal F → ZMod 2) σ = 0 ∨ (χ : AbsGal F → ZMod 2) σ = 1 := by
  generalize (χ : AbsGal F → ZMod 2) σ = x
  revert x
  decide

lemma ker_charHom_index (χ : contHom1 F) (hne : (χ : AbsGal F → ZMod 2) ≠ 0) :
    ((charHom χ).ker).index = 2 := by
  rw [Subgroup.index_ker]
  obtain ⟨σ, hσ⟩ : ∃ σ, (χ : AbsGal F → ZMod 2) σ = 1 := by
    by_contra hc
    push_neg at hc
    apply hne
    funext σ
    rcases char_eq_zero_or_one χ σ with h | h
    · exact h
    · exact absurd h (hc σ)
  have hrange : (charHom χ).range = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hxx : x = Multiplicative.ofAdd (Multiplicative.toAdd x) := rfl
    have hx : Multiplicative.toAdd x = 0 ∨ Multiplicative.toAdd x = 1 := by
      generalize Multiplicative.toAdd x = t
      revert t
      decide
    rcases hx with h | h
    · refine ⟨1, ?_⟩
      rw [map_one, hxx, h]
      rfl
    · refine ⟨σ, ?_⟩
      rw [charHom_apply, hσ, hxx, h]
  rw [hrange]
  simp

lemma adjoin_eq_of_finrank_two {L : IntermediateField F (SeparableClosure F)}
    (hL : Module.finrank F L = 2) {y : SeparableClosure F} (hy : y ∈ L)
    (hy' : y ∉ (⊥ : IntermediateField F (SeparableClosure F))) :
    IntermediateField.adjoin F {y} = L := by
  have hfin : FiniteDimensional F L := by
    apply FiniteDimensional.of_finrank_pos (K := F) (V := L)
    rw [hL]
    norm_num
  have hle : IntermediateField.adjoin F {y} ≤ L := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    rcases hz with rfl
    exact hy
  have hfin' : FiniteDimensional F (IntermediateField.adjoin F {y}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  have hne1 : Module.finrank F (IntermediateField.adjoin F {y}) ≠ 1 := by
    intro h
    apply hy'
    have hbot : IntermediateField.adjoin F {y} = ⊥ :=
      IntermediateField.finrank_eq_one_iff.1 h
    have : y ∈ IntermediateField.adjoin F {y} :=
      IntermediateField.subset_adjoin F {y} rfl
    rwa [hbot] at this
  have hpos : 0 < Module.finrank F (IntermediateField.adjoin F {y}) :=
    Module.finrank_pos
  refine IntermediateField.eq_of_le_of_finrank_le hle ?_
  rw [hL]
  omega

lemma exists_mem_not_mem_bot (L : IntermediateField F (SeparableClosure F))
    (hL : Module.finrank F L = 2) :
    ∃ x : SeparableClosure F, x ∈ L ∧ x ∉ (⊥ : IntermediateField F (SeparableClosure F)) := by
  by_contra hc
  push_neg at hc
  have hbot : L = ⊥ := by
    refine le_antisymm (fun x hx => hc x hx) ?_
    exact bot_le
  rw [hbot] at hL
  rw [IntermediateField.finrank_bot] at hL
  omega

lemma exists_generator_sq_mem (h2 : (2 : F) ≠ 0)
    (L : IntermediateField F (SeparableClosure F)) (hL : Module.finrank F L = 2) :
    ∃ y : SeparableClosure F, y ∈ L ∧ y ∉ (⊥ : IntermediateField F (SeparableClosure F)) ∧
      ∃ c : F, y ^ 2 = algebraMap F (SeparableClosure F) c := by
  obtain ⟨x, hxL, hxb⟩ := exists_mem_not_mem_bot L hL
  have hadj : IntermediateField.adjoin F {x} = L := adjoin_eq_of_finrank_two hL hxL hxb
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hdeg : (minpoly F x).natDegree = 2 := by
    have h := IntermediateField.adjoin.finrank hint
    rw [hadj, hL] at h
    exact h.symm
  have hmonic : (minpoly F x).Monic := minpoly.monic hint
  have haeval : (Polynomial.aeval x) (minpoly F x) = 0 := minpoly.aeval F x
  set b := (minpoly F x).coeff 1 with hb
  set c := (minpoly F x).coeff 0 with hc
  have hexp : x ^ 2 + algebraMap F (SeparableClosure F) b * x
      + algebraMap F (SeparableClosure F) c = 0 := by
    rw [Polynomial.aeval_eq_sum_range, hdeg] at haeval
    have hlead : (minpoly F x).coeff 2 = 1 := by
      have := hmonic.coeff_natDegree
      rwa [hdeg] at this
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hlead, Algebra.smul_def,
      pow_zero, pow_one, mul_one, map_one, one_mul] at haeval
    rw [← haeval]
    ring
  refine ⟨x + algebraMap F (SeparableClosure F) (b / 2), ?_, ?_, ?_⟩
  · exact add_mem hxL (IntermediateField.algebraMap_mem L _)
  · intro hmem
    apply hxb
    have : x = (x + algebraMap F (SeparableClosure F) (b / 2))
        - algebraMap F (SeparableClosure F) (b / 2) := by ring
    rw [this]
    exact sub_mem hmem (IntermediateField.algebraMap_mem _ _)
  · refine ⟨b ^ 2 / 4 - c, ?_⟩
    have h2' : (2 : F) ≠ 0 := h2
    have hb2 : algebraMap F (SeparableClosure F) (b / 2) * 2 = algebraMap F _ b := by
      rw [← map_ofNat (algebraMap F (SeparableClosure F)) 2, ← map_mul]
      congr 1
      field_simp
    have hsq : algebraMap F (SeparableClosure F) (b ^ 2 / 4)
        = (algebraMap F (SeparableClosure F) (b / 2)) ^ 2 := by
      rw [← map_pow]
      congr 1
      rw [div_pow]
      norm_num
    rw [map_sub, hsq]
    have : (x + algebraMap F (SeparableClosure F) (b / 2)) ^ 2
        = x ^ 2 + algebraMap F (SeparableClosure F) (b / 2) * 2 * x
          + (algebraMap F (SeparableClosure F) (b / 2)) ^ 2 := by ring
    rw [this, hb2]
    linear_combination hexp

lemma exists_unit_kummerChar_eq (h2 : (2 : F) ≠ 0) (χ : contHom1 F)
    (hne : (χ : AbsGal F → ZMod 2) ≠ 0) :
    ∃ a : Fˣ, kummerChar h2 a = (χ : AbsGal F → ZMod 2) := by
  have hopen := ker_charHom_isOpen χ
  have hclosed : IsClosed (((charHom χ).ker : Subgroup (AbsGal F)) : Set (AbsGal F)) :=
    OpenSubgroup.isClosed ⟨(charHom χ).ker, hopen⟩
  let Hc : ClosedSubgroup (AbsGal F) := ⟨(charHom χ).ker, hclosed⟩
  have hfix : (IntermediateField.fixedField ((charHom χ).ker)).fixingSubgroup
      = (charHom χ).ker := InfiniteGalois.fixingSubgroup_fixedField Hc
  have hrank : Module.finrank F (IntermediateField.fixedField ((charHom χ).ker)) = 2 := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index, hfix]
    exact ker_charHom_index χ hne
  obtain ⟨y, hyL, hyb, c, hc⟩ :=
    exists_generator_sq_mem h2 (IntermediateField.fixedField ((charHom χ).ker)) hrank
  have hadj : IntermediateField.adjoin F {y} = IntermediateField.fixedField ((charHom χ).ker) :=
    adjoin_eq_of_finrank_two hrank hyL hyb
  have hy0 : y ≠ 0 := by
    intro h
    exact hyb (h ▸ zero_mem _)
  have hc0 : c ≠ 0 := by
    intro h
    apply hy0
    have hy2 : y ^ 2 = 0 := by rw [hc, h, map_zero]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hy2
  refine ⟨Units.mk0 c hc0, ?_⟩
  have hsq : (kummerRoot h2 (Units.mk0 c hc0)) ^ 2 = y ^ 2 := by
    rw [kummerRoot_sq, hc]
    simp
  rw [kummerChar, kummerCharOf_eq_of_sq_eq hsq]
  funext σ
  have hiff : σ y = y ↔ (χ : AbsGal F → ZMod 2) σ = 0 := by
    constructor
    · intro h
      have hmem : σ ∈ (IntermediateField.adjoin F {y}).fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        exact (IntermediateField.forall_mem_adjoin_smul_eq_self_iff F σ).2
          (by rintro w rfl; exact h)
      rw [hadj, hfix] at hmem
      exact (mem_ker_charHom_iff χ σ).1 hmem
    · intro h
      have hmem : σ ∈ (charHom χ).ker := (mem_ker_charHom_iff χ σ).2 h
      rw [← hfix, IntermediateField.mem_fixingSubgroup_iff] at hmem
      exact hmem y hyL
  have hval : kummerCharOf y σ = 0 ∨ kummerCharOf y σ = 1 := by
    unfold kummerCharOf
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases char_eq_zero_or_one χ σ with h | h
  · rw [h]
    exact (kummerCharOf_eq_zero_iff y σ).2 (hiff.2 h)
  · rcases hval with hv | hv
    · exfalso
      have hz := hiff.1 ((kummerCharOf_eq_zero_iff y σ).1 hv)
      rw [hz] at h
      exact absurd h (by decide)
    · rw [hv, h]

theorem kummerMap_surjective (h2 : (2 : F) ≠ 0) : Function.Surjective (kummerMap h2) := by
  intro χ
  by_cases hzero : (χ : AbsGal F → ZMod 2) = 0
  · refine ⟨0, ?_⟩
    rw [map_zero]
    exact Subtype.ext hzero.symm
  · obtain ⟨a, ha⟩ := exists_unit_kummerChar_eq h2 χ hzero
    exact ⟨Additive.ofMul (QuotientGroup.mk a), Subtype.ext ha⟩

/-- **Kummer theory**: for a field of characteristic `≠ 2`, the square classes `Fˣ/(Fˣ)²` are
exactly the continuous characters `Gal(F^sep/F) → ℤ/2`. -/
noncomputable def kummerEquiv (h2 : (2 : F) ≠ 0) : SquareClasses F ≃ₗ[ZMod 2] contHom1 F :=
  LinearEquiv.ofBijective (kummerMap h2) ⟨kummerMap_injective h2, kummerMap_surjective h2⟩

/-- **The Milnor conjecture in degree one**, for an arbitrary field of characteristic `≠ 2`: mod-2
Milnor K-theory `k^M_1(F) = Fˣ/(Fˣ)²` agrees with mod-2 Galois cohomology `H^1(F, ℤ/2)`. -/
theorem normResidueIso_one (h2 : (2 : F) ≠ 0) : NormResidueIso F 1 :=
  (normResidueIso_one_iff_kummer F).2 ⟨kummerEquiv h2⟩

end Surjectivity

end Frontier

/-
# Voevodsky Milnor
Category: Frontier — Fields Medal Work
Target: Frontier.voevodsky_milnor
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is a plain block comment because Lean requires `import` commands to precede
-- any module docstring; the same header is repeated as a module docstring below.)

import RequestProject.Kummer

/-!
# Voevodsky Milnor
Category: Frontier — Fields Medal Work
Target: Frontier.voevodsky_milnor
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- **Voevodsky's Milnor conjecture.**

`NormResidueIso F n` is the statement that mod-2 Milnor K-theory `k^M_n(F)` agrees with mod-2
Galois cohomology `H^n(F, ℤ/2)` (continuous cochain cohomology of the absolute Galois group with
trivial `ℤ/2`-coefficients).  We prove:

1. the base case `n = 0`, for an arbitrary field;
2. the case `n = 1`, for an arbitrary field of characteristic `≠ 2` (this is Kummer theory,
   proved here from scratch: `k^M_1(F) = Fˣ/(Fˣ)²` is the group of continuous characters
   `Gal(F^sep/F) → ℤ/2`); and
3. the full statement, in all degrees, for separably closed fields of characteristic `≠ 2`. -/
theorem voevodsky_milnor :
    (∀ (F : Type) [Field F], NormResidueIso F 0) ∧
    (∀ (F : Type) [Field F], ringChar F ≠ 2 → NormResidueIso F 1) ∧
    (∀ (F : Type) [Field F] [IsSepClosed F], ringChar F ≠ 2 → ∀ n : ℕ, NormResidueIso F n) :=
  ⟨fun F _ => normResidueIso_zero F,
   fun F _ h => normResidueIso_one (two_ne_zero_of_ringChar_ne_two F h),
   fun F _ _ h n => normResidueIso_of_isSepClosed F h n⟩

end Frontier

