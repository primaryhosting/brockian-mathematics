import Mathlib

/-!
# Voevodsky Milnor
Category: Frontier — Fields Medal Work
Target: Frontier.voevodsky_milnor
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` lines to precede every other command, including module
docstrings, so the header above appears immediately after the single `import Mathlib`.)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
## Overview

This file formalises the statement of the *Milnor conjecture* (a theorem of Voevodsky):
for a field `F` of characteristic `≠ 2` the mod-`2` Milnor K-theory of `F` is isomorphic to the
mod-`2` (continuous) Galois cohomology of `F`,
`k^M_n(F) ≅ H^n(Gal(F_sep/F), ℤ/2)`.

We build both sides from scratch:

* `Frontier.MilnorKMod2 F n`, the degree-`n` part of mod-`2` Milnor K-theory, presented as the
  free `ℤ/2`-vector space on `n`-tuples of units of `F` modulo multilinearity and the Steinberg
  relation;
* `Frontier.contCohomologyMod2 G n`, the continuous (inhomogeneous) cochain cohomology of a
  topological group `G` with coefficients in the trivial module `ℤ/2`, applied to the absolute
  Galois group `Gal(F_sep/F)` equipped with the Krull topology.

`Frontier.MilnorConjecture F` is the resulting statement, and the target theorem
`Frontier.voevodsky_milnor` records the parts that are proved here:

1. the base case `n = 0`, for *every* field;
2. the full conjecture for separably closed fields of characteristic `≠ 2`;
3. a Lean-checked reduction of the degree-one case to Kummer theory: the degree-one part of
   mod-`2` Milnor K-theory is `Fˣ/(Fˣ)²`, so degree-one Milnor follows from the statement that the
   Kummer map `Fˣ/(Fˣ)² → H¹(Gal(F_sep/F), ℤ/2)` is an isomorphism.
-/

universe u

namespace Frontier

/-! ## Mod-2 Milnor K-theory -/

section MilnorK

variable (F : Type u) [Field F]

/-- The defining relations of mod-`2` Milnor K-theory in degree `n`, as a subset of the free
`ℤ/2`-vector space on `n`-tuples of units: multilinearity in each slot, and the Steinberg
relation `{a₁, …, aₙ} = 0` whenever `aᵢ + a_j = 1` for some `i ≠ j`. -/
def milnorRelations (n : ℕ) : Set ((Fin n → Fˣ) →₀ ZMod 2) :=
  {x | ∃ (i : Fin n) (a b : Fˣ) (v : Fin n → Fˣ),
        x = Finsupp.single (Function.update v i (a * b)) 1
            - Finsupp.single (Function.update v i a) 1
            - Finsupp.single (Function.update v i b) 1} ∪
  {x | ∃ (v : Fin n → Fˣ) (i j : Fin n), i ≠ j ∧ (v i : F) + (v j : F) = 1 ∧
        x = Finsupp.single v 1}

/-- The subspace of relations of mod-`2` Milnor K-theory in degree `n`. -/
def milnorRelSubmodule (n : ℕ) : Submodule (ZMod 2) ((Fin n → Fˣ) →₀ ZMod 2) :=
  Submodule.span (ZMod 2) (milnorRelations F n)

/-- Mod-`2` Milnor K-theory `k^M_n(F) = K^M_n(F)/2` of a field `F` in degree `n`. -/
def MilnorKMod2 (n : ℕ) : Type u := ((Fin n → Fˣ) →₀ ZMod 2) ⧸ milnorRelSubmodule F n

noncomputable instance (n : ℕ) : AddCommGroup (MilnorKMod2 F n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ milnorRelSubmodule F n))

noncomputable instance (n : ℕ) : Module (ZMod 2) (MilnorKMod2 F n) :=
  inferInstanceAs (Module (ZMod 2) (_ ⧸ milnorRelSubmodule F n))

/-- The symbol `{a₁, …, aₙ}` in mod-`2` Milnor K-theory. -/
noncomputable def symbol {n : ℕ} (v : Fin n → Fˣ) : MilnorKMod2 F n :=
  Submodule.Quotient.mk (Finsupp.single v 1)

theorem milnorRelSubmodule_zero : milnorRelSubmodule F 0 = ⊥ := by
  rw [milnorRelSubmodule, Submodule.span_eq_bot]
  rintro x (⟨i, -⟩ | ⟨v, i, -⟩) <;> exact i.elim0

/-- Degree zero: `k^M_0(F) ≅ ℤ/2`. -/
noncomputable def milnorKMod2ZeroEquiv : MilnorKMod2 F 0 ≃ₗ[ZMod 2] ZMod 2 :=
  (Submodule.quotEquivOfEqBot _ (milnorRelSubmodule_zero F)).trans
    (Finsupp.LinearEquiv.finsuppUnique (ZMod 2) (ZMod 2) _)

/-- If every unit of `F` is a square then mod-`2` Milnor K-theory vanishes in positive degrees. -/
theorem milnorKMod2_subsingleton_of_sq {n : ℕ} (hn : 0 < n)
    (hsq : ∀ a : Fˣ, ∃ b : Fˣ, b * b = a) : Subsingleton (MilnorKMod2 F n) := by
  have hall : ∀ x : ((Fin n → Fˣ) →₀ ZMod 2), x ∈ milnorRelSubmodule F n := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => exact Submodule.zero_mem _
    | add f g hf hg => exact Submodule.add_mem _ hf hg
    | single v c =>
        have hc : Finsupp.single v c = c • Finsupp.single v (1 : ZMod 2) := by
          simp [Finsupp.smul_single]
        rw [hc]
        refine Submodule.smul_mem _ _ ?_
        obtain ⟨b, hb⟩ := hsq (v ⟨0, hn⟩)
        set i : Fin n := ⟨0, hn⟩ with hi
        have hrel : Finsupp.single (Function.update v i (b * b)) (1 : ZMod 2)
            - Finsupp.single (Function.update v i b) 1
            - Finsupp.single (Function.update v i b) 1 ∈ milnorRelSubmodule F n :=
          Submodule.subset_span (Or.inl ⟨i, b, b, v, rfl⟩)
        have h2 : Finsupp.single (Function.update v i b) (1 : ZMod 2)
            + Finsupp.single (Function.update v i b) 1 = 0 := by
          rw [← Finsupp.single_add, show (1 : ZMod 2) + 1 = 0 from rfl, Finsupp.single_zero]
        have hv : Function.update v i (b * b) = v := by
          rw [hb]; exact Function.update_eq_self _ _
        rw [hv, sub_sub, h2, sub_zero] at hrel
        exact hrel
  have hz : ∀ x : MilnorKMod2 F n, x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H y => exact (Submodule.Quotient.mk_eq_zero _).2 (hall y)
  exact ⟨fun a b => by rw [hz a, hz b]⟩

end MilnorK

/-! ## Continuous cochain cohomology with coefficients in the trivial module `ℤ/2` -/

section Cohomology

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The differential of the complex of inhomogeneous cochains with coefficients in the trivial
module `ℤ/2`.  (All signs disappear because the coefficients have characteristic two.) -/
noncomputable def cochainD (n : ℕ) :
    ((Fin n → G) → ZMod 2) →ₗ[ZMod 2] ((Fin (n + 1) → G) → ZMod 2) where
  toFun f := fun g => f (fun i => g i.succ) + ∑ j : Fin (n + 1), f (Fin.contractNth j (· * ·) g)
  map_add' f f' := by
    funext g
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    abel
  map_smul' c f := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_add]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem cochainD_apply (n : ℕ) (f : (Fin n → G) → ZMod 2) (g : Fin (n + 1) → G) :
    cochainD G n f g =
      f (fun i => g i.succ) + ∑ j : Fin (n + 1), f (Fin.contractNth j (· * ·) g) := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The differential squares to zero. -/
theorem cochainD_comp_cochainD (n : ℕ) (f : (Fin n → G) → ZMod 2) :
    cochainD G (n + 1) (cochainD G n f) = 0 := by
  have hneg : ∀ m : ℕ, ((-1 : ULift.{u} (ZMod 2))) ^ m = 1 := fun m => by
    rw [show (-1 : ULift.{u} (ZMod 2)) = 1 from by decide, one_pow]
  have hd : ∀ (m : ℕ) (f : (Fin m → G) → ZMod 2) (g : Fin (m + 1) → G),
      (inhomogeneousCochains.d (Rep.trivial (ULift.{u} (ZMod 2)) G (ULift.{u} (ZMod 2))) m).hom
        (fun x => (ULift.up (f x) : ULift.{u} (ZMod 2))) g = ULift.up (cochainD G m f g) := by
    intro m f g
    rw [inhomogeneousCochains.d_hom_apply]
    simp only [hneg, one_smul, cochainD_apply]
    rw [show (ULift.up (f (fun i => g i.succ) + ∑ j : Fin (m + 1),
          f (Fin.contractNth j (· * ·) g)) : ULift.{u} (ZMod 2)) =
        ULift.up (f (fun i => g i.succ)) +
          ULift.up (∑ j : Fin (m + 1), f (Fin.contractNth j (· * ·) g)) from rfl]
    congr 1
    exact (map_sum (AddEquiv.ulift (α := ZMod 2)).symm _ _).symm
  have h0 := groupCohomology.inhomogeneousCochains.d_comp_d (k := ULift.{u} (ZMod 2)) (G := G) n
      (Rep.trivial (ULift.{u} (ZMod 2)) G (ULift.{u} (ZMod 2)))
  funext g
  have h1 := congrFun (congrArg (fun (m : ModuleCat.of _ _ ⟶ ModuleCat.of _ _) => m.hom
      (fun x => (ULift.up (f x) : ULift.{u} (ZMod 2)))) h0) g
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero] at h1
  rw [funext (hd n f)] at h1
  rw [hd (n + 1) (cochainD G n f) g] at h1
  exact congrArg ULift.down h1

/-- The space of continuous `n`-cochains. -/
def contCochains (n : ℕ) : Submodule (ZMod 2) ((Fin n → G) → ZMod 2) where
  carrier := {f | Continuous f}
  add_mem' hf hg := Continuous.add hf hg
  zero_mem' := continuous_const
  smul_mem' c _ hf := hf.const_smul c

omit [Group G] [IsTopologicalGroup G] in
theorem mem_contCochains {n : ℕ} {f : (Fin n → G) → ZMod 2} :
    f ∈ contCochains G n ↔ Continuous f := Iff.rfl

/-- The differential preserves continuity. -/
theorem cochainD_continuous {n : ℕ} {f : (Fin n → G) → ZMod 2} (hf : Continuous f) :
    Continuous (cochainD G n f) := by
  have h1 : Continuous fun g : Fin (n + 1) → G => f (fun i => g i.succ) :=
    hf.comp (continuous_pi fun i => continuous_apply _)
  have h2 : ∀ j : Fin (n + 1),
      Continuous fun g : Fin (n + 1) → G => f (Fin.contractNth j (· * ·) g) := by
    intro j
    refine hf.comp (continuous_pi fun i => ?_)
    unfold Fin.contractNth
    split_ifs
    · exact continuous_apply _
    · exact (continuous_apply _).mul (continuous_apply _)
    · exact continuous_apply _
  exact h1.add (continuous_finset_sum _ fun j _ => h2 j)

/-- Continuous `n`-cocycles. -/
noncomputable def contCocycles (n : ℕ) : Submodule (ZMod 2) ((Fin n → G) → ZMod 2) :=
  LinearMap.ker (cochainD G n) ⊓ contCochains G n

/-- Continuous `n`-coboundaries. -/
noncomputable def contCoboundaries : (n : ℕ) → Submodule (ZMod 2) ((Fin n → G) → ZMod 2)
  | 0 => ⊥
  | (n + 1) => Submodule.map (cochainD G n) (contCochains G n)

theorem contCoboundaries_le_contCocycles (n : ℕ) :
    contCoboundaries G n ≤ contCocycles G n := by
  cases n with
  | zero => simp [contCoboundaries]
  | succ n =>
      rintro x ⟨f, hf, rfl⟩
      exact ⟨cochainD_comp_cochainD G n f, cochainD_continuous G hf⟩

/-- Continuous cochain cohomology of a topological group `G` with coefficients in the trivial
module `ℤ/2`. -/
def contCohomologyMod2 (n : ℕ) : Type u :=
  contCocycles G n ⧸ Submodule.comap (contCocycles G n).subtype (contCoboundaries G n)

noncomputable instance (n : ℕ) : AddCommGroup (contCohomologyMod2 G n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ Submodule.comap (contCocycles G n).subtype _))

noncomputable instance (n : ℕ) : Module (ZMod 2) (contCohomologyMod2 G n) :=
  inferInstanceAs (Module (ZMod 2) (_ ⧸ Submodule.comap (contCocycles G n).subtype _))

theorem continuous_of_subsingleton_dom {X : Type*} [TopologicalSpace X] [Subsingleton X]
    (f : X → ZMod 2) : Continuous f := by
  rcases isEmpty_or_nonempty X with _ | ⟨⟨x⟩⟩
  · exact continuous_of_discreteTopology
  · have : f = Function.const X (f x) := funext fun y => congrArg f (Subsingleton.elim _ _)
    rw [this]; exact continuous_const

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The zeroth differential vanishes. -/
theorem cochainD_zero_eq_zero : cochainD G 0 = 0 := by
  refine LinearMap.ext fun f => funext fun g => ?_
  rw [cochainD_apply]
  have h : ∀ x y : Fin 0 → G, x = y := fun x y => funext fun i => i.elim0
  rw [Fin.sum_univ_one, h (Fin.contractNth 0 (· * ·) g) (fun i => g i.succ)]
  have : ∀ c : ZMod 2, c + c = 0 := by decide
  simpa using this (f fun i => g i.succ)

omit [IsTopologicalGroup G] in
theorem contCocycles_zero_eq_top : contCocycles G 0 = ⊤ := by
  refine eq_top_iff.2 fun f _ => ⟨?_, continuous_of_subsingleton_dom f⟩
  show cochainD G 0 f = 0
  rw [cochainD_zero_eq_zero]; rfl

/-- `H⁰(G, ℤ/2) ≅ ℤ/2` for every topological group `G`. -/
noncomputable def contCohomologyMod2ZeroEquiv : contCohomologyMod2 G 0 ≃ₗ[ZMod 2] ZMod 2 :=
  (Submodule.quotEquivOfEqBot _ (by simp [contCoboundaries])).trans <|
    (LinearEquiv.ofEq _ _ (contCocycles_zero_eq_top G)).trans <|
      Submodule.topEquiv.trans (LinearEquiv.funUnique (Fin 0 → G) (ZMod 2) (ZMod 2))

/-! ### Degree one: cohomology classes are continuous homomorphisms -/

/-- The `ℤ/2`-module of continuous homomorphisms `G → ℤ/2`. -/
def contHomsMod2 : Submodule (ZMod 2) (G → ZMod 2) where
  carrier := {f | Continuous f ∧ ∀ a b : G, f (a * b) = f a + f b}
  add_mem' hf hg := ⟨hf.1.add hg.1, fun a b => by
    simp only [Pi.add_apply, hf.2 a b, hg.2 a b]; abel⟩
  zero_mem' := ⟨continuous_const, fun a b => by simp⟩
  smul_mem' c f hf := ⟨hf.1.const_smul c, fun a b => by
    simp only [Pi.smul_apply, smul_eq_mul, hf.2 a b]; ring⟩

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Identification of `1`-cochains with functions on `G`. -/
theorem cochainOne_ext (f : (Fin 1 → G) → ZMod 2) (g : Fin 1 → G) : f g = f (fun _ => g 0) := by
  refine congrArg f (funext fun i => ?_)
  have : i = 0 := Subsingleton.elim _ _
  rw [this]

/-- `1`-cochains are the same thing as functions on `G`. -/
def cochainOneEquiv : ((Fin 1 → G) → ZMod 2) ≃ₗ[ZMod 2] (G → ZMod 2) where
  toFun f a := f (fun _ => a)
  invFun h g := h (g 0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := funext fun g => (cochainOne_ext G f g).symm
  right_inv _ := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem cochainD_one_apply (f : (Fin 1 → G) → ZMod 2) (a b : G) :
    cochainD G 1 f ![a, b] =
      f (fun _ => b) + (f (fun _ => a * b) + f (fun _ => a)) := by
  rw [cochainD_apply, Fin.sum_univ_two]
  have h1 : (fun i : Fin 1 => (![a, b] : Fin 2 → G) i.succ) = fun _ => b := by
    funext i; have : i = 0 := Subsingleton.elim _ _; rw [this]; rfl
  have h2 : Fin.contractNth 0 (· * ·) (![a, b] : Fin 2 → G) = fun _ => a * b := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [Fin.contractNth]
  have h3 : Fin.contractNth 1 (· * ·) (![a, b] : Fin 2 → G) = fun _ => a := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [Fin.contractNth]
  rw [h1, h2, h3]

omit [IsTopologicalGroup G] in
theorem map_contCocycles_one :
    Submodule.map (cochainOneEquiv G).toLinearMap (contCocycles G 1) = contHomsMod2 G := by
  ext h
  constructor
  · rintro ⟨f, ⟨hker, hcont⟩, rfl⟩
    refine ⟨hcont.comp (continuous_pi fun _ => continuous_id), fun a b => ?_⟩
    have h0 : cochainD G 1 f ![a, b] = 0 := by
      rw [show cochainD G 1 f = 0 from hker]; rfl
    rw [cochainD_one_apply] at h0
    have hchar : ∀ x y z : ZMod 2, x + (y + z) = 0 → y = z + x := by decide
    exact hchar _ _ _ h0
  · rintro ⟨hcont, hhom⟩
    refine ⟨fun g => h (g 0), ⟨?_, ?_⟩, rfl⟩
    · show cochainD G 1 (fun g => h (g 0)) = 0
      funext g
      have hg : g = ![g 0, g 1] := by
        funext i
        fin_cases i <;> rfl
      rw [hg, cochainD_one_apply]
      have := hhom (g 0) (g 1)
      simp only []
      have hchar : ∀ x y z : ZMod 2, y = x + z → x + (y + z) = 0 := by decide
      exact hchar _ _ _ (by rw [this]; abel)
    · exact hcont.comp (continuous_apply 0)

omit [IsTopologicalGroup G] in
theorem contCoboundaries_one_eq_bot : contCoboundaries G 1 = ⊥ := by
  rw [contCoboundaries]
  refine le_antisymm ?_ bot_le
  rintro x ⟨f, -, rfl⟩
  rw [show cochainD G 0 f = 0 from congrFun (congrArg _ (cochainD_zero_eq_zero G)) f]
  exact Submodule.zero_mem _

/-- `H¹(G, ℤ/2)` is the module of continuous homomorphisms `G → ℤ/2`. -/
noncomputable def contCohomologyMod2OneEquiv :
    contCohomologyMod2 G 1 ≃ₗ[ZMod 2] contHomsMod2 G :=
  (Submodule.quotEquivOfEqBot _ (by rw [contCoboundaries_one_eq_bot]; simp)).trans <|
    ((cochainOneEquiv G).submoduleMap (contCocycles G 1)).trans
      (LinearEquiv.ofEq _ _ (map_contCocycles_one G))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Over the trivial group, the differential acts on (necessarily constant) cochains as
multiplication by the degree. -/
theorem cochainD_of_subsingleton [Subsingleton G] (m : ℕ) (f : (Fin m → G) → ZMod 2)
    (x : Fin m → G) (y : Fin (m + 1) → G) :
    cochainD G m f y = (m : ZMod 2) * f x := by
  have hf : ∀ z : Fin m → G, f z = f x := fun z => congrArg f (Subsingleton.elim _ _)
  rw [cochainD_apply, hf]
  rw [Finset.sum_congr rfl (fun j _ => hf (Fin.contractNth j (· * ·) y))]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : (2 : ZMod 2) = 0 := rfl
  push_cast
  ring_nf
  rw [h2]
  ring

omit [IsTopologicalGroup G] in
/-- For the trivial group all higher continuous cohomology vanishes. -/
theorem contCohomologyMod2_subsingleton [Subsingleton G] {n : ℕ} (hn : 0 < n) :
    Subsingleton (contCohomologyMod2 G n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have key : ∀ z : contCocycles G (m + 1),
      ((z : (Fin (m + 1) → G) → ZMod 2)) ∈ contCoboundaries G (m + 1) := by
    intro z
    set y : (Fin (m + 1) → G) → ZMod 2 := (z : (Fin (m + 1) → G) → ZMod 2) with hy
    set x₀ : Fin (m + 1) → G := fun _ => 1 with hx₀
    have hconst : y = fun _ => y x₀ := funext fun g => congrArg y (Subsingleton.elim _ _)
    have hcoc : cochainD G (m + 1) y = 0 := z.2.1
    rcases Nat.even_or_odd m with he | ho
    · -- `m` even, so `m + 1` is odd and the cocycle condition forces `y = 0`
      have hcast : ((m + 1 : ℕ) : ZMod 2) = 1 := by
        obtain ⟨k, rfl⟩ := he
        push_cast
        rw [show ((k : ZMod 2) + k + 1) = (2 : ZMod 2) * k + 1 by ring, show (2 : ZMod 2) = 0 from rfl]
        ring
      have h0 : y x₀ = 0 := by
        have := congrFun hcoc (fun _ => 1)
        rw [cochainD_of_subsingleton G (m + 1) y x₀ (fun _ => 1), hcast, one_mul] at this
        exact this
      have hyzero : y = 0 := by rw [hconst, h0]; rfl
      exact ⟨0, continuous_const, by rw [hyzero]; exact map_zero _⟩
    · -- `m` odd, so every constant cochain is a coboundary
      have hcast : ((m : ℕ) : ZMod 2) = 1 := by
        obtain ⟨k, rfl⟩ := ho
        push_cast
        rw [show ((2 : ZMod 2) * k + 1) = (2 : ZMod 2) * k + 1 from rfl,
          show (2 : ZMod 2) = 0 from rfl]
        ring
      refine ⟨fun _ => y x₀, continuous_const, ?_⟩
      funext g
      rw [cochainD_of_subsingleton G m (fun _ => y x₀) (fun _ => 1) g, hcast, one_mul]
      exact congrFun hconst.symm g
  refine ⟨fun a b => ?_⟩
  have hz : ∀ c : contCohomologyMod2 G (m + 1), c = 0 := by
    intro c
    induction c using Submodule.Quotient.induction_on with
    | H z => exact (Submodule.Quotient.mk_eq_zero _).2 (key z)
  rw [hz a, hz b]

end Cohomology

/-! ## The Milnor conjecture -/

section Statement

variable (F : Type u) [Field F]

/-- The absolute Galois group of `F`, with the Krull topology. -/
abbrev absoluteGaloisGroup : Type u := SeparableClosure F ≃ₐ[F] SeparableClosure F

/-- Mod-`2` Galois cohomology `H^n(Gal(F_sep/F), ℤ/2)`, defined with continuous cochains. -/
def GaloisCohomologyMod2 (n : ℕ) : Type u := contCohomologyMod2 (absoluteGaloisGroup F) n

noncomputable instance (n : ℕ) : AddCommGroup (GaloisCohomologyMod2 F n) :=
  inferInstanceAs (AddCommGroup (contCohomologyMod2 (absoluteGaloisGroup F) n))

noncomputable instance (n : ℕ) : Module (ZMod 2) (GaloisCohomologyMod2 F n) :=
  inferInstanceAs (Module (ZMod 2) (contCohomologyMod2 (absoluteGaloisGroup F) n))

/-- **The Milnor conjecture** (Voevodsky's theorem) for a field `F`: in every degree, mod-`2`
Milnor K-theory agrees with mod-`2` Galois cohomology. -/
def MilnorConjecture : Prop :=
  ∀ n : ℕ, Nonempty (MilnorKMod2 F n ≃ₗ[ZMod 2] GaloisCohomologyMod2 F n)

/-- The subgroup of squares of `Fˣ`. -/
def squareUnits : Subgroup Fˣ where
  carrier := {a | ∃ b : Fˣ, b * b = a}
  one_mem' := ⟨1, one_mul 1⟩
  mul_mem' := by
    rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, by rw [mul_mul_mul_comm]⟩
  inv_mem' := by
    rintro a ⟨x, rfl⟩
    exact ⟨x⁻¹, by rw [← mul_inv]⟩

end Statement

/-! ## Results -/

/-- The base case of the Milnor conjecture, valid over every field: in degree zero both sides
are `ℤ/2`. -/
noncomputable def milnorDegreeZero (F : Type u) [Field F] :
    MilnorKMod2 F 0 ≃ₗ[ZMod 2] GaloisCohomologyMod2 F 0 :=
  (milnorKMod2ZeroEquiv F).trans (contCohomologyMod2ZeroEquiv (absoluteGaloisGroup F)).symm

/-- Any two subsingleton modules are linearly equivalent. -/
def linearEquivOfSubsingleton (R : Type*) (M : Type*) (N : Type*) [Semiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] [Subsingleton M] [Subsingleton N] :
    M ≃ₗ[R] N where
  toFun _ := 0
  map_add' _ _ := Subsingleton.elim _ _
  map_smul' _ _ := Subsingleton.elim _ _
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- The absolute Galois group of a separably closed field is trivial. -/
theorem subsingleton_absoluteGaloisGroup (F : Type u) [Field F] [IsSepClosed F] :
    Subsingleton (absoluteGaloisGroup F) := by
  have hb := IsPurelyInseparable.bijective_algebraMap_of_isSeparable F (SeparableClosure F)
  refine ⟨fun a b => ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := hb.2 x
  simp [AlgEquiv.commutes]

/-- In a separably closed field of characteristic `≠ 2` every unit is a square. -/
theorem exists_sq_of_isSepClosed (F : Type u) [Field F] [IsSepClosed F] (h2 : (2 : F) ≠ 0)
    (a : Fˣ) : ∃ b : Fˣ, b * b = a := by
  haveI : NeZero ((2 : ℕ) : F) := ⟨by simpa using h2⟩
  obtain ⟨z, hz⟩ := IsSepClosed.exists_pow_nat_eq (k := F) (a : F) 2
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hz
    exact a.ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, by ext; simpa [pow_two] using hz⟩

/-- The Milnor conjecture holds for separably closed fields of characteristic `≠ 2`: both sides
vanish in positive degrees. -/
theorem milnorConjecture_of_isSepClosed (F : Type u) [Field F] [IsSepClosed F] (h2 : (2 : F) ≠ 0) :
    MilnorConjecture F := by
  intro n
  cases n with
  | zero => exact ⟨milnorDegreeZero F⟩
  | succ m =>
      haveI : Subsingleton (MilnorKMod2 F (m + 1)) :=
        milnorKMod2_subsingleton_of_sq F (Nat.succ_pos m) (exists_sq_of_isSepClosed F h2)
      haveI : Subsingleton (absoluteGaloisGroup F) := subsingleton_absoluteGaloisGroup F
      haveI : Subsingleton (GaloisCohomologyMod2 F (m + 1)) :=
        contCohomologyMod2_subsingleton (absoluteGaloisGroup F) (Nat.succ_pos m)
      exact ⟨linearEquivOfSubsingleton _ _ _⟩

section DegreeOne

variable (F : Type u) [Field F]

/-- Mod-`2` Milnor K-theory is `2`-torsion. -/
theorem milnorKMod2_add_self (n : ℕ) (x : MilnorKMod2 F n) : x + x = 0 := by
  have h : ((1 : ZMod 2) + 1) • x = (1 : ZMod 2) • x + (1 : ZMod 2) • x := add_smul _ _ _
  rw [show (1 : ZMod 2) + 1 = 0 from rfl, zero_smul, one_smul] at h
  exact h.symm

/-- `Fx / (Fx)^2` is `2`-torsion. -/
theorem two_nsmul_quot_eq_zero (x : Additive (Fˣ ⧸ squareUnits F)) : 2 • x = 0 := by
  have h : ∀ q : Fˣ ⧸ squareUnits F, q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
        rw [← QuotientGroup.mk_pow]
        exact (QuotientGroup.eq_one_iff _).2 ⟨a, by rw [pow_two]⟩
  have h2 := h (Additive.toMul x)
  have : Additive.ofMul ((Additive.toMul x) ^ 2) = Additive.ofMul (1 : Fˣ ⧸ squareUnits F) :=
    congrArg Additive.ofMul h2
  simpa using this

noncomputable instance : Module (ZMod 2) (Additive (Fˣ ⧸ squareUnits F)) := by
  refine AddCommGroup.zmodModule (n := 2) (G := Additive (Fˣ ⧸ squareUnits F)) fun x => ?_
  exact two_nsmul_quot_eq_zero F x

/-- The class of a unit in `Fx / (Fx)^2`, written additively. -/
def unitClass (a : Fˣ) : Additive (Fˣ ⧸ squareUnits F) :=
  Additive.ofMul (QuotientGroup.mk a)

theorem unitClass_mul (a b : Fˣ) : unitClass F (a * b) = unitClass F a + unitClass F b := rfl

theorem unitClass_surjective : Function.Surjective (unitClass F) := by
  intro x
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
  exact ⟨a, congrArg Additive.ofMul ha⟩

theorem update_fin_one (v : Fin 1 → Fˣ) (i : Fin 1) (x : Fˣ) :
    Function.update v i x = fun _ => x := by
  funext j
  have hj : j = i := Subsingleton.elim _ _
  subst hj
  simp

theorem symbol_mul (a b : Fˣ) :
    symbol F (fun _ : Fin 1 => a * b) = symbol F (fun _ => a) + symbol F (fun _ => b) := by
  have hmem : Finsupp.single (Function.update (fun _ : Fin 1 => a) 0 (a * b)) (1 : ZMod 2)
      - Finsupp.single (Function.update (fun _ : Fin 1 => a) 0 a) 1
      - Finsupp.single (Function.update (fun _ : Fin 1 => a) 0 b) 1 ∈ milnorRelSubmodule F 1 :=
    Submodule.subset_span (Or.inl ⟨0, a, b, fun _ => a, rfl⟩)
  rw [update_fin_one, update_fin_one, update_fin_one] at hmem
  have h0 : symbol F (fun _ : Fin 1 => a * b) - symbol F (fun _ : Fin 1 => a)
      - symbol F (fun _ : Fin 1 => b) = 0 := by
    rw [symbol, symbol, symbol, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_sub]
    exact (Submodule.Quotient.mk_eq_zero _).2 hmem
  rw [sub_sub, sub_eq_zero] at h0
  exact h0

theorem symbol_one : symbol F (fun _ : Fin 1 => 1) = 0 := by
  have h := symbol_mul F 1 1
  rw [one_mul] at h
  exact left_eq_add.mp h

/-- The symbol map `Fx → k^M_1(F)`, as a monoid homomorphism. -/
noncomputable def unitSymbolHom : Fˣ →* Multiplicative (MilnorKMod2 F 1) where
  toFun a := Multiplicative.ofAdd (symbol F (fun _ => a))
  map_one' := congrArg Multiplicative.ofAdd (symbol_one F)
  map_mul' a b := congrArg Multiplicative.ofAdd (symbol_mul F a b)

theorem squareUnits_le_ker : squareUnits F ≤ (unitSymbolHom F).ker := by
  rintro a ⟨b, rfl⟩
  have : symbol F (fun _ : Fin 1 => b * b) = 0 := by
    rw [symbol_mul]; exact milnorKMod2_add_self F 1 _
  exact congrArg Multiplicative.ofAdd this

/-- The inverse map `Fx/(Fx)^2 → k^M_1(F)`. -/
noncomputable def quotToMilnorOne : Additive (Fˣ ⧸ squareUnits F) →+ MilnorKMod2 F 1 :=
  MonoidHom.toAdditiveLeft (QuotientGroup.lift _ (unitSymbolHom F) (squareUnits_le_ker F))

theorem quotToMilnorOne_unitClass (a : Fˣ) :
    quotToMilnorOne F (unitClass F a) = symbol F (fun _ => a) := rfl

theorem milnorRel_one_le_ker :
    milnorRelSubmodule F 1 ≤ LinearMap.ker (Finsupp.linearCombination (ZMod 2)
      (fun v : Fin 1 → Fˣ => unitClass F (v 0))) := by
  rw [milnorRelSubmodule, Submodule.span_le]
  rintro x (⟨i, a, b, v, rfl⟩ | ⟨v, i, j, hij, -, rfl⟩)
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub,
      Finsupp.linearCombination_single, one_smul, update_fin_one]
    rw [unitClass_mul]
    abel
  · exact absurd (Subsingleton.elim i j) hij

/-- The comparison map from degree one Milnor K-theory to `Fx/(Fx)^2`. -/
noncomputable def milnorOneToQuot :
    MilnorKMod2 F 1 →ₗ[ZMod 2] Additive (Fˣ ⧸ squareUnits F) :=
  Submodule.liftQ _ (Finsupp.linearCombination (ZMod 2)
    (fun v : Fin 1 → Fˣ => unitClass F (v 0))) (milnorRel_one_le_ker F)

theorem milnorOneToQuot_symbol (v : Fin 1 → Fˣ) :
    milnorOneToQuot F (symbol F v) = unitClass F (v 0) := by
  show Finsupp.linearCombination (ZMod 2) (fun v : Fin 1 → Fˣ => unitClass F (v 0))
      (Finsupp.single v 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

/-- Degree one of mod-`2` Milnor K-theory is `Fx/(Fx)^2`. -/
noncomputable def milnorKMod2OneEquiv :
    MilnorKMod2 F 1 ≃+ Additive (Fˣ ⧸ squareUnits F) where
  toFun := milnorOneToQuot F
  invFun := quotToMilnorOne F
  map_add' := map_add _
  left_inv := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H y =>
        induction y using Finsupp.induction_linear with
        | zero => simp
        | add f g hf hg =>
            have hsum : (Submodule.Quotient.mk (f + g) : MilnorKMod2 F 1) =
                Submodule.Quotient.mk f + Submodule.Quotient.mk g := rfl
            rw [hsum, map_add, map_add, hf, hg]
        | single v c =>
            have hc : ∀ d : ZMod 2, d = 0 ∨ d = 1 := by decide
            rcases hc c with rfl | rfl
            · simp
            · have hv : v = fun _ => v 0 := funext fun i => congrArg v (Subsingleton.elim _ _)
              show quotToMilnorOne F (milnorOneToQuot F (symbol F v)) = symbol F v
              rw [milnorOneToQuot_symbol, quotToMilnorOne_unitClass, ← hv]
  right_inv := by
    intro x
    obtain ⟨a, rfl⟩ := unitClass_surjective F x
    rw [quotToMilnorOne_unitClass, milnorOneToQuot_symbol]

end DegreeOne

/-! ## The Kummer (norm residue) map in degree one -/

section Kummer

variable (F : Type u) [Field F]

/-- The mod-`2` character of the absolute Galois group attached to an element `r` of the
separable closure: it records whether `σ` fixes `r`. -/
noncomputable def kummerChar (r : SeparableClosure F) : absoluteGaloisGroup F → ZMod 2 :=
  fun σ => if σ r = r then 0 else 1

theorem kummerChar_eq_zero_iff (r : SeparableClosure F) (σ : absoluteGaloisGroup F) :
    kummerChar F r σ = 0 ↔ σ r = r := by
  unfold kummerChar
  split_ifs with h
  · simp [h]
  · exact ⟨fun hc => absurd hc (by decide), fun hc => absurd hc h⟩

theorem kummerChar_eq_one_of_ne {r : SeparableClosure F} {σ : absoluteGaloisGroup F}
    (h : σ r ≠ r) : kummerChar F r σ = 1 := by
  unfold kummerChar
  rw [if_neg h]

theorem kummerChar_continuous (r : SeparableClosure F) : Continuous (kummerChar F r) := by
  have he : ((MulAction.stabilizer (absoluteGaloisGroup F) r : Subgroup (absoluteGaloisGroup F)) :
      Set (absoluteGaloisGroup F)) = {σ : absoluteGaloisGroup F | σ r = r} := by
    ext τ; simp [MulAction.mem_stabilizer_iff]
  have hopen : IsOpen {σ : absoluteGaloisGroup F | σ r = r} := by
    rw [← he]; exact stabilizer_isOpen_of_isIntegral (K := F) r
  have hclosed : IsClosed {σ : absoluteGaloisGroup F | σ r = r} := by
    rw [← he]
    exact Subgroup.isClosed_of_isOpen _ (by rw [he]; exact hopen)
  refine (IsLocallyConstant.iff_isOpen_fiber.2 fun y => ?_).continuous
  have hd : ∀ d : ZMod 2, d = 0 ∨ d = 1 := by decide
  rcases hd y with rfl | rfl
  · have h0 : kummerChar F r ⁻¹' {0} = {σ : absoluteGaloisGroup F | σ r = r} := by
      ext σ
      exact kummerChar_eq_zero_iff F r σ
    rw [h0]; exact hopen
  · have h1 : kummerChar F r ⁻¹' {1} = {σ : absoluteGaloisGroup F | σ r = r}ᶜ := by
      ext σ
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_setOf_eq]
      constructor
      · intro h hc
        rw [(kummerChar_eq_zero_iff F r σ).2 hc] at h
        exact absurd h (by decide)
      · intro h
        exact kummerChar_eq_one_of_ne F h
    rw [h1]; exact hclosed.isOpen_compl

theorem sq_eq_sq_imp_eq_or_eq_neg {K : Type*} [Field K] {x y : K} (h : x ^ 2 = y ^ 2) :
    x = y ∨ x = -y := by
  have hz : (x - y) * (x + y) = 0 := by linear_combination h
  rcases mul_eq_zero.1 hz with h' | h'
  · exact Or.inl (sub_eq_zero.1 h')
  · exact Or.inr (eq_neg_of_add_eq_zero_left h')

theorem two_ne_zero_sepClosure (h2 : (2 : F) ≠ 0) : (2 : SeparableClosure F) ≠ 0 := by
  intro h
  refine h2 ?_
  have hmap : algebraMap F (SeparableClosure F) 2 = 0 := by rw [map_ofNat]; exact h
  exact (map_eq_zero_iff _ (algebraMap F (SeparableClosure F)).injective).1 hmap

theorem neg_ne_self_of_ne_zero (h2 : (2 : F) ≠ 0) {x : SeparableClosure F} (hx : x ≠ 0) :
    -x ≠ x := by
  intro h
  refine hx ?_
  have hxx : x + x = 0 := by
    calc x + x = -x + x := by rw [h]
    _ = 0 := by ring
  have h2x : (2 : SeparableClosure F) * x = 0 := by linear_combination hxx
  rcases mul_eq_zero.1 h2x with h' | h'
  · exact absurd h' (two_ne_zero_sepClosure F h2)
  · exact h'

theorem kummerChar_neg (r : SeparableClosure F) : kummerChar F (-r) = kummerChar F r := by
  funext σ
  have hiff : σ (-r) = -r ↔ σ r = r := by
    rw [map_neg]
    exact neg_inj
  by_cases h : σ r = r
  · rw [(kummerChar_eq_zero_iff F (-r) σ).2 (hiff.2 h), (kummerChar_eq_zero_iff F r σ).2 h]
  · rw [kummerChar_eq_one_of_ne F (fun hc => h (hiff.1 hc)), kummerChar_eq_one_of_ne F h]

theorem kummerChar_congr_sq {r s : SeparableClosure F} (h : r ^ 2 = s ^ 2) :
    kummerChar F r = kummerChar F s := by
  rcases sq_eq_sq_imp_eq_or_eq_neg h with rfl | rfl
  · rfl
  · exact kummerChar_neg F s

/-- Every element of the separable closure of a field of characteristic `≠ 2` has a square
root. -/
theorem exists_sqrt_sepClosure (h2 : (2 : F) ≠ 0) (x : SeparableClosure F) : ∃ r, r ^ 2 = x := by
  haveI : NeZero ((2 : ℕ) : SeparableClosure F) := ⟨by
    simpa using two_ne_zero_sepClosure F h2⟩
  exact IsSepClosed.exists_pow_nat_eq x 2

/-- A chosen square root in the separable closure. -/
noncomputable def sqrtSep (h2 : (2 : F) ≠ 0) (x : SeparableClosure F) : SeparableClosure F :=
  Classical.choose (exists_sqrt_sepClosure F h2 x)

theorem sqrtSep_sq (h2 : (2 : F) ≠ 0) (x : SeparableClosure F) : (sqrtSep F h2 x) ^ 2 = x :=
  Classical.choose_spec (exists_sqrt_sepClosure F h2 x)

theorem galois_fix_or_neg {c : F} {r : SeparableClosure F}
    (hr : r ^ 2 = algebraMap F (SeparableClosure F) c) (σ : absoluteGaloisGroup F) :
    σ r = r ∨ σ r = -r := by
  have h1 : (σ r) ^ 2 = r ^ 2 := by
    rw [← map_pow, hr, AlgEquiv.commutes]
  exact sq_eq_sq_imp_eq_or_eq_neg h1

/-- The Kummer character is a homomorphism on the Galois group. -/
theorem kummerChar_map_mul (h2 : (2 : F) ≠ 0) {c : F} {r : SeparableClosure F}
    (hr : r ^ 2 = algebraMap F (SeparableClosure F) c) (σ τ : absoluteGaloisGroup F) :
    kummerChar F r (σ * τ) = kummerChar F r σ + kummerChar F r τ := by
  by_cases hr0 : r = 0
  · subst hr0
    simp [kummerChar]
  have hneg : -r ≠ r := neg_ne_self_of_ne_zero F h2 hr0
  have hmul : (σ * τ) r = σ (τ r) := rfl
  rcases galois_fix_or_neg F hr σ with hs | hs <;> rcases galois_fix_or_neg F hr τ with ht | ht
  · rw [(kummerChar_eq_zero_iff F r _).2 (by rw [hmul, ht, hs]),
      (kummerChar_eq_zero_iff F r σ).2 hs, (kummerChar_eq_zero_iff F r τ).2 ht, add_zero]
  · rw [kummerChar_eq_one_of_ne F (show (σ * τ) r ≠ r by rw [hmul, ht, map_neg, hs]; exact hneg),
      (kummerChar_eq_zero_iff F r σ).2 hs,
      kummerChar_eq_one_of_ne F (show τ r ≠ r by rw [ht]; exact hneg), zero_add]
  · rw [kummerChar_eq_one_of_ne F (show (σ * τ) r ≠ r by rw [hmul, ht, hs]; exact hneg),
      (kummerChar_eq_zero_iff F r τ).2 ht,
      kummerChar_eq_one_of_ne F (show σ r ≠ r by rw [hs]; exact hneg), add_zero]
  · rw [(kummerChar_eq_zero_iff F r _).2 (by rw [hmul, ht, map_neg, hs, neg_neg]),
      kummerChar_eq_one_of_ne F (show σ r ≠ r by rw [hs]; exact hneg),
      kummerChar_eq_one_of_ne F (show τ r ≠ r by rw [ht]; exact hneg)]
    decide

/-- The Kummer character of a product of square roots is the sum of the characters. -/
theorem kummerChar_mul_roots (h2 : (2 : F) ≠ 0) {c d : F} {x y : SeparableClosure F}
    (hx : x ^ 2 = algebraMap F (SeparableClosure F) c)
    (hy : y ^ 2 = algebraMap F (SeparableClosure F) d) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    kummerChar F (x * y) = kummerChar F x + kummerChar F y := by
  funext σ
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx0 hy0
  have hnx : -x ≠ x := neg_ne_self_of_ne_zero F h2 hx0
  have hny : -y ≠ y := neg_ne_self_of_ne_zero F h2 hy0
  have hnxy : -(x * y) ≠ x * y := neg_ne_self_of_ne_zero F h2 hxy0
  have hmap : σ (x * y) = σ x * σ y := map_mul _ _ _
  rw [Pi.add_apply]
  rcases galois_fix_or_neg F hx σ with hs | hs <;> rcases galois_fix_or_neg F hy σ with ht | ht
  · rw [(kummerChar_eq_zero_iff F _ σ).2 (by rw [hmap, hs, ht]),
      (kummerChar_eq_zero_iff F x σ).2 hs, (kummerChar_eq_zero_iff F y σ).2 ht, add_zero]
  · rw [kummerChar_eq_one_of_ne F (show σ (x * y) ≠ x * y by
        rw [hmap, hs, ht, mul_neg]; exact hnxy),
      (kummerChar_eq_zero_iff F x σ).2 hs,
      kummerChar_eq_one_of_ne F (show σ y ≠ y by rw [ht]; exact hny), zero_add]
  · rw [kummerChar_eq_one_of_ne F (show σ (x * y) ≠ x * y by
        rw [hmap, hs, ht, neg_mul]; exact hnxy),
      (kummerChar_eq_zero_iff F y σ).2 ht,
      kummerChar_eq_one_of_ne F (show σ x ≠ x by rw [hs]; exact hnx), add_zero]
  · rw [(kummerChar_eq_zero_iff F _ σ).2 (by rw [hmap, hs, ht, neg_mul_neg]),
      kummerChar_eq_one_of_ne F (show σ x ≠ x by rw [hs]; exact hnx),
      kummerChar_eq_one_of_ne F (show σ y ≠ y by rw [ht]; exact hny)]
    decide

/-- The Kummer character of a unit of `F`. -/
noncomputable def kummerCharUnit (h2 : (2 : F) ≠ 0) (a : Fˣ) : absoluteGaloisGroup F → ZMod 2 :=
  kummerChar F (sqrtSep F h2 (algebraMap F (SeparableClosure F) (a : F)))

theorem sqrtSep_unit_ne_zero (h2 : (2 : F) ≠ 0) (a : Fˣ) :
    sqrtSep F h2 (algebraMap F (SeparableClosure F) (a : F)) ≠ 0 := by
  intro h
  have hsq := sqrtSep_sq F h2 (algebraMap F (SeparableClosure F) (a : F))
  rw [h, zero_pow (by norm_num)] at hsq
  have ha : (a : F) = 0 :=
    (map_eq_zero_iff _ (algebraMap F (SeparableClosure F)).injective).1 hsq.symm
  exact a.ne_zero ha

theorem kummerCharUnit_mem (h2 : (2 : F) ≠ 0) (a : Fˣ) :
    kummerCharUnit F h2 a ∈ contHomsMod2 (absoluteGaloisGroup F) :=
  ⟨kummerChar_continuous F _,
    fun σ τ => kummerChar_map_mul F h2 (sqrtSep_sq F h2 _) σ τ⟩

theorem kummerCharUnit_mul (h2 : (2 : F) ≠ 0) (a b : Fˣ) :
    kummerCharUnit F h2 (a * b) = kummerCharUnit F h2 a + kummerCharUnit F h2 b := by
  have hra2 : (sqrtSep F h2 (algebraMap F (SeparableClosure F) (a : F))) ^ 2
      = algebraMap F (SeparableClosure F) (a : F) := sqrtSep_sq F h2 _
  have hrb2 : (sqrtSep F h2 (algebraMap F (SeparableClosure F) (b : F))) ^ 2
      = algebraMap F (SeparableClosure F) (b : F) := sqrtSep_sq F h2 _
  have hchar : kummerCharUnit F h2 (a * b)
      = kummerChar F (sqrtSep F h2 (algebraMap F (SeparableClosure F) (a : F))
          * sqrtSep F h2 (algebraMap F (SeparableClosure F) (b : F))) := by
    refine kummerChar_congr_sq F ?_
    rw [sqrtSep_sq, mul_pow, hra2, hrb2, Units.val_mul, map_mul]
  rw [hchar, kummerChar_mul_roots F h2 hra2 hrb2 (sqrtSep_unit_ne_zero F h2 a)
    (sqrtSep_unit_ne_zero F h2 b)]
  rfl

theorem kummerCharUnit_sq (h2 : (2 : F) ≠ 0) (b : Fˣ) :
    kummerCharUnit F h2 (b * b) = 0 := by
  have hchar : kummerCharUnit F h2 (b * b)
      = kummerChar F (algebraMap F (SeparableClosure F) (b : F)) := by
    refine kummerChar_congr_sq F ?_
    rw [sqrtSep_sq, Units.val_mul, map_mul, sq]
  rw [hchar]
  funext σ
  exact (kummerChar_eq_zero_iff F _ σ).2 (AlgEquiv.commutes σ (b : F))

/-- The Kummer map `Fˣ → H¹(Gal(F_sep/F), ℤ/2)`, i.e. the degree one norm residue map, as a
monoid homomorphism. -/
noncomputable def kummerUnitHom (h2 : (2 : F) ≠ 0) :
    Fˣ →* Multiplicative (contHomsMod2 (absoluteGaloisGroup F)) where
  toFun a := Multiplicative.ofAdd (⟨kummerCharUnit F h2 a, kummerCharUnit_mem F h2 a⟩ :
    contHomsMod2 (absoluteGaloisGroup F))
  map_one' := by
    refine congrArg Multiplicative.ofAdd (Subtype.ext ?_)
    have h := kummerCharUnit_sq F h2 1
    rwa [one_mul] at h
  map_mul' a b := by
    refine congrArg Multiplicative.ofAdd (Subtype.ext ?_)
    exact kummerCharUnit_mul F h2 a b

theorem squareUnits_le_ker_kummer (h2 : (2 : F) ≠ 0) :
    squareUnits F ≤ (kummerUnitHom F h2).ker := by
  rintro a ⟨b, rfl⟩
  refine congrArg Multiplicative.ofAdd (Subtype.ext ?_)
  exact kummerCharUnit_sq F h2 b

/-- The Kummer map `Fˣ/(Fˣ)² → H¹(Gal(F_sep/F), ℤ/2)`. -/
noncomputable def kummerMap (h2 : (2 : F) ≠ 0) :
    Additive (Fˣ ⧸ squareUnits F) →+ contHomsMod2 (absoluteGaloisGroup F) :=
  MonoidHom.toAdditiveLeft
    (QuotientGroup.lift _ (kummerUnitHom F h2) (squareUnits_le_ker_kummer F h2))

theorem kummerMap_unitClass (h2 : (2 : F) ≠ 0) (a : Fˣ) :
    (kummerMap F h2 (unitClass F a) : absoluteGaloisGroup F → ZMod 2)
      = kummerCharUnit F h2 a := rfl

/-- **The degree one norm residue map is injective.**  If every Galois automorphism fixes a
square root of `a`, then `a` is already a square in `F`. -/
theorem kummerMap_injective (h2 : (2 : F) ≠ 0) : Function.Injective (kummerMap F h2) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := unitClass_surjective F x
  have hchar : kummerCharUnit F h2 a = 0 := by
    rw [← kummerMap_unitClass F h2 a, hx]
    rfl
  have hfix : ∀ σ : absoluteGaloisGroup F,
      σ (sqrtSep F h2 (algebraMap F (SeparableClosure F) (a : F)))
        = sqrtSep F h2 (algebraMap F (SeparableClosure F) (a : F)) := by
    intro σ
    exact (kummerChar_eq_zero_iff F _ σ).1 (congrFun hchar σ)
  have hbot : sqrtSep F h2 (algebraMap F (SeparableClosure F) (a : F))
      ∈ (⊥ : IntermediateField F (SeparableClosure F)) :=
    (InfiniteGalois.mem_bot_iff_fixed _).2 hfix
  obtain ⟨s, hs⟩ := IntermediateField.mem_bot.1 hbot
  have hs2 : algebraMap F (SeparableClosure F) (s ^ 2)
      = algebraMap F (SeparableClosure F) (a : F) := by
    rw [map_pow, hs]
    exact sqrtSep_sq F h2 _
  have hsa : s ^ 2 = (a : F) := (algebraMap F (SeparableClosure F)).injective hs2
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num)] at hsa
    exact a.ne_zero hsa.symm
  have hmem : a ∈ squareUnits F := ⟨Units.mk0 s hs0, by ext; simpa [sq] using hsa⟩
  exact congrArg Additive.ofMul ((QuotientGroup.eq_one_iff a).2 hmem)

/-- **Surjectivity of the degree one norm residue map** (Kummer theory): every continuous
homomorphism `Gal(F_sep/F) → ℤ/2` is the Kummer character of a unit of `F`. -/
theorem kummerMap_surjective (h2 : (2 : F) ≠ 0) : Function.Surjective (kummerMap F h2) := by
  rintro ⟨χ, hcont, hhom⟩
  have hone : χ 1 = 0 := by
    have h := hhom 1 1
    rw [one_mul] at h
    exact left_eq_add.mp h
  have hinv : ∀ σ : absoluteGaloisGroup F, χ σ⁻¹ = χ σ := by
    intro σ
    have h := hhom σ σ⁻¹
    rw [mul_inv_cancel, hone] at h
    revert h
    generalize χ σ = u
    generalize χ σ⁻¹ = v
    revert u v
    decide
  by_cases hzero : χ = 0
  · refine ⟨unitClass F 1, Subtype.ext ?_⟩
    rw [kummerMap_unitClass]
    have h1 := kummerCharUnit_sq F h2 1
    rw [one_mul] at h1
    rw [h1]
    exact hzero.symm
  obtain ⟨σ₁, hσ₁⟩ := Function.ne_iff.mp hzero
  have hmul0 : ∀ a b : absoluteGaloisGroup F, χ a = 0 → χ b = 0 → χ (a * b) = 0 := by
    intro a b ha hb
    rw [hhom, ha, hb, add_zero]
  let Hs : Subgroup (absoluteGaloisGroup F) :=
    { carrier := {σ | χ σ = 0}
      mul_mem' := fun {a b} ha hb => hmul0 a b ha hb
      one_mem' := hone
      inv_mem' := fun {a} ha => by
        show χ a⁻¹ = 0
        rw [hinv]
        exact ha }
  have hmem : ∀ σ : absoluteGaloisGroup F, σ ∈ Hs ↔ χ σ = 0 := fun _ => Iff.rfl
  have hone' : ∀ σ : absoluteGaloisGroup F, σ ∉ Hs → χ σ = 1 := by
    intro σ hσ
    have hne : χ σ ≠ 0 := fun h => hσ ((hmem σ).2 h)
    revert hne
    generalize χ σ = u
    revert u
    decide
  have hopen : IsOpen (Hs : Set (absoluteGaloisGroup F)) := by
    have hpre : (Hs : Set (absoluteGaloisGroup F)) = χ ⁻¹' {0} := rfl
    rw [hpre]
    exact hcont.isOpen_preimage _ (isOpen_discrete _)
  have hclosed : IsClosed (Hs : Set (absoluteGaloisGroup F)) :=
    Subgroup.isClosed_of_isOpen _ hopen
  have hfix_ne : IntermediateField.fixedField Hs ≠ ⊥ := by
    intro hbot
    have h1 : (IntermediateField.fixedField Hs).fixingSubgroup = Hs :=
      InfiniteGalois.fixingSubgroup_fixedField ⟨Hs, hclosed⟩
    rw [hbot, IntermediateField.fixingSubgroup_bot] at h1
    refine hσ₁ ?_
    have : σ₁ ∈ Hs := h1 ▸ Subgroup.mem_top σ₁
    exact (hmem σ₁).1 this
  obtain ⟨x, hxfix, hxbot⟩ := SetLike.not_le_iff_exists.mp
    (fun hle => hfix_ne (le_antisymm hle bot_le))
  have hxfix' : ∀ σ ∈ Hs, σ x = x := (IntermediateField.mem_fixedField_iff Hs x).1 hxfix
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ : absoluteGaloisGroup F, σ x ≠ x := by
    by_contra hc
    push_neg at hc
    exact hxbot ((InfiniteGalois.mem_bot_iff_fixed x).2 hc)
  have hσ₀H : σ₀ ∉ Hs := fun h => hσ₀ (hxfix' σ₀ h)
  have hσ₀1 : χ σ₀ = 1 := hone' σ₀ hσ₀H
  have hsq : (σ₀ * σ₀) x = x := by
    refine hxfix' _ ((hmem _).2 ?_)
    rw [hhom, hσ₀1]
    decide
  set y : SeparableClosure F := x - σ₀ x with hy
  have hy0 : y ≠ 0 := sub_ne_zero.2 (fun h => hσ₀ h.symm)
  have hσ₀y : σ₀ y = -y := by
    rw [hy, map_sub, show σ₀ (σ₀ x) = x from hsq]
    ring
  have hHy : ∀ σ ∈ Hs, σ y = y := by
    intro σ hσ
    have h1 : σ x = x := hxfix' σ hσ
    have h2 : σ (σ₀ x) = σ₀ x := by
      have hc : σ₀⁻¹ * σ * σ₀ ∈ Hs := by
        refine (hmem _).2 ?_
        rw [hhom, hhom, hinv, hσ₀1, (hmem σ).1 hσ]
        decide
      have h3 : (σ₀⁻¹ * σ * σ₀) x = x := hxfix' _ hc
      have h4 : (σ₀ * (σ₀⁻¹ * σ * σ₀)) x = σ₀ x := by
        show σ₀ ((σ₀⁻¹ * σ * σ₀) x) = σ₀ x
        rw [h3]
      have h5 : (σ₀ * (σ₀⁻¹ * σ * σ₀)) = σ * σ₀ := by group
      rw [h5] at h4
      exact h4
    rw [hy, map_sub, h1, h2]
  have hnotHy : ∀ σ : absoluteGaloisGroup F, σ ∉ Hs → σ y = -y := by
    intro σ hσ
    have hτ : σ * σ₀⁻¹ ∈ Hs := by
      refine (hmem _).2 ?_
      rw [hhom, hinv, hσ₀1, hone' σ hσ]
      decide
    have h5 : σ = (σ * σ₀⁻¹) * σ₀ := by group
    rw [h5]
    show (σ * σ₀⁻¹) (σ₀ y) = -y
    rw [hσ₀y, map_neg, hHy _ hτ]
  have hy2fix : ∀ σ : absoluteGaloisGroup F, σ (y ^ 2) = y ^ 2 := by
    intro σ
    by_cases hσ : σ ∈ Hs
    · rw [map_pow, hHy σ hσ]
    · rw [map_pow, hnotHy σ hσ]
      ring
  obtain ⟨d, hd⟩ := IntermediateField.mem_bot.1
    ((InfiniteGalois.mem_bot_iff_fixed (y ^ 2)).2 hy2fix)
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, map_zero] at hd
    exact hy0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hd.symm)
  refine ⟨unitClass F (Units.mk0 d hd0), Subtype.ext ?_⟩
  rw [kummerMap_unitClass]
  have hchar : kummerCharUnit F h2 (Units.mk0 d hd0) = kummerChar F y := by
    refine kummerChar_congr_sq F ?_
    rw [sqrtSep_sq]
    exact hd
  rw [hchar]
  funext σ
  by_cases hσ : σ ∈ Hs
  · rw [(kummerChar_eq_zero_iff F y σ).2 (hHy σ hσ)]
    exact ((hmem σ).1 hσ).symm
  · rw [kummerChar_eq_one_of_ne F (show σ y ≠ y by
      rw [hnotHy σ hσ]; exact neg_ne_self_of_ne_zero F h2 hy0)]
    exact (hone' σ hσ).symm

end Kummer

/-- Reduction of degree one of the Milnor conjecture to Kummer theory. -/
theorem milnorDegreeOne_of_kummer (F : Type u) [Field F]
    (h : Nonempty (Additive (Fˣ ⧸ squareUnits F) ≃+ GaloisCohomologyMod2 F 1)) :
    Nonempty (MilnorKMod2 F 1 ≃+ GaloisCohomologyMod2 F 1) :=
  ⟨(milnorKMod2OneEquiv F).trans h.some⟩

/-- The **degree one norm residue map** `k^M_1(F) → H¹(Gal(F_sep/F), ℤ/2)`: the composite of the
identification `k^M_1(F) ≅ Fˣ/(Fˣ)²` with the Kummer map and the identification of `H¹` with
continuous homomorphisms. -/
noncomputable def normResidueOne (F : Type u) [Field F] (h2 : (2 : F) ≠ 0) :
    MilnorKMod2 F 1 →+ GaloisCohomologyMod2 F 1 :=
  (((contCohomologyMod2OneEquiv (absoluteGaloisGroup F)).symm.toAddEquiv).toAddMonoidHom.comp
    ((kummerMap F h2).comp (milnorKMod2OneEquiv F).toAddMonoidHom))

theorem normResidueOne_coe (F : Type u) [Field F] (h2 : (2 : F) ≠ 0) :
    ⇑(normResidueOne F h2) = (contCohomologyMod2OneEquiv (absoluteGaloisGroup F)).symm ∘
      (kummerMap F h2) ∘ (milnorKMod2OneEquiv F) := rfl

/-- The degree one norm residue map is injective for every field of characteristic `≠ 2`. -/
theorem normResidueOne_injective (F : Type u) [Field F] (h2 : (2 : F) ≠ 0) :
    Function.Injective (normResidueOne F h2) := by
  rw [normResidueOne_coe]
  exact ((contCohomologyMod2OneEquiv (absoluteGaloisGroup F)).symm.injective).comp
    ((kummerMap_injective F h2).comp (milnorKMod2OneEquiv F).injective)

/-- If the Kummer map is surjective (the remaining half of Kummer theory), then the degree one
norm residue map is an isomorphism, i.e. the Milnor conjecture holds in degree one. -/
theorem normResidueOne_bijective_of_kummer_surjective (F : Type u) [Field F] (h2 : (2 : F) ≠ 0)
    (hsurj : Function.Surjective (kummerMap F h2)) :
    Function.Bijective (normResidueOne F h2) := by
  refine ⟨normResidueOne_injective F h2, ?_⟩
  rw [normResidueOne_coe]
  exact ((contCohomologyMod2OneEquiv (absoluteGaloisGroup F)).symm.surjective).comp
    (hsurj.comp (milnorKMod2OneEquiv F).surjective)

/-- The degree one norm residue map is bijective for every field of characteristic `≠ 2`. -/
theorem normResidueOne_bijective (F : Type u) [Field F] (h2 : (2 : F) ≠ 0) :
    Function.Bijective (normResidueOne F h2) :=
  normResidueOne_bijective_of_kummer_surjective F h2 (kummerMap_surjective F h2)

/-- **Voevodsky's theorem (the Milnor conjecture): formalised statement and proved cases.**

1. In degree zero the norm-residue statement holds over every field.
2. The full conjecture holds for separably closed fields of characteristic `≠ 2`.
3. Over every field of characteristic `≠ 2` the degree one norm residue map
   `k^M_1(F) → H¹(Gal(F_sep/F), ℤ/2)` is an isomorphism (the base case of the conjecture,
   classical Kummer theory), so in particular `k^M_1(F) ≅ H¹(Gal(F_sep/F), ℤ/2)`. -/
theorem voevodsky_milnor :
    (∀ (F : Type u) [Field F], Nonempty (MilnorKMod2 F 0 ≃ₗ[ZMod 2] GaloisCohomologyMod2 F 0)) ∧
    (∀ (F : Type u) [Field F], IsSepClosed F → (2 : F) ≠ 0 → MilnorConjecture F) ∧
    (∀ (F : Type u) [Field F] (h2 : (2 : F) ≠ 0),
      Function.Bijective (normResidueOne F h2) ∧
      Nonempty (MilnorKMod2 F 1 ≃+ GaloisCohomologyMod2 F 1)) := by
  refine ⟨fun F _ => ⟨milnorDegreeZero F⟩, fun F _ hsc h2 => ?_, fun F _ h2 => ?_⟩
  · exact milnorConjecture_of_isSepClosed F h2
  · exact ⟨normResidueOne_bijective F h2,
      ⟨AddEquiv.ofBijective (normResidueOne F h2) (normResidueOne_bijective F h2)⟩⟩

end Frontier

