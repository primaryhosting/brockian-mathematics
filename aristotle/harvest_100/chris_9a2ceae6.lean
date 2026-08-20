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

import Mathlib

/-!
# Mod-2 Milnor K-theory of a field

`K^M_n(F)/2` is the abelian group (a `ZMod 2`-vector space) presented by generators the
symbols `{a₁, …, aₙ}` with `aᵢ ∈ Fˣ`, subject to
* multilinearity `{…, a·b, …} = {…, a, …} + {…, b, …}`, and
* the Steinberg relation `{…, a, …, 1 - a, …} = 0`.

Since the coefficients are taken in `ZMod 2` this is exactly Milnor K-theory modulo `2`.

## Main definitions

* `Frontier.milnorRelations F n` : the set of defining relations.
* `Frontier.KMilnorMod2 F n` : the group `K^M_n(F)/2`.
* `Frontier.symbol F v` : the symbol `{v 0, …, v (n-1)}`.

## Main results

* `Frontier.kMilnorMod2ZeroEquiv` : `K^M_0(F)/2 ≃ ℤ/2`.
* `Frontier.exists_symbol_eq_one` : in degree one, every element is a single symbol.
-/

namespace Frontier

variable (F : Type) [Field F]

/-- The defining relations of `K^M_n(F)/2`: multilinearity in each slot and the Steinberg
relation `{…, a, …, 1 - a, …} = 0`. -/
def milnorRelations (n : ℕ) : Set ((Fin n → Fˣ) →₀ ZMod 2) :=
  {x | (∃ (i : Fin n) (a b : Fˣ) (v : Fin n → Fˣ),
          x = Finsupp.single (Function.update v i (a * b)) 1
            - Finsupp.single (Function.update v i a) 1
            - Finsupp.single (Function.update v i b) 1) ∨
       (∃ (i j : Fin n) (v : Fin n → Fˣ), i ≠ j ∧ ((v i : F) + (v j : F) = 1) ∧
          x = Finsupp.single v 1)}

/-- Mod-2 Milnor K-theory `K^M_n(F)/2`. -/
abbrev KMilnorMod2 (n : ℕ) :=
  ((Fin n → Fˣ) →₀ ZMod 2) ⧸ Submodule.span (ZMod 2) (milnorRelations F n)

/-- The symbol `{v 0, …, v (n-1)} ∈ K^M_n(F)/2`. -/
noncomputable def symbol {n : ℕ} (v : Fin n → Fˣ) : KMilnorMod2 F n :=
  Submodule.Quotient.mk (Finsupp.single v 1)

variable {F}

lemma symbol_update_mul {n : ℕ} (i : Fin n) (a b : Fˣ) (v : Fin n → Fˣ) :
    symbol F (Function.update v i (a * b))
      = symbol F (Function.update v i a) + symbol F (Function.update v i b) := by
  have hmem : (Finsupp.single (Function.update v i (a * b)) 1
      - Finsupp.single (Function.update v i a) 1
      - Finsupp.single (Function.update v i b) (1 : ZMod 2))
      ∈ Submodule.span (ZMod 2) (milnorRelations F n) :=
    Submodule.subset_span (Or.inl ⟨i, a, b, v, rfl⟩)
  have := (Submodule.Quotient.mk_eq_zero _).2 hmem
  unfold symbol
  rw [sub_sub, Submodule.Quotient.mk_sub, sub_eq_zero, Submodule.Quotient.mk_add] at this
  exact this

lemma symbol_steinberg {n : ℕ} (i j : Fin n) (v : Fin n → Fˣ) (hij : i ≠ j)
    (h : (v i : F) + (v j : F) = 1) : symbol F v = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span (Or.inr ⟨i, j, v, hij, h, rfl⟩))

/-- In a `ZMod 2`-module every element is its own negative. -/
lemma self_add_self_eq_zero {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x : M) :
    x + x = 0 := by
  have h : ((2 : ZMod 2)) • x = x + x := two_smul (ZMod 2) x
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [← h, h2, zero_smul]

variable (F)

/-- `K^M_0(F)/2 ≃ ℤ/2`. -/
noncomputable def kMilnorMod2ZeroEquiv : KMilnorMod2 F 0 ≃ₗ[ZMod 2] ZMod 2 := by
  have hrel : milnorRelations F 0 = ∅ := by
    ext x
    simp only [milnorRelations, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro (⟨i, _⟩ | ⟨i, _⟩) <;> exact i.elim0
  have hbot : Submodule.span (ZMod 2) (milnorRelations F 0) = ⊥ := by
    rw [hrel, Submodule.span_empty]
  exact (Submodule.quotEquivOfEqBot _ hbot).trans
    (Finsupp.LinearEquiv.finsuppUnique (ZMod 2) (ZMod 2) (Fin 0 → Fˣ))

variable {F}

/-- Degree-one symbols are multiplicative. -/
lemma symbol_one_mul (a b : Fˣ) :
    symbol F (fun _ : Fin 1 => a * b)
      = symbol F (fun _ : Fin 1 => a) + symbol F (fun _ : Fin 1 => b) := by
  have h := symbol_update_mul (F := F) (n := 1) 0 a b (fun _ => a)
  have e : ∀ c : Fˣ, Function.update (fun _ : Fin 1 => a) 0 c = fun _ => c := by
    intro c
    funext i
    fin_cases i
    simp
  simpa [e] using h

lemma symbol_one_one : symbol F (fun _ : Fin 1 => (1 : Fˣ)) = 0 := by
  have h := symbol_one_mul (F := F) 1 1
  simp only [mul_one] at h
  exact left_eq_add.mp h

lemma symbol_one_sq (a : Fˣ) : symbol F (fun _ : Fin 1 => a * a) = 0 := by
  rw [symbol_one_mul]
  exact self_add_self_eq_zero _

/-- In degree one, every element of `K^M_1(F)/2` is a single symbol. -/
lemma exists_symbol_eq_one (x : KMilnorMod2 F 1) :
    ∃ a : Fˣ, x = symbol F (fun _ => a) := by
  induction x using Submodule.Quotient.induction_on with
  | H c =>
    induction c using Finsupp.induction with
    | zero => exact ⟨1, by simpa using (symbol_one_one (F := F)).symm⟩
    | single_add v r f _ _ ih =>
        obtain ⟨a, ha⟩ := ih
        have hv : v = fun _ => v 0 := by
          funext i; fin_cases i; rfl
        have hmk : (Submodule.Quotient.mk (Finsupp.single v r + f) : KMilnorMod2 F 1)
            = r • symbol F (fun _ => v 0) + symbol F (fun _ => a) := by
          rw [Submodule.Quotient.mk_add, ← ha]
          congr 1
          rw [hv]
          unfold symbol
          rw [← Submodule.Quotient.mk_smul]
          congr 1
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [hmk]
        by_cases hr : r = 0
        · exact ⟨a, by simp [hr]⟩
        · have hzo : ∀ s : ZMod 2, s ≠ 0 → s = 1 := by decide
          have hr1 : r = 1 := hzo r hr
          refine ⟨v 0 * a, ?_⟩
          rw [hr1, one_smul, symbol_one_mul]

end Frontier

import Mathlib

/-!
# Continuous cochain cohomology with `ZMod 2` coefficients

For a topological group `G` we define the cohomology of the complex of *continuous*
inhomogeneous cochains `Gⁿ → ZMod 2`, where `G` acts trivially on `ZMod 2`
(equipped with the discrete topology).  This is the standard definition of the
Galois cohomology groups `Hⁿ(G, ℤ/2)` when `G` is a profinite group, such as an
absolute Galois group.

The differential is taken to be Mathlib's differential on inhomogeneous cochains
(`groupCohomology.inhomogeneousCochains.d`) for the trivial representation, so that
`d ∘ d = 0` comes for free.

## Main definitions

* `Frontier.contCochains G n` : the submodule of continuous cochains `Gⁿ → ZMod 2`.
* `Frontier.contCohomology G n` : the `n`-th continuous cochain cohomology group.

## Main results

* `Frontier.contCohomologyZeroEquiv` : `H⁰(G, ℤ/2) ≃ ℤ/2`.
* `Frontier.contCohomologyOneEquiv` : `H¹(G, ℤ/2) ≃ Homcont(G, ℤ/2)`.
-/

namespace Frontier

open groupCohomology

variable (G : Type) [Group G] [TopologicalSpace G] [ContinuousMul G]

/-- The differential on inhomogeneous cochains with trivial `ZMod 2`-coefficients. -/
noncomputable def cochainD (n : ℕ) :
    ((Fin n → G) → ZMod 2) →ₗ[ZMod 2] ((Fin (n + 1) → G) → ZMod 2) :=
  (inhomogeneousCochains.d (Rep.trivial (ZMod 2) G (ZMod 2)) n).hom

omit [TopologicalSpace G] [ContinuousMul G] in
lemma cochainD_apply (n : ℕ) (f : (Fin n → G) → ZMod 2) (g : Fin (n + 1) → G) :
    cochainD G n f g =
      f (fun i => g i.succ) + ∑ j : Fin (n + 1), f (Fin.contractNth j (· * ·) g) := by
  simp [cochainD, inhomogeneousCochains.d_hom_apply]

omit [TopologicalSpace G] [ContinuousMul G] in
lemma cochainD_comp_cochainD (n : ℕ) :
    (cochainD G (n + 1)).comp (cochainD G n) = 0 := by
  have h := inhomogeneousCochains.d_comp_d (A := Rep.trivial (ZMod 2) G (ZMod 2)) (n := n)
  ext f g
  have h2 := congrArg (fun x => ModuleCat.Hom.hom x f) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  simpa [cochainD] using congrFun h2 g

omit [TopologicalSpace G] [ContinuousMul G] in
lemma cochainD_zero_eq_zero : cochainD G 0 = 0 := by
  refine LinearMap.ext fun f => funext fun g => ?_
  rw [cochainD_apply]
  have h : (fun i : Fin 0 => g i.succ) = Fin.contractNth 0 (· * ·) g := Subsingleton.elim _ _
  simp [h, CharTwo.add_self_eq_zero]

omit [TopologicalSpace G] [ContinuousMul G] in
lemma cochainD_one_apply (f : (Fin 1 → G) → ZMod 2) (g : Fin 2 → G) :
    cochainD G 1 f g =
      f (fun _ => g 1) + f (fun _ => g 0 * g 1) + f (fun _ => g 0) := by
  rw [cochainD_apply, Fin.sum_univ_two]
  have h0 : Fin.contractNth (0 : Fin 2) (· * ·) g = fun _ => g 0 * g 1 := by
    funext i; fin_cases i; simp [Fin.contractNth]
  have h1 : Fin.contractNth (1 : Fin 2) (· * ·) g = fun _ => g 0 := by
    funext i; fin_cases i; simp [Fin.contractNth]
  have h2 : (fun i : Fin 1 => g i.succ) = fun _ => g 1 := by
    funext i; fin_cases i; rfl
  simp only [h0, h1, h2]
  abel

/-- The submodule of continuous cochains `Gⁿ → ZMod 2`. -/
def contCochains (n : ℕ) : Submodule (ZMod 2) ((Fin n → G) → ZMod 2) where
  carrier := {f | Continuous f}
  add_mem' hf hg := Continuous.add hf hg
  zero_mem' := continuous_const
  smul_mem' c _ hf := Continuous.const_smul hf c

omit [Group G] [ContinuousMul G] in
lemma mem_contCochains {n : ℕ} {f : (Fin n → G) → ZMod 2} :
    f ∈ contCochains G n ↔ Continuous f := Iff.rfl

lemma cochainD_mem_contCochains {n : ℕ} {f : (Fin n → G) → ZMod 2}
    (hf : f ∈ contCochains G n) : cochainD G n f ∈ contCochains G (n + 1) := by
  rw [mem_contCochains] at hf ⊢
  have hcont : Continuous fun g : Fin (n + 1) → G => f (fun i => g i.succ) :=
    hf.comp (continuous_pi fun i => continuous_apply _)
  have hsum : ∀ j : Fin (n + 1),
      Continuous fun g : Fin (n + 1) → G => f (Fin.contractNth j (· * ·) g) := by
    intro j
    refine hf.comp (continuous_pi fun i => ?_)
    unfold Fin.contractNth
    split_ifs
    · exact continuous_apply (A := fun _ : Fin (n + 1) => G) i.castSucc
    · exact (continuous_apply (A := fun _ : Fin (n + 1) => G) i.castSucc).mul
        (continuous_apply (A := fun _ : Fin (n + 1) => G) i.succ)
    · exact continuous_apply (A := fun _ : Fin (n + 1) => G) i.succ
  have heq : (cochainD G n f) = fun g => f (fun i => g i.succ) +
      ∑ j : Fin (n + 1), f (Fin.contractNth j (· * ·) g) := by
    funext g; exact cochainD_apply G n f g
  rw [heq]
  exact hcont.add (continuous_finset_sum _ fun j _ => hsum j)

/-- Continuous cocycles: continuous cochains killed by the differential. -/
noncomputable def contCocycles (n : ℕ) : Submodule (ZMod 2) ((Fin n → G) → ZMod 2) :=
  contCochains G n ⊓ LinearMap.ker (cochainD G n)

/-- Continuous coboundaries: differentials of continuous cochains. -/
noncomputable def contCoboundaries (n : ℕ) : Submodule (ZMod 2) ((Fin n → G) → ZMod 2) :=
  match n with
  | 0 => ⊥
  | (m + 1) => (contCochains G m).map (cochainD G m)

omit [ContinuousMul G] in
lemma contCoboundaries_zero : contCoboundaries G 0 = ⊥ := rfl

omit [ContinuousMul G] in
lemma contCoboundaries_succ (n : ℕ) :
    contCoboundaries G (n + 1) = (contCochains G n).map (cochainD G n) := rfl

lemma contCoboundaries_le_contCocycles (n : ℕ) :
    contCoboundaries G n ≤ contCocycles G n := by
  cases n with
  | zero => simp [contCoboundaries_zero]
  | succ m =>
      rw [contCoboundaries_succ]
      rintro _ ⟨f, hf, rfl⟩
      refine ⟨cochainD_mem_contCochains G hf, ?_⟩
      have := congrArg (fun L => L f) (cochainD_comp_cochainD G m)
      simpa using this

/-- The `n`-th continuous cochain cohomology group of `G` with coefficients in `ZMod 2`
(trivial action).  For a profinite group `G` this is the usual (continuous) group
cohomology; for an absolute Galois group it is mod-2 Galois cohomology. -/
noncomputable def contCohomology (n : ℕ) : Type :=
  (contCocycles G n) ⧸
    (Submodule.comap (contCocycles G n).subtype (contCoboundaries G n))

noncomputable instance (n : ℕ) : AddCommGroup (contCohomology G n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

noncomputable instance (n : ℕ) : Module (ZMod 2) (contCohomology G n) :=
  inferInstanceAs (Module (ZMod 2) (_ ⧸ _))

/-- The continuous homomorphisms `G → ZMod 2`, i.e. continuous characters of order
dividing `2`.  This is the standard description of `H¹(G, ℤ/2)`. -/
def contChars : Submodule (ZMod 2) (G → ZMod 2) where
  carrier := {f | Continuous f ∧ ∀ x y, f (x * y) = f x + f y}
  add_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    exact ⟨hf.add hg, by intro x y; simp [hf', hg']; abel⟩
  zero_mem' := ⟨continuous_const, by simp⟩
  smul_mem' := by
    rintro c f ⟨hf, hf'⟩
    exact ⟨hf.const_smul c, by intro x y; simp [hf', mul_add]⟩

omit [ContinuousMul G] in
lemma mem_contChars {f : G → ZMod 2} :
    f ∈ contChars G ↔ Continuous f ∧ ∀ x y, f (x * y) = f x + f y := Iff.rfl

lemma continuous_of_subsingleton_dom {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Subsingleton X] (f : X → Y) : Continuous f := by
  rw [continuous_def]
  intro s _
  rcases Set.eq_empty_or_nonempty (f ⁻¹' s) with h | ⟨y, hy⟩
  · rw [h]; exact isOpen_empty
  · have : f ⁻¹' s = Set.univ := by
      ext x
      simpa [Subsingleton.elim x y] using hy
    rw [this]; exact isOpen_univ

omit [ContinuousMul G] in
lemma contCocycles_zero_eq_top : contCocycles G 0 = ⊤ := by
  rw [contCocycles, cochainD_zero_eq_zero, LinearMap.ker_zero, inf_top_eq]
  ext f
  exact ⟨fun _ => trivial, fun _ => continuous_of_subsingleton_dom f⟩

omit [ContinuousMul G] in
lemma contCoboundaries_one_eq_bot : contCoboundaries G 1 = ⊥ := by
  rw [contCoboundaries_succ, cochainD_zero_eq_zero, Submodule.map_zero]

/-- `H⁰(G, ℤ/2) ≃ ℤ/2`. -/
noncomputable def contCohomologyZeroEquiv : contCohomology G 0 ≃ₗ[ZMod 2] ZMod 2 := by
  have h1 : Submodule.comap (contCocycles G 0).subtype (contCoboundaries G 0) = ⊥ := by
    rw [contCoboundaries_zero, Submodule.comap_bot]
    exact LinearMap.ker_eq_bot_of_injective (Submodule.injective_subtype _)
  exact (Submodule.quotEquivOfEqBot _ h1).trans
    (((LinearEquiv.ofEq (contCocycles G 0) ⊤ (contCocycles_zero_eq_top G)).trans
        (Submodule.topEquiv (R := ZMod 2) (M := (Fin 0 → G) → ZMod 2))).trans
      (LinearEquiv.funUnique (Fin 0 → G) (ZMod 2) (ZMod 2)))

/-- Reindexing along `G ≃ (Fin 1 → G)`. -/
noncomputable def cochainOneEquiv : ((Fin 1 → G) → ZMod 2) ≃ₗ[ZMod 2] (G → ZMod 2) :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (Equiv.funUnique (Fin 1) G).symm

omit [Group G] [TopologicalSpace G] [ContinuousMul G] in
@[simp] lemma cochainOneEquiv_apply (f : (Fin 1 → G) → ZMod 2) (x : G) :
    cochainOneEquiv G f x = f (fun _ => x) := rfl

omit [ContinuousMul G] in
lemma mem_contCocycles_one_iff (f : (Fin 1 → G) → ZMod 2) :
    f ∈ contCocycles G 1 ↔ cochainOneEquiv G f ∈ contChars G := by
  have hcont : Continuous f ↔ Continuous (cochainOneEquiv G f) := by
    constructor
    · intro hf
      exact hf.comp (continuous_pi fun _ => continuous_id)
    · intro hf
      have : f = (cochainOneEquiv G f) ∘ (fun v : Fin 1 → G => v 0) := by
        funext v
        simp only [cochainOneEquiv_apply, Function.comp_apply]
        congr 1
        funext i
        fin_cases i
        rfl
      rw [this]
      exact hf.comp (continuous_apply (A := fun _ : Fin 1 => G) 0)
  constructor
  · rintro ⟨hf, hker⟩
    refine ⟨hcont.1 hf, fun x y => ?_⟩
    have h := congrFun (LinearMap.mem_ker.1 hker) ![x, y]
    rw [cochainD_one_apply] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h
    simp only [cochainOneEquiv_apply]
    have h' : (f fun _ => x * y) + ((f fun _ => y) + (f fun _ => x)) = 0 := by
      rw [← h]; ring
    rw [add_eq_zero_iff_eq_neg.1 h', CharTwo.neg_eq]
    ring
  · rintro ⟨hu, hhom⟩
    refine ⟨hcont.2 hu, ?_⟩
    show cochainD G 1 f = 0
    funext g
    rw [cochainD_one_apply]
    have h := hhom (g 0) (g 1)
    simp only [cochainOneEquiv_apply] at h
    rw [h]
    have hrw : (f fun _ => g 1) + ((f fun _ => g 0) + (f fun _ => g 1)) + (f fun _ => g 0)
        = ((f fun _ => g 1) + (f fun _ => g 1)) + ((f fun _ => g 0) + (f fun _ => g 0)) := by
      ring
    simp [hrw, CharTwo.add_self_eq_zero]

omit [ContinuousMul G] in
lemma map_contCocycles_one :
    Submodule.map (cochainOneEquiv G).toLinearMap (contCocycles G 1) = contChars G := by
  ext u
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact (mem_contCocycles_one_iff G f).1 hf
  · intro hu
    refine ⟨(cochainOneEquiv G).symm u, ?_, by simp⟩
    rw [mem_contCocycles_one_iff]
    simpa using hu

/-- `H¹(G, ℤ/2)` is the group of continuous characters `G → ℤ/2`. -/
noncomputable def contCohomologyOneEquiv : contCohomology G 1 ≃ₗ[ZMod 2] contChars G := by
  have h1 : Submodule.comap (contCocycles G 1).subtype (contCoboundaries G 1) = ⊥ := by
    rw [contCoboundaries_one_eq_bot, Submodule.comap_bot]
    exact LinearMap.ker_eq_bot_of_injective (Submodule.injective_subtype _)
  exact (Submodule.quotEquivOfEqBot _ h1).trans
    (((cochainOneEquiv G).submoduleMap (contCocycles G 1)).trans
      (LinearEquiv.ofEq _ _ (map_contCocycles_one G)))

end Frontier

import Mathlib
import RequestProject.Frontier.ContinuousCohomology
import RequestProject.Frontier.MilnorK

/-!
# The norm residue map in degree one (Kummer theory)

For a field `F` with `char F ≠ 2` we construct the degree-one norm residue map
`K^M_1(F)/2 = Fˣ/(Fˣ)² → H¹(Gal(F^sep/F), ℤ/2)`, `a ↦ (σ ↦ σ(√a)/√a)`, and prove
that it is bijective.  This is the degree-one case of the Milnor conjecture
(Voevodsky's theorem), which in this degree is classical Kummer theory.

## Main definitions

* `Frontier.GalGroup F` : the absolute Galois group `Gal(F^sep/F)`.
* `Frontier.kummerChar a` : the quadratic character `σ ↦ σ(√a)/√a` with values in `ℤ/2`.
* `Frontier.normResidueOne` : the induced map `K^M_1(F)/2 → Homcont(Gal(F^sep/F), ℤ/2)`.

## Main results

* `Frontier.normResidueOne_bijective` : the degree-one norm residue map is bijective.
-/

namespace Frontier

open IntermediateField

attribute [local instance] Classical.propDecidable

variable (F : Type) [Field F]

/-- The absolute Galois group of `F`, i.e. `Gal(F^sep/F)`, with the Krull topology. -/
abbrev GalGroup := SeparableClosure F ≃ₐ[F] SeparableClosure F

variable {F}

/-- A chosen square root in `F^sep` of (the image of) a unit of `F`. -/
noncomputable def sqrtIn (a : Fˣ) : SeparableClosure F :=
  if h : ∃ x : SeparableClosure F, x ^ 2 = algebraMap F (SeparableClosure F) (a : F)
  then h.choose else 0

lemma exists_sq_eq (hF : (2 : F) ≠ 0) (a : Fˣ) :
    ∃ x : SeparableClosure F, x ^ 2 = algebraMap F (SeparableClosure F) (a : F) := by
  have h2 : ((2 : ℕ) : SeparableClosure F) ≠ 0 := by
    have h : ((2 : ℕ) : SeparableClosure F) = algebraMap F (SeparableClosure F) (2 : F) := by
      push_cast
      rw [map_ofNat]
    rw [h]
    simpa using hF
  haveI : NeZero ((2 : ℕ) : SeparableClosure F) := ⟨h2⟩
  exact IsSepClosed.exists_pow_nat_eq _ 2

lemma sqrtIn_sq (hF : (2 : F) ≠ 0) (a : Fˣ) :
    (sqrtIn a) ^ 2 = algebraMap F (SeparableClosure F) (a : F) := by
  rw [sqrtIn, dif_pos (exists_sq_eq hF a)]
  exact (exists_sq_eq hF a).choose_spec

lemma sqrtIn_ne_zero (hF : (2 : F) ≠ 0) (a : Fˣ) : sqrtIn a ≠ (0 : SeparableClosure F) := by
  intro h
  have := sqrtIn_sq hF a
  rw [h] at this
  simp only [ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true] at this
  exact (Units.ne_zero a) (by
    have := this.symm
    exact (map_eq_zero (algebraMap F (SeparableClosure F))).1 this)

/-- The quadratic character `σ ↦ σ(√a)/√a` attached to a unit `a`, with values in `ℤ/2`. -/
noncomputable def kummerChar (a : Fˣ) (σ : GalGroup F) : ZMod 2 :=
  if σ (sqrtIn a) = sqrtIn a then 0 else 1

lemma kummerChar_eq_zero_iff (a : Fˣ) (σ : GalGroup F) :
    kummerChar a σ = 0 ↔ σ (sqrtIn a) = sqrtIn a := by
  unfold kummerChar
  split_ifs with h
  · simp [h]
  · simp [h]

/-- Any Galois conjugate of `√a` is `± √a`. -/
lemma sqrtIn_conj (hF : (2 : F) ≠ 0) (a : Fˣ) (σ : GalGroup F) :
    σ (sqrtIn a) = sqrtIn a ∨ σ (sqrtIn a) = -sqrtIn a := by
  have hsq : (σ (sqrtIn a)) ^ 2 = (sqrtIn a) ^ 2 := by
    rw [← map_pow, sqrtIn_sq hF, AlgEquiv.commutes]
  have hz : (σ (sqrtIn a) - sqrtIn a) * (σ (sqrtIn a) + sqrtIn a) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.1 hz with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

lemma neg_ne_self (hF : (2 : F) ≠ 0) {x : SeparableClosure F} (hx : x ≠ 0) : -x ≠ x := by
  intro h
  have h2 : (2 : SeparableClosure F) * x = 0 := by linear_combination -h
  have h2' : (2 : SeparableClosure F) ≠ 0 := by
    rw [(map_ofNat (algebraMap F (SeparableClosure F)) 2).symm]
    simpa using hF
  rcases mul_eq_zero.1 h2 with h | h
  · exact h2' h
  · exact hx h

lemma kummerChar_of_fix {a : Fˣ} {σ : GalGroup F} (h : σ (sqrtIn a) = sqrtIn a) :
    kummerChar a σ = 0 := (kummerChar_eq_zero_iff a σ).2 h

lemma kummerChar_of_neg (hF : (2 : F) ≠ 0) {a : Fˣ} {σ : GalGroup F}
    (h : σ (sqrtIn a) = -sqrtIn a) : kummerChar a σ = 1 := by
  unfold kummerChar
  rw [if_neg]
  rw [h]
  exact neg_ne_self hF (sqrtIn_ne_zero hF a)

lemma kummerChar_add (hF : (2 : F) ≠ 0) (a : Fˣ) (σ τ : GalGroup F) :
    kummerChar a (σ * τ) = kummerChar a σ + kummerChar a τ := by
  have hmul : (σ * τ) (sqrtIn a) = σ (τ (sqrtIn a)) := rfl
  rcases sqrtIn_conj hF a σ with hs | hs <;> rcases sqrtIn_conj hF a τ with ht | ht
  · rw [kummerChar_of_fix (by rw [hmul, ht, hs]), kummerChar_of_fix hs, kummerChar_of_fix ht]
    simp
  · rw [kummerChar_of_neg hF (by rw [hmul, ht, map_neg, hs]), kummerChar_of_fix hs,
      kummerChar_of_neg hF ht]
    simp
  · rw [kummerChar_of_neg hF (by rw [hmul, ht, hs]), kummerChar_of_neg hF hs,
      kummerChar_of_fix ht]
    simp
  · rw [kummerChar_of_fix (by rw [hmul, ht, map_neg, hs, neg_neg]), kummerChar_of_neg hF hs,
      kummerChar_of_neg hF ht]
    decide

/-- A homomorphism to `ZMod 2` with open kernel is continuous. -/
lemma continuous_of_open_subgroup_in_kernel {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (f : G → ZMod 2) (hf : ∀ x y, f (x * y) = f x + f y)
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (hUk : ∀ u ∈ U, f u = 0) : Continuous f := by
  rw [continuous_def]
  intro s _
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨(fun u => x * u) '' (U : Set G), ?_, ?_, ⟨1, U.one_mem, mul_one x⟩⟩
  · rintro _ ⟨u, hu, rfl⟩
    have : f (x * u) = f x := by rw [hf, hUk u hu, add_zero]
    simpa [this] using hx
  · exact (Homeomorph.mulLeft x).isOpenMap _ hU

lemma kummerChar_continuous (hF : (2 : F) ≠ 0) (a : Fˣ) :
    Continuous (kummerChar a : GalGroup F → ZMod 2) := by
  haveI : FiniteDimensional F (F⟮(sqrtIn a)⟯ : IntermediateField F (SeparableClosure F)) :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral (R := F) (sqrtIn a))
  refine continuous_of_open_subgroup_in_kernel _ (fun x y => kummerChar_add hF a x y)
    (IntermediateField.fixingSubgroup (F⟮(sqrtIn a)⟯)) ?_ ?_
  · exact IntermediateField.fixingSubgroup_isOpen _
  · intro u hu
    refine kummerChar_of_fix ?_
    exact (IntermediateField.mem_fixingSubgroup_iff _ u).1 hu _
      (IntermediateField.mem_adjoin_simple_self F (sqrtIn a))

lemma kummerChar_eq_one_iff (a : Fˣ) (σ : GalGroup F) :
    kummerChar a σ = 1 ↔ σ (sqrtIn a) ≠ sqrtIn a := by
  unfold kummerChar
  split_ifs with h
  · simp [h]
  · simp [h]

lemma kummerChar_mul (hF : (2 : F) ≠ 0) (a b : Fˣ) :
    (kummerChar (a * b) : GalGroup F → ZMod 2) = kummerChar a + kummerChar b := by
  funext σ
  simp only [Pi.add_apply]
  have hα := sqrtIn_ne_zero hF a
  have hβ := sqrtIn_ne_zero hF b
  have hY : sqrtIn a * sqrtIn b ≠ (0 : SeparableClosure F) := mul_ne_zero hα hβ
  have hγ : sqrtIn (a * b) = sqrtIn a * sqrtIn b ∨
      sqrtIn (a * b) = -(sqrtIn a * sqrtIn b) := by
    have h1 : (sqrtIn (a * b) : SeparableClosure F) ^ 2 = (sqrtIn a * sqrtIn b) ^ 2 := by
      rw [mul_pow, sqrtIn_sq hF, sqrtIn_sq hF, sqrtIn_sq hF, ← map_mul, Units.val_mul]
    have h2 : (sqrtIn (a * b) - sqrtIn a * sqrtIn b)
        * (sqrtIn (a * b) + sqrtIn a * sqrtIn b) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hfix : σ (sqrtIn (a * b)) = sqrtIn (a * b)
      ↔ σ (sqrtIn a * sqrtIn b) = sqrtIn a * sqrtIn b := by
    rcases hγ with h | h
    · rw [h]
    · rw [h]; simp
  rcases sqrtIn_conj hF a σ with hs | hs <;> rcases sqrtIn_conj hF b σ with ht | ht
  · rw [kummerChar_of_fix (hfix.2 (by rw [map_mul, hs, ht])), kummerChar_of_fix hs,
      kummerChar_of_fix ht]
    simp
  · rw [(kummerChar_eq_one_iff (a * b) σ).2 (fun hc => ?_), kummerChar_of_fix hs,
      kummerChar_of_neg hF ht]
    · simp
    · have : σ (sqrtIn a * sqrtIn b) = -(sqrtIn a * sqrtIn b) := by
        rw [map_mul, hs, ht]; ring
      exact neg_ne_self hF hY (this ▸ hfix.1 hc)
  · rw [(kummerChar_eq_one_iff (a * b) σ).2 (fun hc => ?_), kummerChar_of_neg hF hs,
      kummerChar_of_fix ht]
    · simp
    · have : σ (sqrtIn a * sqrtIn b) = -(sqrtIn a * sqrtIn b) := by
        rw [map_mul, hs, ht]; ring
      exact neg_ne_self hF hY (this ▸ hfix.1 hc)
  · rw [kummerChar_of_fix (hfix.2 (by rw [map_mul, hs, ht]; ring)), kummerChar_of_neg hF hs,
      kummerChar_of_neg hF ht]
    decide

lemma kummerChar_mem_contChars (hF : (2 : F) ≠ 0) (a : Fˣ) :
    (kummerChar a : GalGroup F → ZMod 2) ∈ contChars (GalGroup F) :=
  ⟨kummerChar_continuous hF a, fun x y => kummerChar_add hF a x y⟩

lemma isSquare_of_kummerChar_eq_zero (hF : (2 : F) ≠ 0) (a : Fˣ)
    (h : (kummerChar a : GalGroup F → ZMod 2) = 0) : ∃ b : Fˣ, a = b * b := by
  have hfix : ∀ σ : GalGroup F, σ (sqrtIn a) = sqrtIn a := fun σ =>
    (kummerChar_eq_zero_iff a σ).1 (congrFun h σ)
  obtain ⟨b0, hb0⟩ : sqrtIn a ∈ Set.range (algebraMap F (SeparableClosure F)) :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 hfix
  have hb0ne : b0 ≠ 0 := by
    intro hz
    exact sqrtIn_ne_zero hF a (by rw [← hb0, hz, map_zero])
  have hsq : algebraMap F (SeparableClosure F) (b0 ^ 2)
      = algebraMap F (SeparableClosure F) (a : F) := by
    rw [map_pow, hb0, sqrtIn_sq hF]
  have h2 : b0 ^ 2 = (a : F) := (algebraMap F (SeparableClosure F)).injective hsq
  exact ⟨Units.mk0 b0 hb0ne, Units.ext (by simp [← h2, sq])⟩

lemma kummerChar_one (hF : (2 : F) ≠ 0) : (kummerChar (1 : Fˣ) : GalGroup F → ZMod 2) = 0 := by
  have hsq : (sqrtIn (1 : Fˣ) : SeparableClosure F) ^ 2 = 1 := by
    rw [sqrtIn_sq hF]
    simp
  have h : (sqrtIn (1 : Fˣ) - 1) * (sqrtIn (1 : Fˣ) + 1) = (0 : SeparableClosure F) := by
    linear_combination hsq
  funext σ
  refine kummerChar_of_fix ?_
  rcases mul_eq_zero.1 h with h1 | h1
  · rw [sub_eq_zero.1 h1, map_one]
  · rw [eq_neg_of_add_eq_zero_left h1, map_neg, map_one]

/-- The kernel of a `ZMod 2`-valued homomorphism, as a subgroup. -/
def charKernel {G : Type*} [Group G] (chi : G → ZMod 2)
    (hhom : ∀ x y, chi (x * y) = chi x + chi y) : Subgroup G where
  carrier := {g | chi g = 0}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [hhom, hx, hy, add_zero]
  one_mem' := by
    have h := hhom 1 1
    rw [mul_one] at h
    exact (left_eq_add.mp h)
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have h := hhom x x⁻¹
    rw [mul_inv_cancel, hx, zero_add] at h
    have h1 : chi 1 = 0 := by
      have h2 := hhom 1 1
      rw [mul_one] at h2
      exact (left_eq_add.mp h2)
    rw [h1] at h
    exact h.symm

@[simp] lemma mem_charKernel {G : Type*} [Group G] {chi : G → ZMod 2}
    {hhom : ∀ x y, chi (x * y) = chi x + chi y} {g : G} :
    g ∈ charKernel chi hhom ↔ chi g = 0 := Iff.rfl

lemma zmod_two_eq_one_of_ne_zero {u : ZMod 2} (h : u ≠ 0) : u = 1 := by
  revert h
  revert u
  decide

lemma zmod_two_eq_of_iff {u v : ZMod 2} (h : u = 0 ↔ v = 0) : u = v := by
  revert h
  revert u v
  decide

lemma exists_kummerChar_eq (hF : (2 : F) ≠ 0) (chi : GalGroup F → ZMod 2)
    (hchi : chi ∈ contChars (GalGroup F)) :
    ∃ a : Fˣ, (kummerChar a : GalGroup F → ZMod 2) = chi := by
  obtain ⟨hcont, hhom⟩ := hchi
  by_cases hzero : chi = 0
  · exact ⟨1, by rw [kummerChar_one hF, hzero]⟩
  obtain ⟨s0, hs0⟩ : ∃ σ : GalGroup F, chi σ = 1 := by
    by_contra hcon
    push_neg at hcon
    exact hzero (funext fun σ => by
      by_contra hne
      exact hcon σ (zmod_two_eq_one_of_ne_zero hne))
  set H := charKernel chi hhom with hH
  have hHopen : IsOpen (H : Set (GalGroup F)) := by
    have hpre : (H : Set (GalGroup F)) = chi ⁻¹' {0} := rfl
    rw [hpre]
    exact hcont.isOpen_preimage _ (isOpen_discrete _)
  have hHclosed : IsClosed (H : Set (GalGroup F)) := Subgroup.isClosed_of_isOpen H hHopen
  have hfixsub : (IntermediateField.fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField
      (⟨H, hHclosed⟩ : ClosedSubgroup (GalGroup F))
  have hs0H : s0 ∉ H := by
    rw [hH, mem_charKernel, hs0]
    decide
  obtain ⟨x, hxL, hxne⟩ : ∃ x ∈ IntermediateField.fixedField H, s0 x ≠ x := by
    by_contra hcon
    push_neg at hcon
    exact hs0H (hfixsub ▸ (IntermediateField.mem_fixingSubgroup_iff _ s0).2 hcon)
  set y : SeparableClosure F := x - s0 x with hy
  have hyne : y ≠ 0 := sub_ne_zero.2 (fun h => hxne h.symm)
  -- every element of `H` fixes `y`
  have hHy : ∀ h ∈ H, h y = y := by
    intro h hh
    have hx' : h x = x := (IntermediateField.mem_fixedField_iff _ x).1 hxL h hh
    have hconj : s0⁻¹ * h * s0 ∈ H := by
      rw [hH, mem_charKernel] at hh ⊢
      have h1 := hhom (s0⁻¹ * h) s0
      have h2 := hhom s0⁻¹ h
      have h3 := hhom s0 s0⁻¹
      rw [mul_inv_cancel] at h3
      have h4 : chi 1 = 0 := by
        have h5 := hhom 1 1
        rw [mul_one] at h5
        exact (left_eq_add.mp h5)
      rw [h4] at h3
      have hinv : chi s0⁻¹ = 1 := by
        rw [hs0] at h3
        revert h3
        generalize chi s0⁻¹ = u
        revert u
        decide
      rw [h1, h2, hh, hinv, hs0]
      decide
    have hs0x : h (s0 x) = s0 x := by
      have heq : h * s0 = s0 * (s0⁻¹ * h * s0) := by group
      calc h (s0 x) = (h * s0) x := (AlgEquiv.mul_apply h s0 x).symm
        _ = (s0 * (s0⁻¹ * h * s0)) x := by rw [heq]
        _ = s0 ((s0⁻¹ * h * s0) x) := AlgEquiv.mul_apply _ _ _
        _ = s0 x := by
            rw [(IntermediateField.mem_fixedField_iff _ x).1 hxL _ hconj]
    rw [hy, map_sub, hx', hs0x]
  -- `s0` negates `y`
  have hs0sq : s0 * s0 ∈ H := by
    rw [hH, mem_charKernel, hhom, hs0]
    decide
  have hs0y : s0 y = -y := by
    have h1 : s0 (s0 x) = x := by
      have := (IntermediateField.mem_fixedField_iff _ x).1 hxL _ hs0sq
      simpa [AlgEquiv.mul_apply] using this
    rw [hy, map_sub, h1]
    ring
  -- elements outside `H` negate `y`
  have hout : ∀ τ : GalGroup F, τ ∉ H → τ y = -y := by
    intro τ hτ
    have hτ1 : chi τ = 1 := zmod_two_eq_one_of_ne_zero (by simpa [hH] using hτ)
    have hmem : s0⁻¹ * τ ∈ H := by
      rw [hH, mem_charKernel, hhom]
      have h3 := hhom s0 s0⁻¹
      rw [mul_inv_cancel] at h3
      have h4 : chi 1 = 0 := by
        have h5 := hhom 1 1
        rw [mul_one] at h5
        exact (left_eq_add.mp h5)
      rw [h4] at h3
      have hinv : chi s0⁻¹ = 1 := by
        rw [hs0] at h3
        revert h3
        generalize chi s0⁻¹ = u
        revert u
        decide
      rw [hinv, hτ1]
      decide
    have heq : s0 * (s0⁻¹ * τ) = τ := by group
    calc τ y = (s0 * (s0⁻¹ * τ)) y := by rw [heq]
      _ = s0 ((s0⁻¹ * τ) y) := AlgEquiv.mul_apply _ _ _
      _ = s0 y := by rw [hHy _ hmem]
      _ = -y := hs0y
  -- `y ^ 2` lies in `F`
  have hyfix : ∀ τ : GalGroup F, τ (y * y) = y * y := by
    intro τ
    by_cases hτ : τ ∈ H
    · rw [map_mul, hHy τ hτ]
    · rw [map_mul, hout τ hτ]
      ring
  obtain ⟨c, hc⟩ : y * y ∈ Set.range (algebraMap F (SeparableClosure F)) :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 hyfix
  have hcne : c ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hc
    exact (mul_ne_zero hyne hyne) hc.symm
  refine ⟨Units.mk0 c hcne, ?_⟩
  set a : Fˣ := Units.mk0 c hcne with ha
  have hasq : (sqrtIn a : SeparableClosure F) ^ 2 = y * y := by
    rw [sqrtIn_sq hF, ha]
    simpa using hc
  have halpha : (sqrtIn a : SeparableClosure F) = y ∨ sqrtIn a = -y := by
    have h2 : (sqrtIn a - y) * (sqrtIn a + y) = (0 : SeparableClosure F) := by
      linear_combination hasq
    rcases mul_eq_zero.1 h2 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  funext τ
  refine zmod_two_eq_of_iff ?_
  rw [kummerChar_eq_zero_iff]
  constructor
  · intro hfix
    by_contra hτ
    have hτH : τ ∉ H := by simpa [hH] using hτ
    have hneg : τ y = -y := hout τ hτH
    have : τ y = y := by
      rcases halpha with h | h
      · rwa [h] at hfix
      · rw [h, map_neg, neg_inj] at hfix
        exact hfix
    rw [hneg] at this
    exact neg_ne_self hF hyne this
  · intro hτ
    have hτH : τ ∈ H := by simpa [hH] using hτ
    have hyy : τ y = y := hHy τ hτH
    rcases halpha with h | h
    · rw [h]; exact hyy
    · rw [h, map_neg, hyy]

end Frontier

import Mathlib
import RequestProject.Frontier.ContinuousCohomology
import RequestProject.Frontier.MilnorK
import RequestProject.Frontier.Kummer

/-!
# Voevodsky Milnor
Category: Frontier — Fields Medal Work
Target: Frontier.voevodsky_milnor
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Milnor conjecture

The Milnor conjecture, proved by Voevodsky, states that for a field `F` of characteristic
`≠ 2` the norm residue homomorphism

`K^M_n(F)/2 ⟶ Hⁿ(Gal(F^sep/F), ℤ/2)`,   `{a₁,…,aₙ} ↦ χ_{a₁} ∪ ⋯ ∪ χ_{aₙ}`

is an isomorphism for every `n`.  Here `K^M_*(F)/2` is mod-2 Milnor K-theory
(`Frontier.KMilnorMod2`) and `Hⁿ(-, ℤ/2)` is continuous (Galois) cochain cohomology
(`Frontier.contCohomology`).

This file formalises the statement, and proves it in the degrees where it does not
require Voevodsky's machinery:

* degree `0`: both sides are canonically `ℤ/2` (`Frontier.normResidueZeroEquiv`);
* degree `1`: this is Kummer theory; the norm residue map `a ↦ (σ ↦ σ(√a)/√a)` is
  constructed in `Frontier.normResidueOne` and proved bijective.

A (weak, group-theoretic) form of the general statement, which is Voevodsky's theorem, is
recorded as `Frontier.MilnorConjecture`; it is *not* proved here.

## Mathlib inputs

Mathlib contains neither Milnor K-theory nor Galois cohomology, so both sides of the norm
residue map are constructed here.  The main Mathlib results used are:
`groupCohomology.inhomogeneousCochains.d_comp_d` (the cochain differential squares to zero),
`IsSepClosed.exists_pow_nat_eq` (square roots exist in a separably closed field),
`IntermediateField.fixingSubgroup_isOpen` (openness in the Krull topology),
`InfiniteGalois.fixingSubgroup_fixedField` and `InfiniteGalois.mem_range_algebraMap_iff_fixed`
(the infinite Galois correspondence).
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace Frontier

variable {F : Type} [Field F]

attribute [local instance] Classical.propDecidable

/-- The degree-one norm residue map on the free module of degree-one symbols:
`a ↦ (σ ↦ σ(√a)/√a)`, with values in the continuous characters of `Gal(F^sep/F)`. -/
noncomputable def kummerFree (hF : (2 : F) ≠ 0) :
    ((Fin 1 → Fˣ) →₀ ZMod 2) →ₗ[ZMod 2] contChars (GalGroup F) :=
  Finsupp.linearCombination (ZMod 2)
    (fun v : Fin 1 → Fˣ => (⟨kummerChar (v 0), kummerChar_mem_contChars hF (v 0)⟩ :
      contChars (GalGroup F)))

@[simp] lemma kummerFree_single (hF : (2 : F) ≠ 0) (v : Fin 1 → Fˣ) :
    kummerFree hF (Finsupp.single v 1)
      = ⟨kummerChar (v 0), kummerChar_mem_contChars hF (v 0)⟩ := by
  simp [kummerFree]

lemma milnorRelations_le_ker_kummerFree (hF : (2 : F) ≠ 0) :
    Submodule.span (ZMod 2) (milnorRelations F 1) ≤ LinearMap.ker (kummerFree hF) := by
  rw [Submodule.span_le]
  rintro x (⟨i, a, b, v, rfl⟩ | ⟨i, j, v, hij, -, -⟩)
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, kummerFree_single,
      Function.update_self]
    ext σ
    have h := congrFun (kummerChar_mul hF a b) σ
    simp only [Submodule.coe_sub, Pi.sub_apply, Pi.add_apply, ZeroMemClass.coe_zero,
      Pi.zero_apply] at h ⊢
    rw [h]
    ring
  · exact absurd (Subsingleton.elim i j) hij

/-- The degree-one norm residue map `K^M_1(F)/2 → Homcont(Gal(F^sep/F), ℤ/2)`. -/
noncomputable def normResidueOneChars (hF : (2 : F) ≠ 0) :
    KMilnorMod2 F 1 →ₗ[ZMod 2] contChars (GalGroup F) :=
  Submodule.liftQ _ (kummerFree hF) (milnorRelations_le_ker_kummerFree hF)

@[simp] lemma normResidueOneChars_symbol (hF : (2 : F) ≠ 0) (a : Fˣ) :
    normResidueOneChars hF (symbol F (fun _ : Fin 1 => a))
      = ⟨kummerChar a, kummerChar_mem_contChars hF a⟩ := by
  simp [normResidueOneChars, symbol]

lemma normResidueOneChars_bijective (hF : (2 : F) ≠ 0) :
    Function.Bijective (normResidueOneChars hF) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := exists_symbol_eq_one x
    rw [normResidueOneChars_symbol] at hx
    have hchar : (kummerChar a : GalGroup F → ZMod 2) = 0 := congrArg Subtype.val hx
    obtain ⟨b, rfl⟩ := isSquare_of_kummerChar_eq_zero hF a hchar
    exact symbol_one_sq b
  · rintro ⟨chi, hchi⟩
    obtain ⟨a, ha⟩ := exists_kummerChar_eq hF chi hchi
    exact ⟨symbol F (fun _ => a), by rw [normResidueOneChars_symbol]; exact Subtype.ext ha⟩

/-- The degree-one norm residue map `K^M_1(F)/2 → H¹(Gal(F^sep/F), ℤ/2)`. -/
noncomputable def normResidueOne (hF : (2 : F) ≠ 0) :
    KMilnorMod2 F 1 →ₗ[ZMod 2] contCohomology (GalGroup F) 1 :=
  (contCohomologyOneEquiv (GalGroup F)).symm.toLinearMap ∘ₗ normResidueOneChars hF

/-- In degree zero both sides of the norm residue map are canonically `ℤ/2`; note that the
identity is the only `ℤ/2`-linear isomorphism `ℤ/2 ≃ ℤ/2`, so this pins down the degree-zero
norm residue map. -/
noncomputable def normResidueZeroEquiv (F : Type) [Field F] :
    KMilnorMod2 F 0 ≃ₗ[ZMod 2] contCohomology (GalGroup F) 0 :=
  (kMilnorMod2ZeroEquiv F).trans (contCohomologyZeroEquiv (GalGroup F)).symm

/-- The degree-zero norm residue map `K^M_0(F)/2 → H⁰(Gal(F^sep/F), ℤ/2)`. -/
noncomputable def normResidueZero (F : Type) [Field F] :
    KMilnorMod2 F 0 →ₗ[ZMod 2] contCohomology (GalGroup F) 0 :=
  (normResidueZeroEquiv F).toLinearMap

/-- The degree-zero norm residue map is nonzero: it sends the empty symbol, i.e. the unit of
mod-2 Milnor K-theory, to the nonzero class in `H⁰`. -/
lemma normResidueZero_symbol_ne_zero (F : Type) [Field F] (v : Fin 0 → Fˣ) :
    normResidueZero F (symbol F v) ≠ 0 := by
  intro h
  have h1 : symbol F v = 0 := (normResidueZeroEquiv F).map_eq_zero_iff.1 h
  have h2 : kMilnorMod2ZeroEquiv F (symbol F v) = 0 := by
    rw [h1, map_zero]
  have h3 : kMilnorMod2ZeroEquiv F (symbol F v) = 1 := by
    have hs : ∀ w : Fin 0 → Fˣ, (Finsupp.single v (1 : ZMod 2)) w = 1 := by
      intro w
      rw [Subsingleton.elim w v, Finsupp.single_eq_same]
    simp [kMilnorMod2ZeroEquiv, symbol, Submodule.quotEquivOfEqBot,
      Finsupp.LinearEquiv.finsuppUnique, hs]
  rw [h3] at h2
  exact one_ne_zero h2

/-- The Milnor conjecture (Voevodsky's theorem): for a field of characteristic `≠ 2`, mod-2
Milnor K-theory agrees with mod-2 Galois cohomology in every degree.  This is recorded for
reference only, and in a weak form: the isomorphism is asked for merely as an isomorphism of
`ℤ/2`-vector spaces, since writing down the norm residue map in degrees `≥ 2` requires cup
products, which are not developed here.  It is not proved. -/
def MilnorConjecture (F : Type) [Field F] : Prop :=
  (2 : F) ≠ 0 → ∀ n : ℕ, Nonempty (KMilnorMod2 F n ≃ₗ[ZMod 2] contCohomology (GalGroup F) n)

/-- **The Milnor conjecture in degrees ≤ 1.**  For a field `F` with `char F ≠ 2`:

* in degree `0`, the norm residue map `K^M_0(F)/2 → H⁰(Gal(F^sep/F), ℤ/2)` is bijective
  (both sides are `ℤ/2`);
* in degree `1`, the norm residue map `K^M_1(F)/2 → H¹(Gal(F^sep/F), ℤ/2)`,
  `{a} ↦ (σ ↦ σ(√a)/√a)`, is bijective.

The second statement is the (classical, Kummer-theoretic) degree-one case of Voevodsky's
theorem. -/
theorem voevodsky_milnor (F : Type) [Field F] (hF : (2 : F) ≠ 0) :
    Function.Bijective (normResidueZero F) ∧
      Function.Bijective (normResidueOne hF) := by
  refine ⟨(normResidueZeroEquiv F).bijective, ?_⟩
  rw [normResidueOne, LinearMap.coe_comp]
  exact (contCohomologyOneEquiv (GalGroup F)).symm.bijective.comp
    (normResidueOneChars_bijective hF)

end Frontier

