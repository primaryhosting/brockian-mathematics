/-
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Overview

Mathlib does not (yet) contain the theory of smooth projective complex varieties, their singular
cohomology, the Hodge decomposition, or cycle class maps.  We therefore develop, from scratch, the
linear-algebraic and axiomatic framework needed to *state* the Hodge conjecture, and we prove the
degree-`0` base case together with several Lean-checked reductions.

The framework consists of:

* `Frontier.Cx V`, the complexification `ℂ ⊗[ℚ] V` of a rational vector space, with its
  inclusion `Frontier.cxIncl` (proved injective) and its complex conjugation `Frontier.cxConj`;
* `Frontier.HodgeStr`, a pure rational Hodge structure: a finite-dimensional `ℚ`-vector space `V`
  of weight `w` together with a decomposition `V ⊗ ℂ = ⨁_{p+q=w} V^{p,q}` satisfying Hodge
  symmetry `conj (V^{p,q}) = V^{q,p}`;
* `Frontier.hodgeClasses H p`, the `ℚ`-subspace of rational classes of type `(p,p)`;
* `Frontier.HodgeTheory`, an axiomatization of the geometric input of the conjecture: a class of
  (smooth projective, connected) varieties, the Hodge structures on their rational cohomology, and
  the subspaces of classes of algebraic cycles;
* `Frontier.HodgeTheory.HodgeConjecture`, the statement of the Hodge conjecture for such data:
  every rational Hodge class of type `(p,p)` is a rational combination of classes of algebraic
  cycles.

The main theorem `Frontier.hodge_statement` proves the base case `p = 0` of the conjecture for
*every* Hodge theory: in cohomological degree `0` all Hodge classes are algebraic.
-/

namespace Frontier

/-! ## Complexification of a rational vector space -/

/-- The complexification `ℂ ⊗[ℚ] V` of a `ℚ`-vector space `V`. -/
abbrev Cx (V : Type) [AddCommGroup V] [Module ℚ V] : Type := ℂ ⊗[ℚ] V

/-- The canonical inclusion `V → V ⊗ ℂ`, `v ↦ 1 ⊗ v`. -/
noncomputable def cxIncl (V : Type) [AddCommGroup V] [Module ℚ V] : V →ₗ[ℚ] Cx V :=
  TensorProduct.mk ℚ ℂ V 1

@[simp] lemma cxIncl_apply {V : Type} [AddCommGroup V] [Module ℚ V] (v : V) :
    cxIncl V v = (1 : ℂ) ⊗ₜ[ℚ] v := rfl

/-- There is a `ℚ`-linear functional on `ℂ` sending `1` to `1`. -/
theorem exists_ratLinearFunctional : ∃ f : ℂ →ₗ[ℚ] ℚ, f 1 = 1 := by
  set e := (LinearEquiv.toSpanNonzeroSingleton ℚ ℂ (1 : ℂ) one_ne_zero) with he
  obtain ⟨g, hg⟩ := LinearMap.exists_extend e.symm.toLinearMap
  refine ⟨g, ?_⟩
  have h1 : (1 : ℂ) ∈ Submodule.span ℚ {(1 : ℂ)} := Submodule.mem_span_singleton_self _
  have hkey := congrArg (fun F : (Submodule.span ℚ {(1 : ℂ)}) →ₗ[ℚ] ℚ => F ⟨1, h1⟩) hg
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hkey
  have he1 : e 1 = ⟨1, h1⟩ := by ext; simp [he]
  rw [show ((⟨1, h1⟩ : Submodule.span ℚ {(1 : ℂ)})) = e 1 from he1.symm] at hkey
  simpa using hkey

/-- The complexification map `V → V ⊗ ℂ` is injective. -/
theorem cxIncl_injective (V : Type) [AddCommGroup V] [Module ℚ V] :
    Function.Injective (cxIncl V) := by
  obtain ⟨f, hf⟩ := exists_ratLinearFunctional
  have hli : Function.LeftInverse
      ((TensorProduct.lid ℚ V).toLinearMap ∘ₗ LinearMap.rTensor V f) (cxIncl V) := by
    intro v; simp [cxIncl, hf]
  exact hli.injective

/-- Complex conjugation on the complexification `ℂ ⊗[ℚ] V`, acting on the first factor. -/
noncomputable def cxConj (V : Type) [AddCommGroup V] [Module ℚ V] : Cx V →ₗ[ℚ] Cx V :=
  LinearMap.rTensor V (RingHom.toRatAlgHom (starRingEnd ℂ)).toLinearMap

@[simp] lemma cxConj_tmul {V : Type} [AddCommGroup V] [Module ℚ V] (z : ℂ) (v : V) :
    cxConj V (z ⊗ₜ[ℚ] v) = (starRingEnd ℂ) z ⊗ₜ[ℚ] v := rfl

/-! ## Rational Hodge structures -/

/-- A pure rational Hodge structure: a finite-dimensional `ℚ`-vector space `carrier` of weight `w`,
together with a decomposition of its complexification into subspaces `Hpq p q` (the "`(p,q)`
components"), which vanish unless `p + q = w`, which decompose the complexification as an internal
direct sum, and which satisfy Hodge symmetry: complex conjugation exchanges `Hpq p q` and
`Hpq q p`. -/
structure HodgeStr where
  /-- The weight of the Hodge structure. -/
  w : ℤ
  /-- The underlying rational vector space. -/
  carrier : Type
  [acg : AddCommGroup carrier]
  [mod : Module ℚ carrier]
  [fin : Module.Finite ℚ carrier]
  /-- The `(p,q)`-component of the complexification. -/
  Hpq : ℤ → ℤ → Submodule ℂ (Cx carrier)
  /-- The Hodge decomposition is concentrated in bidegrees of total degree `w`. -/
  weight : ∀ p q, p + q ≠ w → Hpq p q = ⊥
  /-- The `(p,q)`-components decompose the complexification. -/
  internal : DirectSum.IsInternal fun pq : ℤ × ℤ => Hpq pq.1 pq.2
  /-- Hodge symmetry. -/
  conj_symm : ∀ p q, ∀ x ∈ Hpq p q, cxConj carrier x ∈ Hpq q p

attribute [instance] HodgeStr.acg HodgeStr.mod HodgeStr.fin

/-- A Hodge structure is *effective* if its Hodge decomposition is concentrated in nonnegative
bidegrees.  Hodge structures of geometric origin, i.e. those on `Hᵏ(X, ℚ)` for `X` a smooth
projective variety, are effective. -/
def HodgeStr.Effective (H : HodgeStr) : Prop :=
  ∀ p q, p < 0 ∨ q < 0 → H.Hpq p q = ⊥

/-- The space of *Hodge classes of type `(p,p)`*: the rational classes whose image in the
complexification lies in the `(p,p)`-component of the Hodge decomposition. -/
noncomputable def hodgeClasses (H : HodgeStr) (p : ℤ) : Submodule ℚ H.carrier :=
  Submodule.comap (cxIncl H.carrier) ((H.Hpq p p).restrictScalars ℚ)

lemma mem_hodgeClasses_iff {H : HodgeStr} {p : ℤ} {v : H.carrier} :
    v ∈ hodgeClasses H p ↔ (1 : ℂ) ⊗ₜ[ℚ] v ∈ H.Hpq p p := Iff.rfl

/-- In an effective Hodge structure of weight `0`, the whole complexification is of type `(0,0)`. -/
theorem HodgeStr.Hpq_zero_eq_top (H : HodgeStr) (hw : H.w = 0) (he : H.Effective) :
    H.Hpq 0 0 = ⊤ := by
  have hsup : (⨆ pq : ℤ × ℤ, H.Hpq pq.1 pq.2) = ⊤ := H.internal.submodule_iSup_eq_top
  refine top_le_iff.mp ?_
  rw [← hsup]
  refine iSup_le ?_
  rintro ⟨p, q⟩
  by_cases hpq : p + q ≠ H.w
  · simp [H.weight p q hpq]
  · push_neg at hpq
    rw [hw] at hpq
    rcases lt_trichotomy p 0 with hp | hp | hp
    · simp [he p q (Or.inl hp)]
    · subst hp
      simp only [zero_add] at hpq
      subst hpq
      exact le_rfl
    · have hq : q < 0 := by omega
      simp [he p q (Or.inr hq)]

/-- In an effective Hodge structure of weight `0`, every rational class is a Hodge class. -/
theorem hodgeClasses_eq_top_of_weight_zero (H : HodgeStr) (hw : H.w = 0) (he : H.Effective) :
    hodgeClasses H 0 = ⊤ := by
  rw [hodgeClasses, H.Hpq_zero_eq_top hw he]
  simp

/-- If a Hodge structure has no `(p,p)`-classes at all, then it has no nonzero rational Hodge
classes of type `(p,p)`. -/
theorem hodgeClasses_eq_bot_of_Hpq_eq_bot (H : HodgeStr) (p : ℤ) (h : H.Hpq p p = ⊥) :
    hodgeClasses H p = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro v hv
  rw [mem_hodgeClasses_iff, h, Submodule.mem_bot] at hv
  have : cxIncl H.carrier v = cxIncl H.carrier 0 := by simpa using hv
  simpa using cxIncl_injective H.carrier this

/-! ## The Hodge conjecture -/

/-- An axiomatization of the geometric data entering the Hodge conjecture.

`Var` is a class of (smooth projective, connected) complex varieties.  For each `X : Var` and each
degree `k`, `H X k` is the weight-`k` Hodge structure on `Hᵏ(X, ℚ)`; it is effective.  For each
codimension `p`, `alg X p` is the `ℚ`-subspace of `H²ᵖ(X, ℚ)` spanned by the cycle classes of the
codimension-`p` algebraic subvarieties of `X`; by the standard properties of the cycle class map,
these are Hodge classes of type `(p,p)`.  Finally, `fund X` is the fundamental class of `X` in
`H⁰(X, ℚ)`: it is nonzero, algebraic (being the class of the codimension-`0` cycle `X` itself),
and, `X` being connected, `H⁰(X, ℚ)` is one-dimensional. -/
structure HodgeTheory where
  /-- The class of varieties under consideration. -/
  Var : Type
  /-- The Hodge structure on the degree-`k` rational cohomology of `X`. -/
  H : Var → ℕ → HodgeStr
  /-- The Hodge structure on `Hᵏ(X, ℚ)` is pure of weight `k`. -/
  weight_eq : ∀ X k, (H X k).w = k
  /-- Hodge structures of geometric origin are effective. -/
  effective : ∀ X k, (H X k).Effective
  /-- The subspace of `H²ᵖ(X, ℚ)` spanned by classes of codimension-`p` algebraic cycles. -/
  alg : (X : Var) → (p : ℕ) → Submodule ℚ (H X (2 * p)).carrier
  /-- Algebraic cycle classes are Hodge classes of type `(p,p)`. -/
  alg_le_hodgeClasses : ∀ X p, alg X p ≤ hodgeClasses (H X (2 * p)) p
  /-- The fundamental class of `X` in `H⁰(X, ℚ)`. -/
  fund : (X : Var) → (H X 0).carrier
  /-- The fundamental class is nonzero. -/
  fund_ne_zero : ∀ X, fund X ≠ 0
  /-- The fundamental class is algebraic: it is the class of the codimension-`0` cycle `X`. -/
  fund_mem_alg : ∀ X, fund X ∈ alg X 0
  /-- The varieties are connected, so their degree-`0` cohomology is one-dimensional. -/
  finrank_H0 : ∀ X, Module.finrank ℚ (H X 0).carrier = 1

/-- **The Hodge conjecture** for a given Hodge theory: for every variety `X` and every
codimension `p`, every rational Hodge class of type `(p,p)` in `H²ᵖ(X, ℚ)` is a rational linear
combination of classes of codimension-`p` algebraic cycles. -/
def HodgeTheory.HodgeConjecture (T : HodgeTheory) : Prop :=
  ∀ (X : T.Var) (p : ℕ), hodgeClasses (T.H X (2 * p)) p ≤ T.alg X p

/-- The Hodge conjecture, equivalently: the algebraic classes are exactly the Hodge classes. -/
theorem HodgeTheory.hodgeConjecture_iff (T : HodgeTheory) :
    T.HodgeConjecture ↔ ∀ (X : T.Var) (p : ℕ), T.alg X p = hodgeClasses (T.H X (2 * p)) p := by
  constructor
  · intro h X p
    exact le_antisymm (T.alg_le_hodgeClasses X p) (h X p)
  · intro h X p
    exact (h X p).ge

/-- **The base case of the Hodge conjecture.**  In cohomological degree `0`, i.e. for `p = 0`,
every Hodge class is algebraic, for every Hodge theory and every variety: the degree-`0`
cohomology is one-dimensional, spanned by the (algebraic) fundamental class, while — the Hodge
structure being effective of weight `0` — every degree-`0` class is a Hodge class. -/
theorem hodge_statement (T : HodgeTheory) (X : T.Var) :
    T.alg X 0 = hodgeClasses (T.H X (2 * 0)) 0 := by
  have hspan : Submodule.span ℚ {T.fund X} = ⊤ :=
    (finrank_eq_one_iff_of_nonzero (T.fund X) (T.fund_ne_zero X)).mp (T.finrank_H0 X)
  have halg : T.alg X 0 = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hspan, Submodule.span_le, Set.singleton_subset_iff]
    exact T.fund_mem_alg X
  have hhod : hodgeClasses (T.H X (2 * 0)) 0 = ⊤ :=
    hodgeClasses_eq_top_of_weight_zero _ (by simpa using T.weight_eq X 0)
      (T.effective X (2 * 0))
  rw [halg, hhod]

/-- The degree-`0` case of the Hodge conjecture, in the form in which the conjecture is stated:
every Hodge class in `H⁰(X, ℚ)` is algebraic. -/
theorem hodgeConjecture_degree_zero (T : HodgeTheory) (X : T.Var) :
    hodgeClasses (T.H X (2 * 0)) 0 ≤ T.alg X 0 :=
  (hodge_statement T X).ge

/-! ## Lean-checked reductions -/

/-- Base change of a `ℚ`-linear equivalence to the complexifications. -/
noncomputable def cxCongr {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W]
    [Module ℚ W] (e : V ≃ₗ[ℚ] W) : Cx V ≃ₗ[ℂ] Cx W :=
  LinearEquiv.ofLinear (LinearMap.baseChange ℂ e.toLinearMap)
    (LinearMap.baseChange ℂ e.symm.toLinearMap)
    (by rw [← LinearMap.baseChange_comp]; simp [LinearMap.baseChange_id])
    (by rw [← LinearMap.baseChange_comp]; simp [LinearMap.baseChange_id])

@[simp] lemma cxCongr_tmul {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W]
    [Module ℚ W] (e : V ≃ₗ[ℚ] W) (z : ℂ) (v : V) :
    cxCongr e (z ⊗ₜ[ℚ] v) = z ⊗ₜ[ℚ] e v := rfl

/-- **Reduction: invariance of Hodge classes under isomorphisms of Hodge structures.**
If `e` is an isomorphism of rational vector spaces whose complexification carries the
`(p,p)`-component of `H₁` onto that of `H₂`, then it carries the Hodge classes of `H₁` onto the
Hodge classes of `H₂`. -/
theorem hodgeClasses_map_of_iso {H₁ H₂ : HodgeStr} (e : H₁.carrier ≃ₗ[ℚ] H₂.carrier) (p : ℤ)
    (h : Submodule.map (cxCongr e).toLinearMap (H₁.Hpq p p) = H₂.Hpq p p) :
    Submodule.map e.toLinearMap (hodgeClasses H₁ p) = hodgeClasses H₂ p := by
  ext y
  simp only [Submodule.mem_map, mem_hodgeClasses_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← h]
    exact ⟨(1 : ℂ) ⊗ₜ[ℚ] x, hx, by simp⟩
  · intro hy
    rw [← h] at hy
    obtain ⟨z, hz, hze⟩ := hy
    refine ⟨e.symm y, ?_, by simp⟩
    have : z = (1 : ℂ) ⊗ₜ[ℚ] e.symm y := by
      apply (cxCongr e).injective
      simp only [cxCongr_tmul, LinearEquiv.apply_symm_apply]
      simpa using hze
    rwa [this] at hz

/-- **Reduction: the Hodge conjecture transfers along isomorphisms of Hodge structures.**
If all Hodge classes of type `(p,p)` on `H₁` are algebraic, and `e` is an isomorphism of Hodge
structures in bidegree `(p,p)` matching the algebraic parts, then all Hodge classes of type
`(p,p)` on `H₂` are algebraic. -/
theorem hodgeConjecture_transfer_of_iso {H₁ H₂ : HodgeStr} (e : H₁.carrier ≃ₗ[ℚ] H₂.carrier)
    (p : ℤ) (hHpq : Submodule.map (cxCongr e).toLinearMap (H₁.Hpq p p) = H₂.Hpq p p)
    (alg₁ : Submodule ℚ H₁.carrier) (alg₂ : Submodule ℚ H₂.carrier)
    (halg : Submodule.map e.toLinearMap alg₁ = alg₂)
    (h₁ : hodgeClasses H₁ p ≤ alg₁) :
    hodgeClasses H₂ p ≤ alg₂ := by
  rw [← halg, ← hodgeClasses_map_of_iso e p hHpq]
  exact Submodule.map_mono h₁

/-- **Reduction: the rank-one case.**  If every Hodge class of type `(p,p)` is a rational multiple
of a single algebraic class, the Hodge conjecture holds in that bidegree. -/
theorem hodgeConjecture_of_span_singleton {H : HodgeStr} {p : ℤ} {alg : Submodule ℚ H.carrier}
    {c : H.carrier} (hc : c ∈ alg) (hspan : hodgeClasses H p ≤ Submodule.span ℚ {c}) :
    hodgeClasses H p ≤ alg :=
  hspan.trans (by rwa [Submodule.span_le, Set.singleton_subset_iff])

/-- **Reduction: the case of no Hodge classes.**  If the `(p,p)`-component of the Hodge
decomposition vanishes, the Hodge conjecture holds in that bidegree. -/
theorem hodgeConjecture_of_Hpq_eq_bot {H : HodgeStr} {p : ℤ} {alg : Submodule ℚ H.carrier}
    (h : H.Hpq p p = ⊥) : hodgeClasses H p ≤ alg := by
  rw [hodgeClasses_eq_bot_of_Hpq_eq_bot H p h]
  exact bot_le

/-! ## Consistency: the axioms of a Hodge theory are satisfiable

To be sure that the statement above is not vacuous, we exhibit explicit Hodge structures, an
explicit Hodge theory, and check that the Hodge conjecture holds for it. -/

theorem iSupIndep_of_single {R M ι : Type} [Ring R] [AddCommGroup M] [Module R M]
    [DecidableEq ι] (A : ι → Submodule R M) (i₀ : ι) (h : ∀ i, i ≠ i₀ → A i = ⊥) :
    iSupIndep A := by
  rw [iSupIndep_def]
  intro i
  by_cases hi : i = i₀
  · subst hi
    have hbot : (⨆ j, ⨆ (_ : j ≠ i), A j) = ⊥ := by
      refine le_antisymm (iSup_le fun j => iSup_le fun hj => ?_) bot_le
      rw [h j hj]
    rw [hbot]
    exact disjoint_bot_right
  · rw [h i hi]
    exact disjoint_bot_left

instance cxSubsingleton (V : Type) [AddCommGroup V] [Module ℚ V] [Subsingleton V] :
    Subsingleton (Cx V) := by
  have h : ∀ z : Cx V, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul a v => rw [Subsingleton.elim v 0]; simp
    | add a b ha hb => rw [ha, hb]; simp
  exact ⟨fun x y => by rw [h x, h y]⟩

/-- If the underlying rational vector space is zero, all its classes are (trivially) Hodge
classes. -/
theorem hodgeClasses_eq_top_of_subsingleton (H : HodgeStr) [Subsingleton H.carrier] (p : ℤ) :
    hodgeClasses H p = ⊤ :=
  Subsingleton.elim _ _

/-- The zero Hodge structure, of any prescribed weight. -/
noncomputable def HodgeStr.zeroStr (w : ℤ) : HodgeStr where
  w := w
  carrier := Fin 0 → ℚ
  Hpq _ _ := ⊥
  weight _ _ _ := rfl
  internal := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    exact ⟨iSupIndep_of_single _ (0, 0) fun _ _ => rfl, Subsingleton.elim _ _⟩
  conj_symm _ _ x _ := (Submodule.mem_bot ℂ).2 (Subsingleton.elim _ _)

/-- The unit Hodge structure `ℚ(0)`: the one-dimensional Hodge structure of weight `0` and
type `(0,0)`.  It is the Hodge structure on `H⁰(X, ℚ)` of a connected variety. -/
noncomputable def HodgeStr.unit : HodgeStr where
  w := 0
  carrier := ℚ
  Hpq p q := if p = 0 ∧ q = 0 then ⊤ else ⊥
  weight p q h := if_neg (by rintro ⟨rfl, rfl⟩; simp at h)
  internal := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · refine iSupIndep_of_single _ ((0 : ℤ), (0 : ℤ)) fun i hi => ?_
      exact if_neg (fun hc => hi (Prod.ext hc.1 hc.2))
    · refine le_antisymm le_top (le_trans ?_ (le_iSup
        (fun pq : ℤ × ℤ => if pq.1 = 0 ∧ pq.2 = 0 then (⊤ : Submodule ℂ (Cx ℚ)) else ⊥)
        ((0 : ℤ), (0 : ℤ))))
      simp
  conj_symm p q x hx := by
    by_cases hpq : p = 0 ∧ q = 0
    · rw [if_pos ⟨hpq.2, hpq.1⟩]
      exact Submodule.mem_top
    · rw [if_neg hpq, Submodule.mem_bot] at hx
      subst hx
      rw [map_zero]
      exact Submodule.zero_mem _

theorem HodgeStr.unit_effective : HodgeStr.unit.Effective := by
  intro p q hpq
  refine if_neg ?_
  rintro ⟨rfl, rfl⟩
  simp at hpq

/-- The cohomology of the point-like variety of `Frontier.exampleHodgeTheory`. -/
noncomputable def exampleH (k : ℕ) : HodgeStr :=
  if k = 0 then HodgeStr.unit else HodgeStr.zeroStr k

/-- The algebraic classes of the point-like variety of `Frontier.exampleHodgeTheory`. -/
noncomputable def exampleAlg (p : ℕ) : Submodule ℚ (exampleH (2 * p)).carrier :=
  hodgeClasses (exampleH (2 * p)) p

/-- An explicit Hodge theory: a single point-like variety, with `H⁰ = ℚ(0)` and all higher
cohomology zero.  This shows that the axioms of `Frontier.HodgeTheory` are consistent. -/
noncomputable def exampleHodgeTheory : HodgeTheory where
  Var := Unit
  H _ k := exampleH k
  weight_eq _ k := by
    by_cases hk : k = 0
    · subst hk
      rw [exampleH, if_pos rfl]
      rfl
    · rw [exampleH, if_neg hk]
      rfl
  effective _ k := by
    by_cases hk : k = 0
    · subst hk
      rw [exampleH, if_pos rfl]
      exact HodgeStr.unit_effective
    · rw [exampleH, if_neg hk]
      intro p q _
      rfl
  alg _ p := exampleAlg p
  alg_le_hodgeClasses _ _ := le_of_eq rfl
  fund _ := (1 : ℚ)
  fund_ne_zero _ := by
    show (1 : ℚ) ≠ (0 : ℚ)
    norm_num
  fund_mem_alg _ := by
    show (1 : ℚ) ∈ hodgeClasses HodgeStr.unit 0
    rw [mem_hodgeClasses_iff]
    show (1 : ℂ) ⊗ₜ[ℚ] (1 : ℚ) ∈ (if (0 : ℤ) = 0 ∧ (0 : ℤ) = 0 then ⊤ else ⊥)
    rw [if_pos ⟨rfl, rfl⟩]
    exact Submodule.mem_top
  finrank_H0 _ := by
    show Module.finrank ℚ ℚ = 1
    simp

/-- The framework is not vacuous: there is a Hodge theory, and the Hodge conjecture holds for
it. -/
theorem exists_hodgeTheory_hodgeConjecture : ∃ T : HodgeTheory, T.HodgeConjecture :=
  ⟨exampleHodgeTheory, fun _ _ => le_rfl⟩

end Frontier

