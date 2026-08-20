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

namespace Frontier

/-!
## The set-up

Let `X` be a smooth complex projective variety and let `p : ℤ`.  The Hodge conjecture
concerns the rational cohomology group `V = H^{2p}(X, ℚ)`, which carries a rational
Hodge structure of weight `2p`: its complexification `ℂ ⊗[ℚ] V ≃ H^{2p}(X, ℂ)`
decomposes as an internal direct sum of the Hodge pieces `H^{i, 2p-i}`, and complex
conjugation on the complexification interchanges `H^{i, 2p-i}` and `H^{2p-i, i}`.

The group of *Hodge classes* is `Hdg^p(X) = V ∩ H^{p,p}`, the set of rational classes
whose image in the complexification lies in the middle piece.  The group of *algebraic
classes* is the ℚ-span of the cycle classes of the codimension-`p` algebraic subvarieties
of `X`; it is contained in `Hdg^p(X)`.

Since Mathlib contains neither the singular cohomology of a complex variety nor the cycle
class map, we axiomatise exactly this data: a `Frontier.HodgeDatum V p` records the
rational Hodge structure of weight `2p` on `V` together with the subspace of algebraic
classes and the (elementary) fact that algebraic classes are Hodge classes.  The Hodge
conjecture is then the statement `Frontier.HodgeConjecture`, namely that every Hodge class
is algebraic.
-/

section Complexification

variable (V : Type*) [AddCommGroup V] [Module ℚ V]

/-- Complex conjugation on the complexification `ℂ ⊗[ℚ] V` of a rational vector space `V`,
i.e. the map `z ⊗ v ↦ conj z ⊗ v`.  It is only `ℚ`-linear (it is conjugate-linear over `ℂ`). -/
noncomputable def complexConj : (ℂ ⊗[ℚ] V) →ₗ[ℚ] (ℂ ⊗[ℚ] V) :=
  TensorProduct.map (LinearMap.restrictScalars ℚ Complex.conjAe.toLinearMap) LinearMap.id

@[simp]
theorem complexConj_tmul (z : ℂ) (v : V) :
    complexConj V (z ⊗ₜ[ℚ] v) = (starRingEnd ℂ) z ⊗ₜ[ℚ] v := by
  simp [complexConj]

/-- The canonical `ℚ`-linear inclusion `V → ℂ ⊗[ℚ] V`, `v ↦ 1 ⊗ v`. -/
noncomputable def toComplexification : V →ₗ[ℚ] ℂ ⊗[ℚ] V := TensorProduct.mk ℚ ℂ V 1

@[simp]
theorem toComplexification_apply (v : V) : toComplexification V v = (1 : ℂ) ⊗ₜ[ℚ] v := rfl

/-- A rational vector space embeds into its complexification. -/
theorem toComplexification_injective : Function.Injective (toComplexification V) := by
  have hf : Function.Injective (Algebra.linearMap ℚ ℂ) := fun a b h => by simpa using h
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := V) (Algebra.linearMap ℚ ℂ) hf
  intro a b hab
  apply (TensorProduct.lid ℚ V).symm.injective
  apply h2
  simpa [TensorProduct.lid] using hab

end Complexification

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- A rational Hodge structure of weight `n` on the `ℚ`-vector space `V`: an internal direct
sum decomposition `ℂ ⊗[ℚ] V = ⨁ i, V^{i, n-i}` into complex subspaces, such that complex
conjugation carries `V^{i, n-i}` into `V^{n-i, i}`. -/
structure HodgeStr (V : Type*) [AddCommGroup V] [Module ℚ V] (n : ℤ) where
  /-- The Hodge piece `V^{i, n-i}` of the complexification. -/
  piece : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)
  /-- The pieces form an internal direct sum decomposition of `ℂ ⊗[ℚ] V`. -/
  internal : DirectSum.IsInternal piece
  /-- Complex conjugation maps `V^{i, n-i}` into `V^{n-i, i}`. -/
  conj_symm : ∀ (i : ℤ) (x : ℂ ⊗[ℚ] V), x ∈ piece i → complexConj V x ∈ piece (n - i)

/-- The Hodge classes of type `(p, p)`: the rational classes `v : V` whose image `1 ⊗ v` in the
complexification lies in the Hodge piece `V^{p,p}`. -/
noncomputable def HodgeStr.hodgeClasses {n : ℤ} (H : HodgeStr V n) (p : ℤ) : Submodule ℚ V :=
  ((H.piece p).restrictScalars ℚ).comap (toComplexification V)

theorem HodgeStr.mem_hodgeClasses_iff {n : ℤ} (H : HodgeStr V n) (p : ℤ) (v : V) :
    v ∈ H.hodgeClasses p ↔ (1 : ℂ) ⊗ₜ[ℚ] v ∈ H.piece p := Iff.rfl

/-- The data entering the Hodge conjecture in codimension `p`: the weight-`2p` rational Hodge
structure on `V = H^{2p}(X, ℚ)` together with the subspace `alg` of algebraic classes (the
`ℚ`-span of the classes of codimension-`p` subvarieties), which consists of Hodge classes. -/
structure HodgeDatum (V : Type*) [AddCommGroup V] [Module ℚ V] (p : ℤ) where
  /-- The weight-`2p` rational Hodge structure on `V`. -/
  hs : HodgeStr V (2 * p)
  /-- The subspace of algebraic classes. -/
  alg : Submodule ℚ V
  /-- Cycle classes are Hodge classes. -/
  alg_le : alg ≤ hs.hodgeClasses p

variable {p : ℤ}

/-- **The Hodge conjecture** for a given datum: every Hodge class of type `(p,p)` is a rational
linear combination of classes of algebraic cycles, i.e. the space of algebraic classes coincides
with the space of Hodge classes. -/
def HodgeConjecture (D : HodgeDatum V p) : Prop :=
  D.alg = D.hs.hodgeClasses p

/-!
## Elementary reductions and base cases
-/

/-- Since algebraic classes are always Hodge classes, the Hodge conjecture reduces to the single
inclusion "every Hodge class is algebraic". -/
theorem hodgeConjecture_iff (D : HodgeDatum V p) :
    HodgeConjecture D ↔ ∀ v : V, v ∈ D.hs.hodgeClasses p → v ∈ D.alg :=
  ⟨fun h _ hv => h ▸ hv, fun h => le_antisymm D.alg_le h⟩

/-- Base case: if there are no nonzero Hodge classes of type `(p,p)` then the Hodge conjecture
holds in codimension `p`. -/
theorem hodgeConjecture_of_piece_eq_bot (D : HodgeDatum V p) (h : D.hs.piece p = ⊥) :
    HodgeConjecture D := by
  have hbot : D.hs.hodgeClasses p = ⊥ := by
    refine le_antisymm (fun v hv => ?_) bot_le
    have hv' : (1 : ℂ) ⊗ₜ[ℚ] v ∈ D.hs.piece p := hv
    rw [h, Submodule.mem_bot] at hv'
    have hv0 : v = 0 := toComplexification_injective V (by simpa using hv')
    simp [hv0]
  have halg : D.alg = ⊥ := le_bot_iff.mp (le_trans D.alg_le hbot.le)
  show D.alg = D.hs.hodgeClasses p
  rw [hbot, halg]

/-- If a Hodge structure is concentrated in bidegree `(p, p)`, then every rational class is a
Hodge class. -/
theorem hodgeClasses_eq_top_of_concentrated {n : ℤ} (H : HodgeStr V n) (p : ℤ)
    (h : ∀ i, i ≠ p → H.piece i = ⊥) : H.hodgeClasses p = ⊤ := by
  have htop : H.piece p = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← H.internal.submodule_iSup_eq_top]
    exact iSup_le fun i => by
      by_cases hi : i = p
      · exact hi ▸ le_rfl
      · simp [h i hi]
  simp [HodgeStr.hodgeClasses, htop]

/-- Base case (degree `0`, or more generally a Hodge structure concentrated in bidegree `(p,p)`):
if the Hodge structure is concentrated in bidegree `(p, p)` and every rational class is algebraic
— for `p = 0` and `X` connected this is the statement that `H^0(X, ℚ)` is spanned by the
fundamental class `[X]`, which is algebraic — then the Hodge conjecture holds. -/
theorem hodgeConjecture_of_concentrated (D : HodgeDatum V p)
    (hconc : ∀ i, i ≠ p → D.hs.piece i = ⊥) (hfund : D.alg = ⊤) :
    HodgeConjecture D := by
  rw [HodgeConjecture, hfund, hodgeClasses_eq_top_of_concentrated D.hs p hconc]

/-!
## A nonvacuous instance: the Hodge datum of a point

To see that the axioms above are consistent (so that the statement is not vacuous), we exhibit,
for any `V` and any `p`, the Hodge datum concentrated in bidegree `(p, p)` with all classes
algebraic.  For `V = ℚ` and `p = 0` this is the Hodge datum of `H^0` of a point.
-/

/-- The Hodge structure on `V` concentrated in bidegree `(p, p)` (a sum of copies of the Tate
type `ℚ(-p)`). -/
noncomputable def HodgeStr.concentrated (V : Type*) [AddCommGroup V] [Module ℚ V] (p : ℤ) :
    HodgeStr V (2 * p) where
  piece i := if i = p then ⊤ else ⊥
  internal := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨?_, ?_⟩
    · intro i
      by_cases hi : i = p
      · have hsup : (⨆ j, ⨆ (_ : j ≠ i), (if j = p then (⊤ : Submodule ℂ (ℂ ⊗[ℚ] V)) else ⊥))
            = ⊥ := by
          refine le_antisymm (iSup_le fun j => iSup_le fun hj => ?_) bot_le
          have hjp : j ≠ p := by simpa [hi] using hj
          simp [hjp]
        rw [hsup]
        exact disjoint_bot_right
      · simp [hi]
    · exact le_antisymm le_top (le_iSup_of_le p (by simp))
  conj_symm i x hx := by
    by_cases hi : i = p
    · subst hi
      have h2 : 2 * i - i = i := by ring
      simp [h2]
    · simp only [hi, if_false, Submodule.mem_bot] at hx
      subst hx
      simp only [map_zero]
      split <;> simp

/-- The Hodge datum concentrated in bidegree `(p, p)` with all classes algebraic. -/
noncomputable def HodgeDatum.concentrated (V : Type*) [AddCommGroup V] [Module ℚ V] (p : ℤ) :
    HodgeDatum V p where
  hs := HodgeStr.concentrated V p
  alg := ⊤
  alg_le := by
    have h : (HodgeStr.concentrated V p).hodgeClasses p = ⊤ :=
      hodgeClasses_eq_top_of_concentrated _ p (fun i hi => by simp [HodgeStr.concentrated, hi])
    exact h.ge

/-- The Hodge conjecture holds for the concentrated datum; in particular the axioms of a
`HodgeDatum` are satisfiable. -/
theorem hodgeConjecture_concentrated (V : Type*) [AddCommGroup V] [Module ℚ V] (p : ℤ) :
    HodgeConjecture (HodgeDatum.concentrated V p) :=
  hodgeConjecture_of_concentrated _ (fun i hi => by simp [HodgeDatum.concentrated,
    HodgeStr.concentrated, hi]) rfl

/-!
## A Lean-checked reduction: direct sums

The Hodge conjecture for a direct sum of Hodge data is equivalent to the Hodge conjecture for
each summand.  (Geometrically: `H^{2p}(X ⊔ Y) = H^{2p}(X) ⊕ H^{2p}(Y)`.)
-/

section Aux

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {ι : Type*} [DecidableEq ι]

/-- An internal direct sum decomposition can be transported along a linear equivalence. -/
theorem isInternal_map_equiv (P : ι → Submodule R M) (e : M ≃ₗ[R] N)
    (h : DirectSum.IsInternal P) : DirectSum.IsInternal (fun i => (P i).map (e : M →ₗ[R] N)) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h ⊢
  obtain ⟨h1, h2⟩ := h
  constructor
  · have := (iSupIndep_map_orderIso_iff (Submodule.orderIsoMapComap e) (a := P)).mpr h1
    convert this using 1
  · rw [← Submodule.map_iSup, h2, Submodule.map_top, LinearEquiv.range]

/-- The product of two internal direct sum decompositions is an internal direct sum
decomposition of the product. -/
theorem isInternal_prod (A : ι → Submodule R M) (B : ι → Submodule R N)
    (hA : DirectSum.IsInternal A) (hB : DirectSum.IsInternal B) :
    DirectSum.IsInternal (fun i => (A i).prod (B i)) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hA hB ⊢
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  constructor
  · intro i
    rw [Submodule.disjoint_def]
    rintro ⟨x, y⟩ hxy hsup
    have hle : (⨆ j, ⨆ (_ : j ≠ i), (A j).prod (B j)) ≤
        (⨆ j, ⨆ (_ : j ≠ i), A j).prod (⨆ j, ⨆ (_ : j ≠ i), B j) :=
      iSup_le fun j => iSup_le fun hj => Submodule.prod_mono
        (le_iSup_of_le j (le_iSup_of_le hj le_rfl)) (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
    have hsup' := hle hsup
    rw [Submodule.mem_prod] at hsup' hxy
    have hx : x = 0 := (Submodule.disjoint_def.mp (hA1 i)) x hxy.1 hsup'.1
    have hy : y = 0 := (Submodule.disjoint_def.mp (hB1 i)) y hxy.2 hsup'.2
    simp [hx, hy]
  · refine le_antisymm le_top ?_
    rw [← LinearMap.sup_range_inl_inr (R := R) (M := M) (M₂ := N)]
    refine sup_le ?_ ?_
    · rw [← Submodule.map_top (LinearMap.inl R M N), ← hA2, Submodule.map_iSup]
      refine iSup_le fun j => le_iSup_of_le j ?_
      rintro z ⟨a, ha, rfl⟩
      exact ⟨ha, by simp⟩
    · rw [← Submodule.map_top (LinearMap.inr R M N), ← hB2, Submodule.map_iSup]
      refine iSup_le fun j => le_iSup_of_le j ?_
      rintro z ⟨b, hb, rfl⟩
      exact ⟨by simp, hb⟩

/-- Equality of products of submodules is equality of the factors. -/
theorem Submodule.prod_eq_prod_iff {a c : Submodule R M} {b d : Submodule R N} :
    a.prod b = c.prod d ↔ a = c ∧ b = d := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => by rw [h.1, h.2]⟩
  · ext x
    constructor
    · intro hx
      have : ((x, 0) : M × N) ∈ c.prod d := h ▸ ⟨hx, zero_mem _⟩
      exact this.1
    · intro hx
      have : ((x, 0) : M × N) ∈ a.prod b := h.symm ▸ ⟨hx, zero_mem _⟩
      exact this.1
  · ext y
    constructor
    · intro hy
      have : ((0, y) : M × N) ∈ c.prod d := h ▸ ⟨zero_mem _, hy⟩
      exact this.2
    · intro hy
      have : ((0, y) : M × N) ∈ a.prod b := h.symm ▸ ⟨zero_mem _, hy⟩
      exact this.2

end Aux

section Prod

variable {W : Type*} [AddCommGroup W] [Module ℚ W]

/-- The complexification of a direct sum is the direct sum of the complexifications. -/
noncomputable def prodComplexification (V W : Type*) [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] :
    ℂ ⊗[ℚ] (V × W) ≃ₗ[ℂ] (ℂ ⊗[ℚ] V) × (ℂ ⊗[ℚ] W) :=
  TensorProduct.prodRight ℚ ℂ ℂ V W

@[simp]
theorem prodComplexification_tmul (z : ℂ) (v : V) (w : W) :
    prodComplexification V W (z ⊗ₜ[ℚ] (v, w)) = (z ⊗ₜ[ℚ] v, z ⊗ₜ[ℚ] w) := by
  simp [prodComplexification]

/-- Complex conjugation on the complexification of a direct sum is computed componentwise. -/
theorem prodComplexification_conj (x : ℂ ⊗[ℚ] (V × W)) :
    prodComplexification V W (complexConj (V × W) x) =
      (complexConj V (prodComplexification V W x).1,
        complexConj W (prodComplexification V W x).2) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [Prod.ext_iff]
  | tmul z vw => obtain ⟨v, w⟩ := vw; simp
  | add x y hx hy => simp [hx, hy]

/-- The direct sum of two rational Hodge structures of weight `n`. -/
noncomputable def HodgeStr.prod {n : ℤ} (H₁ : HodgeStr V n) (H₂ : HodgeStr W n) :
    HodgeStr (V × W) n where
  piece i := ((H₁.piece i).prod (H₂.piece i)).map
    ((prodComplexification V W).symm : _ →ₗ[ℂ] _)
  internal :=
    isInternal_map_equiv _ (prodComplexification V W).symm
      (isInternal_prod _ _ H₁.internal H₂.internal)
  conj_symm i x hx := by
    rw [Submodule.mem_map_equiv] at hx ⊢
    simp only [LinearEquiv.symm_symm] at hx ⊢
    rw [Submodule.mem_prod] at hx ⊢
    rw [prodComplexification_conj]
    exact ⟨H₁.conj_symm i _ hx.1, H₂.conj_symm i _ hx.2⟩

@[simp]
theorem HodgeStr.hodgeClasses_prod {n : ℤ} (H₁ : HodgeStr V n) (H₂ : HodgeStr W n) (p : ℤ) :
    (H₁.prod H₂).hodgeClasses p = (H₁.hodgeClasses p).prod (H₂.hodgeClasses p) := by
  ext ⟨v, w⟩
  rw [Submodule.mem_prod, HodgeStr.mem_hodgeClasses_iff, HodgeStr.mem_hodgeClasses_iff,
    HodgeStr.mem_hodgeClasses_iff]
  show ((1 : ℂ) ⊗ₜ[ℚ] (v, w)) ∈ Submodule.map _ _ ↔ _
  rw [Submodule.mem_map_equiv]
  simp [Submodule.mem_prod]

/-- The direct sum of two Hodge data in codimension `p`. -/
noncomputable def HodgeDatum.prod (D₁ : HodgeDatum V p) (D₂ : HodgeDatum W p) :
    HodgeDatum (V × W) p where
  hs := D₁.hs.prod D₂.hs
  alg := D₁.alg.prod D₂.alg
  alg_le := by
    rw [HodgeStr.hodgeClasses_prod]
    exact Submodule.prod_mono D₁.alg_le D₂.alg_le

/-- **Reduction to the summands.**  The Hodge conjecture for a direct sum of Hodge data holds
if and only if it holds for each summand. -/
theorem hodgeConjecture_prod_iff (D₁ : HodgeDatum V p) (D₂ : HodgeDatum W p) :
    HodgeConjecture (D₁.prod D₂) ↔ HodgeConjecture D₁ ∧ HodgeConjecture D₂ := by
  show (D₁.alg.prod D₂.alg = (D₁.hs.prod D₂.hs).hodgeClasses p) ↔ _
  rw [HodgeStr.hodgeClasses_prod, Submodule.prod_eq_prod_iff]
  rfl

end Prod

/-!
## The statement
-/

/-- **Hodge statement.**

For a smooth complex projective variety `X` and `p : ℤ`, write `V = H^{2p}(X, ℚ)` with its
weight-`2p` rational Hodge structure, and let `alg ⊆ V` be the `ℚ`-span of the cycle classes of
the codimension-`p` algebraic subvarieties.  The **Hodge conjecture** asserts
`alg = Hdg^p := V ∩ H^{p,p}`, which is `Frontier.HodgeConjecture D` for the corresponding
`D : Frontier.HodgeDatum V p`.

This theorem records the formalised statement together with what is proved about it:

* the conjecture is equivalent to the single inclusion `Hdg^p ⊆ alg` (the reverse inclusion is
  part of the data, cycle classes being of type `(p,p)`);
* the base case in which there are no nonzero Hodge classes of type `(p,p)`;
* the base case of a Hodge structure concentrated in bidegree `(p,p)` all of whose classes are
  algebraic — for `p = 0` and `X` connected this is the classical degree-`0` case, where
  `H^0(X,ℚ) = ℚ·[X]` and the fundamental class `[X]` is algebraic;
* the reduction to summands: the conjecture for a direct sum of Hodge data is equivalent to the
  conjecture for each summand;
* nonvacuity: a datum satisfying all the axioms exists, and the conjecture holds for it. -/
theorem hodge_statement :
    (∀ {V : Type} [AddCommGroup V] [Module ℚ V] {p : ℤ} (D : HodgeDatum V p),
        HodgeConjecture D ↔ ∀ v : V, v ∈ D.hs.hodgeClasses p → v ∈ D.alg) ∧
      (∀ {V : Type} [AddCommGroup V] [Module ℚ V] {p : ℤ} (D : HodgeDatum V p),
        D.hs.piece p = ⊥ → HodgeConjecture D) ∧
      (∀ {V : Type} [AddCommGroup V] [Module ℚ V] {p : ℤ} (D : HodgeDatum V p),
        (∀ i, i ≠ p → D.hs.piece i = ⊥) → D.alg = ⊤ → HodgeConjecture D) ∧
      (∀ {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W] {p : ℤ}
          (D₁ : HodgeDatum V p) (D₂ : HodgeDatum W p),
        HodgeConjecture (D₁.prod D₂) ↔ HodgeConjecture D₁ ∧ HodgeConjecture D₂) ∧
      (∀ (V : Type) [AddCommGroup V] [Module ℚ V] (p : ℤ),
        HodgeConjecture (HodgeDatum.concentrated V p)) :=
  ⟨fun D => hodgeConjecture_iff D, fun D h => hodgeConjecture_of_piece_eq_bot D h,
    fun D h1 h2 => hodgeConjecture_of_concentrated D h1 h2,
    fun D₁ D₂ => hodgeConjecture_prod_iff D₁ D₂,
    fun V _ _ p => hodgeConjecture_concentrated V p⟩

end Frontier

