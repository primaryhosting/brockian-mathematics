import Mathlib
import RequestProject.Hodge

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
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open TensorProduct

namespace Frontier

/-! ## Rational Hodge structures -/

/-- A **rational Hodge structure of weight `w`** on a finite–dimensional `ℚ`-vector space `V`:
a decomposition of the complexification `ℂ ⊗[ℚ] V` into complex subspaces
`piece q = V^{q, w - q}`, together with the complex conjugation of `ℂ ⊗[ℚ] V`
(semilinear over `ℂ`, the identity on the rational points `1 ⊗ v`), subject to the
symmetry `conj (V^{q, w - q}) ⊆ V^{w - q, q}`.

This is the standard linear–algebra package carried by the singular cohomology
`H^w(X, ℚ)` of a smooth projective complex variety `X`. -/
structure HodgeStructure (w : ℤ) (V : Type*) [AddCommGroup V] [Module ℚ V] where
  /-- The Hodge piece `V^{q, w - q}` of the complexification. -/
  piece : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)
  /-- The Hodge decomposition `ℂ ⊗ V = ⨁_q V^{q, w - q}`. -/
  decomposition : DirectSum.IsInternal piece
  /-- Complex conjugation on the complexification. -/
  conj : (ℂ ⊗[ℚ] V) →ₗ[ℚ] (ℂ ⊗[ℚ] V)
  /-- Conjugation acts on the first tensor factor. -/
  conj_tmul : ∀ (c : ℂ) (v : V), conj (c ⊗ₜ[ℚ] v) = (starRingEnd ℂ c) ⊗ₜ[ℚ] v
  /-- The Hodge symmetry `conj (V^{q, w - q}) ⊆ V^{w - q, q}`. -/
  conj_piece : ∀ q, Submodule.map conj ((piece q).restrictScalars ℚ)
      ≤ (piece (w - q)).restrictScalars ℚ

namespace HodgeStructure

variable {w : ℤ} {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The rational classes of type `(q, w - q)`: those `v ∈ V` whose image `1 ⊗ v` in the
complexification lies in the Hodge piece `V^{q, w - q}`.  For `w = 2 p` and `q = p` these are
the **Hodge classes** of the Hodge structure. -/
def hodgeClasses (hs : HodgeStructure w V) (q : ℤ) : Submodule ℚ V :=
  ((hs.piece q).restrictScalars ℚ).comap (TensorProduct.mk ℚ ℂ V 1)

@[simp]
theorem mem_hodgeClasses {hs : HodgeStructure w V} {q : ℤ} {v : V} :
    v ∈ hs.hodgeClasses q ↔ (1 : ℂ) ⊗ₜ[ℚ] v ∈ hs.piece q := Iff.rfl

/-- Conjugation fixes the rational points `1 ⊗ v` of the complexification. -/
theorem conj_one_tmul (hs : HodgeStructure w V) (v : V) :
    hs.conj ((1 : ℂ) ⊗ₜ[ℚ] v) = (1 : ℂ) ⊗ₜ[ℚ] v := by
  rw [hs.conj_tmul]
  simp

/-- **Rational classes have type `(q, q)`.**  If `2 q ≠ w` then there is no nonzero rational
class of type `(q, w - q)`: Hodge symmetry forces `1 ⊗ v` to lie in two distinct summands of
the Hodge decomposition.  In particular a Hodge structure of odd weight has no nonzero
"Hodge classes". -/
theorem eq_zero_of_two_mul_ne (hs : HodgeStructure w V) {q : ℤ} (hq : 2 * q ≠ w) {v : V}
    (hv : v ∈ hs.hodgeClasses q) : v = 0 := by
  have hmem : (1 : ℂ) ⊗ₜ[ℚ] v ∈ hs.piece q := hv
  have hmem' : (1 : ℂ) ⊗ₜ[ℚ] v ∈ hs.piece (w - q) := by
    have : hs.conj ((1 : ℂ) ⊗ₜ[ℚ] v) ∈ (hs.piece (w - q)).restrictScalars ℚ :=
      hs.conj_piece q ⟨(1 : ℂ) ⊗ₜ[ℚ] v, hmem, rfl⟩
    rwa [hs.conj_one_tmul] at this
  have hne : q ≠ w - q := by omega
  have hdisj : Disjoint (hs.piece q) (hs.piece (w - q)) :=
    hs.decomposition.submodule_iSupIndep.pairwiseDisjoint hne
  have hzero : (1 : ℂ) ⊗ₜ[ℚ] v = 0 :=
    (Submodule.disjoint_def.mp hdisj) _ hmem hmem'
  have hmk : (TensorProduct.mk ℚ ℂ V 1) v = (TensorProduct.mk ℚ ℂ V 1) 0 := by
    simpa using hzero
  exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := ℚ) (B := ℂ) V hmk

end HodgeStructure

/-! ## Hodge data and the Hodge conjecture -/

/-- The linear–algebra data attached to a smooth projective complex variety `X` and an integer
`p ≥ 0`: the finite–dimensional rational cohomology group `H^{2p}(X, ℚ)` with its Hodge
structure of weight `2 p`, together with the subspace `algebraic` spanned by the cycle classes
of the algebraic subvarieties of `X` of codimension `p`.  That these cycle classes are Hodge
classes is part of the data (`algebraic_le_hodgeClasses`); it is the standard fact that the
cycle class of a codimension-`p` subvariety is a rational class of type `(p, p)`. -/
structure HodgeDatum (p : ℤ) where
  /-- The rational cohomology group `H^{2p}(X, ℚ)`. -/
  coh : Type
  [addCommGroup : AddCommGroup coh]
  [module : Module ℚ coh]
  [finite : Module.Finite ℚ coh]
  /-- Its Hodge structure of weight `2 p`. -/
  hodge : HodgeStructure (2 * p) coh
  /-- The `ℚ`-span of the classes of algebraic cycles of codimension `p`. -/
  algebraic : Submodule ℚ coh
  /-- Algebraic cycle classes are Hodge classes. -/
  algebraic_le_hodgeClasses : algebraic ≤ hodge.hodgeClasses p

attribute [instance] HodgeDatum.addCommGroup HodgeDatum.module HodgeDatum.finite

/-- **The Hodge conjecture** for the datum `D` coming from a smooth projective complex variety
`X` in codimension `p`: every Hodge class in `H^{2p}(X, ℚ)`, i.e. every rational cohomology
class of type `(p, p)`, is a `ℚ`-linear combination of classes of algebraic cycles of
codimension `p`. -/
def HodgeConjectureFor {p : ℤ} (D : HodgeDatum p) : Prop :=
  D.hodge.hodgeClasses p ≤ D.algebraic

/-- The Hodge conjecture for `D` says exactly that the space of Hodge classes coincides with
the space of algebraic classes (one inclusion always holds). -/
theorem hodgeConjectureFor_iff {p : ℤ} (D : HodgeDatum p) :
    HodgeConjectureFor D ↔ D.hodge.hodgeClasses p = D.algebraic :=
  ⟨fun h => le_antisymm h D.algebraic_le_hodgeClasses, fun h => h.le⟩

/-- **Reduction to a spanning family.**  To prove the Hodge conjecture for `D` it suffices to
exhibit a family of algebraic classes spanning the space of Hodge classes. -/
theorem hodgeConjectureFor_of_span {p : ℤ} (D : HodgeDatum p) {S : Set D.coh}
    (hS : S ⊆ (D.algebraic : Set D.coh))
    (hspan : D.hodge.hodgeClasses p ≤ Submodule.span ℚ S) :
    HodgeConjectureFor D :=
  hspan.trans (Submodule.span_le.mpr hS)

/-- **The Hodge conjecture in codimension `0`.**  If `X` is connected, then
`H^0(X, ℚ) = ℚ · [X]` is spanned by the fundamental class, which is the class of the
codimension-`0` cycle `X` itself; hence every Hodge class in `H^0(X, ℚ)` is algebraic. -/
theorem hodgeConjectureFor_codim_zero (D : HodgeDatum 0) (fc : D.coh)
    (hconn : ∀ v : D.coh, ∃ c : ℚ, v = c • fc) (hfc : fc ∈ D.algebraic) :
    HodgeConjectureFor D := by
  intro v _
  obtain ⟨c, rfl⟩ := hconn v
  exact D.algebraic.smul_mem c hfc

/-- **Vanishing base case.**  If the Hodge structure carries no nonzero rational class of type
`(p, p)` then the Hodge conjecture holds for `D`. -/
theorem hodgeConjectureFor_of_hodgeClasses_eq_bot {p : ℤ} (D : HodgeDatum p)
    (h : D.hodge.hodgeClasses p = ⊥) : HodgeConjectureFor D := by
  rw [HodgeConjectureFor, h]
  exact bot_le

/-- **Reduction along a correspondence.**  Let `f` be a morphism of rational cohomology which
carries algebraic classes to algebraic classes and whose image contains every Hodge class of
the target (as the image of a Hodge class of the source).  Then the Hodge conjecture for the
source implies the Hodge conjecture for the target.  This is the shape of all the standard
reductions of the Hodge conjecture along algebraic correspondences. -/
theorem hodgeConjectureFor_of_map {p : ℤ} (D E : HodgeDatum p) (f : D.coh →ₗ[ℚ] E.coh)
    (hsurj : ∀ v ∈ E.hodge.hodgeClasses p, ∃ u ∈ D.hodge.hodgeClasses p, f u = v)
    (halg : ∀ u ∈ D.algebraic, f u ∈ E.algebraic)
    (hD : HodgeConjectureFor D) : HodgeConjectureFor E := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := hsurj v hv
  exact halg u (hD hu)

/-! ## Consistency: the axioms are satisfiable -/

/-- Complex conjugation of `ℂ`, as a `ℚ`-linear map. -/
noncomputable def conjQ : ℂ →ₗ[ℚ] ℂ where
  toFun z := (starRingEnd ℂ) z
  map_add' := by intro x y; simp
  map_smul' := by intro c x; simp [Rat.smul_def]

/-- Complex conjugation of the complexification `ℂ ⊗[ℚ] V`. -/
noncomputable def conjCx (V : Type*) [AddCommGroup V] [Module ℚ V] :
    (ℂ ⊗[ℚ] V) →ₗ[ℚ] (ℂ ⊗[ℚ] V) :=
  TensorProduct.map conjQ LinearMap.id

@[simp]
theorem conjCx_tmul {V : Type*} [AddCommGroup V] [Module ℚ V] (c : ℂ) (v : V) :
    conjCx V (c ⊗ₜ[ℚ] v) = (starRingEnd ℂ) c ⊗ₜ[ℚ] v := rfl

/-- The Hodge structure of weight `0` and type `(0,0)` on a rational vector space:
the whole complexification sits in the piece `V^{0,0}`.  It is the Hodge structure of
`H^0(X, ℚ)`. -/
noncomputable def trivialHodgeStructure (V : Type*) [AddCommGroup V] [Module ℚ V] :
    HodgeStructure 0 V where
  piece q := if q = 0 then ⊤ else ⊥
  decomposition := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · intro i
      by_cases hi : i = 0
      · subst hi
        have hbot : (⨆ j, ⨆ (_ : j ≠ (0 : ℤ)), (if j = 0 then (⊤ : Submodule ℂ (ℂ ⊗[ℚ] V)) else ⊥))
            = ⊥ := by
          refine iSup_eq_bot.2 fun j => iSup_eq_bot.2 fun hj => ?_
          simp [hj]
        rw [hbot]
        exact disjoint_bot_right
      · simp [hi]
    · exact le_antisymm le_top (le_iSup_of_le 0 (by simp))
  conj := conjCx V
  conj_tmul := fun c v => rfl
  conj_piece := by
    intro q
    by_cases hq : q = 0 <;> simp [hq]

@[simp]
theorem trivialHodgeStructure_hodgeClasses (V : Type*) [AddCommGroup V] [Module ℚ V] :
    (trivialHodgeStructure V).hodgeClasses 0 = ⊤ := by
  ext v
  simp [HodgeStructure.hodgeClasses, trivialHodgeStructure]

/-- The Hodge datum of a point: `H^0 = ℚ`, all of it algebraic (spanned by the fundamental
class).  This witnesses that the axioms of `Frontier.HodgeDatum` are consistent, so the
results below are not vacuous. -/
noncomputable def pointDatum : HodgeDatum 0 where
  coh := ℚ
  hodge := trivialHodgeStructure ℚ
  algebraic := ⊤
  algebraic_le_hodgeClasses := by simp

/-- The Hodge conjecture holds for the Hodge datum of a point. -/
theorem hodgeConjectureFor_pointDatum : HodgeConjectureFor pointDatum :=
  fun _ _ => Submodule.mem_top

/-- **Hodge statement.**

Part (1) is the formalized statement of the Hodge conjecture for a Hodge datum `D`
(the data attached to a smooth projective complex variety in codimension `p`): it is
equivalent to the equality of the space of Hodge classes with the space of algebraic classes.

Part (2) is the base case of the conjecture in codimension `0`: for a connected variety
`H^0(X, ℚ)` is spanned by the fundamental class `[X]`, which is algebraic, so every Hodge
class is algebraic.

Part (3) is a Lean-checked reduction: the conjecture follows as soon as the Hodge classes are
spanned by algebraic classes.

Part (4) records that only the middle type `(q, q)` can support nonzero rational classes,
so that Hodge classes are indeed the only classes the conjecture has to account for.

Part (5) is the reduction along a correspondence: a map of cohomology preserving algebraic
classes and hitting all Hodge classes of the target transports the conjecture. -/
theorem hodge_statement :
    (∀ (p : ℤ) (D : HodgeDatum p),
        HodgeConjectureFor D ↔ D.hodge.hodgeClasses p = D.algebraic) ∧
    (∀ (D : HodgeDatum 0) (fc : D.coh), (∀ v : D.coh, ∃ c : ℚ, v = c • fc) →
        fc ∈ D.algebraic → HodgeConjectureFor D) ∧
    (∀ (p : ℤ) (D : HodgeDatum p) (S : Set D.coh), S ⊆ (D.algebraic : Set D.coh) →
        D.hodge.hodgeClasses p ≤ Submodule.span ℚ S → HodgeConjectureFor D) ∧
    (∀ (w q : ℤ) (V : Type) [AddCommGroup V] [Module ℚ V]
        (hs : HodgeStructure w V), 2 * q ≠ w → hs.hodgeClasses q = ⊥) ∧
    (∀ (p : ℤ) (D E : HodgeDatum p) (f : D.coh →ₗ[ℚ] E.coh),
        (∀ v ∈ E.hodge.hodgeClasses p, ∃ u ∈ D.hodge.hodgeClasses p, f u = v) →
        (∀ u ∈ D.algebraic, f u ∈ E.algebraic) →
        HodgeConjectureFor D → HodgeConjectureFor E) := by
  refine ⟨fun _ D => hodgeConjectureFor_iff D, hodgeConjectureFor_codim_zero,
    fun p D S hS hspan => hodgeConjectureFor_of_span D hS hspan, ?_,
    fun p D E f => hodgeConjectureFor_of_map D E f⟩
  intro w q V _ _ hs hq
  exact (Submodule.eq_bot_iff _).2 fun v hv => hs.eq_zero_of_two_mul_ne hq hv

end Frontier

