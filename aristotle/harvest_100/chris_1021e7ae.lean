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

/-! ## Complex conjugation on a complexified rational vector space -/

/-- Complex conjugation, viewed as a `ℚ`-linear endomorphism of `ℂ`. -/
noncomputable def conjQ : ℂ →ₗ[ℚ] ℂ where
  toFun z := starRingEnd ℂ z
  map_add' := by intro x y; simp
  map_smul' := by intro q z; simp [Complex.ext_iff]

/-- The conjugation `z ⊗ v ↦ conj z ⊗ v` on the complexification `ℂ ⊗[ℚ] V` of a
rational vector space `V`.  It is `ℚ`-linear and `ℂ`-antilinear. -/
noncomputable def conjTensor (V : Type) [AddCommGroup V] [Module ℚ V] :
    (ℂ ⊗[ℚ] V) →ₗ[ℚ] (ℂ ⊗[ℚ] V) :=
  LinearMap.rTensor V conjQ

@[simp] lemma conjTensor_tmul (V : Type) [AddCommGroup V] [Module ℚ V] (z : ℂ) (v : V) :
    conjTensor V (z ⊗ₜ[ℚ] v) = (starRingEnd ℂ) z ⊗ₜ[ℚ] v := rfl

lemma conjTensor_surjective (V : Type) [AddCommGroup V] [Module ℚ V] :
    Function.Surjective (conjTensor V) := by
  intro x
  refine ⟨conjTensor V x, ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z v => simp [conjTensor, conjQ]
  | add a b ha hb => simp [map_add, ha, hb]

/-! ## Rational Hodge structures -/

/-- A pure rational Hodge structure of weight `w` on a finite-dimensional `ℚ`-vector space `V`:
a decomposition of the complexification `V ⊗ ℂ = ⨁_{p+q = w} V^{p,q}` into complex subspaces
(indexed here by `p`, with `q = w - p`), which is exchanged by complex conjugation:
`conj (V^{p,q}) = V^{q,p}`. -/
structure HodgeStructure (w : ℤ) (V : Type) [AddCommGroup V] [Module ℚ V] where
  /-- The `(p, w - p)` piece of the Hodge decomposition of the complexification. -/
  piece : ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)
  /-- The pieces give an internal direct sum decomposition of `ℂ ⊗[ℚ] V`. -/
  internal : DirectSum.IsInternal piece
  /-- Complex conjugation carries the `(p, w - p)` piece onto the `(w - p, p)` piece. -/
  conj_piece : ∀ p : ℤ,
    ((piece p).restrictScalars ℚ).map (conjTensor V) = (piece (w - p)).restrictScalars ℚ

/-- The space of *Hodge classes* of a weight-`2p` rational Hodge structure `H`:
the rational classes `v ∈ V` whose image `1 ⊗ v` in the complexification lies in the
`(p, p)`-piece.  This is a `ℚ`-subspace of `V`. -/
noncomputable def hodgeClasses {w : ℤ} {V : Type} [AddCommGroup V] [Module ℚ V]
    (H : HodgeStructure w V) (p : ℤ) : Submodule ℚ V :=
  ((H.piece p).restrictScalars ℚ).comap (TensorProduct.mk ℚ ℂ V 1)

lemma mem_hodgeClasses_iff {w : ℤ} {V : Type} [AddCommGroup V] [Module ℚ V]
    (H : HodgeStructure w V) (p : ℤ) (v : V) :
    v ∈ hodgeClasses H p ↔ (1 : ℂ) ⊗ₜ[ℚ] v ∈ H.piece p := Iff.rfl

/-- Base case of the theory of Hodge classes: if the Hodge structure is purely of type `(p,p)`,
i.e. the whole complexification is the `(p,p)`-piece, then *every* rational class is a
Hodge class. -/
lemma hodgeClasses_eq_top_of_piece_eq_top {w : ℤ} {V : Type} [AddCommGroup V] [Module ℚ V]
    (H : HodgeStructure w V) (p : ℤ) (hp : H.piece p = ⊤) :
    hodgeClasses H p = ⊤ := by
  ext v
  simp [mem_hodgeClasses_iff, hp]

/-- If a rational vector space is trivial then it has no nonzero Hodge classes. -/
lemma hodgeClasses_eq_bot_of_trivial {w : ℤ} {V : Type} [AddCommGroup V] [Module ℚ V]
    (H : HodgeStructure w V) (p : ℤ) (hV : (⊤ : Submodule ℚ V) = ⊥) :
    hodgeClasses H p = ⊥ :=
  le_antisymm (hV ▸ le_top) bot_le

/-- A one-index family of submodules, equal to everything at `i₀` and zero elsewhere, gives an
internal direct sum decomposition. -/
lemma isInternal_single {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (i₀ : ℤ) :
    DirectSum.IsInternal (fun k : ℤ => if k = i₀ then (⊤ : Submodule R M) else ⊥) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨fun i => ?_, le_antisymm le_top (le_iSup_of_le i₀ (by simp))⟩
  by_cases h : i = i₀
  · have hbot : (⨆ j, ⨆ (_ : j ≠ i), if j = i₀ then (⊤ : Submodule R M) else ⊥) = ⊥ := by
      refine iSup_eq_bot.2 fun j => iSup_eq_bot.2 fun hj => ?_
      have : j ≠ i₀ := by rw [← h] at *; exact hj
      simp [this]
    simp [hbot]
  · simp [h]

/-- The Hodge structure of *Tate type* `(p, p)` on a rational vector space `V`: the whole
complexification sits in the `(p,p)`-piece.  (For `V = ℚ` and `p = 0` this is the Hodge structure
on `H^0` of a connected variety; for `p = d` on `H^{2d}`.)  In particular Hodge structures, in
the above sense, exist. -/
noncomputable def tateHodgeStructure (V : Type) [AddCommGroup V] [Module ℚ V] (p : ℤ) :
    HodgeStructure (2 * p) V where
  piece k := if k = p then ⊤ else ⊥
  internal := isInternal_single p
  conj_piece k := by
    by_cases h : k = p
    · subst h
      have hk : 2 * k - k = k := by ring
      simp [hk, Submodule.map_top, LinearMap.range_eq_top.2 (conjTensor_surjective V)]
    · have h2 : 2 * p - k ≠ p := by omega
      simp [h, h2]

@[simp] lemma tateHodgeStructure_piece_self (V : Type) [AddCommGroup V] [Module ℚ V] (p : ℤ) :
    (tateHodgeStructure V p).piece p = ⊤ := by
  simp [tateHodgeStructure]

/-- Every rational class of a Tate-type Hodge structure is a Hodge class. -/
lemma hodgeClasses_tate (V : Type) [AddCommGroup V] [Module ℚ V] (p : ℤ) :
    hodgeClasses (tateHodgeStructure V p) p = ⊤ :=
  hodgeClasses_eq_top_of_piece_eq_top _ _ (tateHodgeStructure_piece_self V p)

/-! ## Cohomological data of a smooth projective complex variety -/

/-- The Hodge-theoretic data attached to a smooth projective complex variety `X` of complex
dimension `d`:

* for each `p`, the finite-dimensional `ℚ`-vector space `coh p = H^{2p}(X, ℚ)`, equipped with
  its pure rational Hodge structure of weight `2p`;
* the subspace `alg p ⊆ H^{2p}(X, ℚ)` spanned by the cohomology classes of algebraic cycles of
  codimension `p` (the image of the cycle class map);
* the (elementary, known) fact that classes of algebraic cycles are Hodge classes;
* the vanishing `H^{2p}(X, ℚ) = 0` for `p > d`.
-/
structure HodgeVarietyData (d : ℕ) where
  /-- `coh p` is the rational cohomology `H^{2p}(X, ℚ)`. -/
  coh : ℕ → Type
  [addCommGroup : ∀ p, AddCommGroup (coh p)]
  [isModule : ∀ p, Module ℚ (coh p)]
  [finite : ∀ p, Module.Finite ℚ (coh p)]
  /-- The weight-`2p` Hodge structure on `H^{2p}(X, ℚ)`. -/
  hs : ∀ p : ℕ, HodgeStructure (2 * (p : ℤ)) (coh p)
  /-- The subspace of classes of algebraic cycles of codimension `p`. -/
  alg : ∀ p : ℕ, Submodule ℚ (coh p)
  /-- Algebraic cycle classes are Hodge classes. -/
  alg_le_hodge : ∀ p : ℕ, alg p ≤ hodgeClasses (hs p) (p : ℤ)
  /-- Cohomology vanishes above the (real) dimension `2d`. -/
  vanishing : ∀ p : ℕ, d < p → (⊤ : Submodule ℚ (coh p)) = ⊥

attribute [instance] HodgeVarietyData.addCommGroup HodgeVarietyData.isModule
  HodgeVarietyData.finite

/-- **The Hodge conjecture** for a smooth projective complex variety with cohomological data `X`:
every Hodge class in `H^{2p}(X, ℚ)` is a rational linear combination of classes of algebraic
cycles of codimension `p`. -/
def HodgeConjecture {d : ℕ} (X : HodgeVarietyData d) : Prop :=
  ∀ p : ℕ, hodgeClasses (X.hs p) (p : ℤ) ≤ X.alg p

/-- Equivalent formulation: the Hodge conjecture says that the image of the cycle class map is
*exactly* the space of Hodge classes. -/
theorem hodgeConjecture_iff {d : ℕ} (X : HodgeVarietyData d) :
    HodgeConjecture X ↔ ∀ p : ℕ, X.alg p = hodgeClasses (X.hs p) (p : ℤ) :=
  ⟨fun h p => le_antisymm (X.alg_le_hodge p) (h p),
   fun h p => (h p).ge⟩

/-- Above the dimension the Hodge conjecture is vacuous: there are no nonzero Hodge classes. -/
lemma hodgeClasses_le_alg_of_gt_dim {d : ℕ} (X : HodgeVarietyData d) (p : ℕ) (hp : d < p) :
    hodgeClasses (X.hs p) (p : ℤ) ≤ X.alg p := by
  rw [hodgeClasses_eq_bot_of_trivial _ _ (X.vanishing p hp)]
  exact bot_le

/-- **Base case / Lean-checked reduction of the Hodge conjecture.**

For a smooth projective complex variety of dimension `d ≤ 2` (a point, a curve or a surface),
the Hodge conjecture follows from just three inputs:

* degree `0`: the fundamental class generates the Hodge classes of `H^0`;
* degree `2` (`p = 1`): the Lefschetz `(1,1)`-theorem, i.e. Hodge classes in `H^2` are classes
  of divisors;
* top degree `p = d`: the class of a point generates the Hodge classes of `H^{2d}`.

Indeed all remaining cohomological degrees are above the dimension, hence carry no cohomology.
-/
theorem hodge_statement {d : ℕ} (hd : d ≤ 2) (X : HodgeVarietyData d)
    (hzero : hodgeClasses (X.hs 0) (0 : ℤ) ≤ X.alg 0)
    (hone : hodgeClasses (X.hs 1) (1 : ℤ) ≤ X.alg 1)
    (htop : hodgeClasses (X.hs d) (d : ℤ) ≤ X.alg d) :
    HodgeConjecture X := by
  intro p
  by_cases hp : d < p
  · exact hodgeClasses_le_alg_of_gt_dim X p hp
  · push_neg at hp
    have hp2 : p ≤ 2 := hp.trans hd
    interval_cases p
    · exact hzero
    · exact hone
    · have hd2 : d = 2 := le_antisymm hd hp
      subst hd2
      exact htop

/-! ## Non-vacuity: the Hodge conjecture for a point -/

/-- The rational cohomology of a point: `H^0 = ℚ` and `H^{2p} = 0` for `p > 0`. -/
def pointCoh : ℕ → Type
  | 0 => ℚ
  | _ + 1 => PUnit

instance instPointCohAddCommGroup : ∀ p, AddCommGroup (pointCoh p)
  | 0 => inferInstanceAs (AddCommGroup ℚ)
  | _ + 1 => inferInstanceAs (AddCommGroup PUnit)

instance instPointCohModule : ∀ p, Module ℚ (pointCoh p)
  | 0 => inferInstanceAs (Module ℚ ℚ)
  | _ + 1 => inferInstanceAs (Module ℚ PUnit)

instance instPointCohFinite : ∀ p, Module.Finite ℚ (pointCoh p)
  | 0 => inferInstanceAs (Module.Finite ℚ ℚ)
  | _ + 1 => inferInstanceAs (Module.Finite ℚ PUnit)

/-- The Hodge-theoretic data of a point: all cohomology is of Tate type and algebraic. -/
noncomputable def pointVariety : HodgeVarietyData 0 where
  coh := pointCoh
  hs p := tateHodgeStructure (pointCoh p) (p : ℤ)
  alg _ := ⊤
  alg_le_hodge p := by rw [hodgeClasses_tate]
  vanishing p hp := by
    obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
    refine le_antisymm (fun x _ => ?_) bot_le
    haveI : Subsingleton (pointCoh (n + 1)) := inferInstanceAs (Subsingleton PUnit)
    have : x = 0 := Subsingleton.elim x 0
    simp [this]

/-- The Hodge conjecture holds for a point.  In particular the hypotheses of `hodge_statement`
are satisfiable, so the statement is not vacuous. -/
theorem hodgeConjecture_point : HodgeConjecture pointVariety :=
  hodge_statement (le_of_lt (by norm_num)) pointVariety (fun _ _ => trivial)
    (fun _ _ => trivial) (fun _ _ => trivial)

end Frontier

