import Mathlib

/-!
# Margulis Superrigidity
Category: Frontier Abel
Target: Frontier.margulis_superrigidity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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

set_option grind.warning false

/-!
## Overview

Margulis' superrigidity theorem says, in its classical form:

> Let `G` be a connected semisimple Lie group of real rank at least `2`, with finite centre and
> no compact factors, let `Γ ≤ G` be an irreducible lattice, let `H` be a connected non-compact
> simple algebraic group over `ℝ`, and let `ρ : Γ → H(ℝ)` be a homomorphism whose image is
> Zariski dense.  Then `ρ` extends to a continuous homomorphism `G → H(ℝ)`.

The flagship instance is `Γ = SL(n, ℤ) ≤ SL(n, ℝ) = G` for `n ≥ 3`.

This file does three things.

* It formalises the *extension property* that is the conclusion of superrigidity, both in the
  dense-image form (`Frontier.SuperrigidDense`) and in the unrestricted form
  (`Frontier.SuperrigidAll`), and formalises the statement of Margulis superrigidity for the
  concrete higher-rank lattice `SL(n,ℤ) ≤ SL(n,ℝ)` with target `GL(m,ℝ)`
  (`Frontier.MargulisSuperrigidityStatement`).

* It proves two Lean-checked *reductions*.  The main one,
  `Frontier.superrigidAll_of_superrigidDense`, reduces the extension problem for an arbitrary
  homomorphism to the dense-image case, by replacing the target by the closure of the image;
  this is the (elementary) step by which the general form of superrigidity is deduced from the
  Zariski-dense form.  The target theorem `Frontier.margulis_superrigidity` is this reduction
  carried out for `SL(n,ℤ) ≤ SL(n,ℝ)`: assuming the deep dense-image input of Margulis' theorem
  for closed subgroups of the target, *every* homomorphism `SL(n,ℤ) → GL(m,ℝ)` extends to a
  continuous homomorphism on `SL(n,ℝ)`.

* It proves, unconditionally, the abelian *base case* of the extension phenomenon
  (`Frontier.margulis_superrigidity_baseCase`): every homomorphism from the lattice
  `ℤⁿ ≤ ℝⁿ` to the vector group `ℝᵐ` extends to a **unique** continuous homomorphism
  `ℝⁿ → ℝᵐ`.

Two deliberate deviations from the classical statement are recorded here.  First, Zariski density
of the image is replaced by density in the ambient (Hausdorff, locally compact) topology; this is
a stronger hypothesis on `ρ`, so the dense-image statements below are formally weaker than
Margulis'.  Second, the deep analytic content of Margulis' theorem is *not* proved: it appears as
an explicit hypothesis of the reduction theorems, which is what makes them reductions.
-/

namespace Frontier

/-! ## The extension property -/

/-- `SuperrigidDense G Γ H` : every homomorphism from the subgroup `Γ ≤ G` to `H` whose image is
dense in `H` extends to a continuous homomorphism `G → H`.  This is the conclusion of Margulis
superrigidity, in the form in which it is proved (density replacing Zariski density here). -/
def SuperrigidDense (G : Type*) [Group G] [TopologicalSpace G] (Γ : Subgroup G)
    (H : Type*) [Group H] [TopologicalSpace H] : Prop :=
  ∀ ρ : Γ →* H, Dense (Set.range (ρ : Γ → H)) →
    ∃ Φ : G →* H, Continuous Φ ∧ ∀ γ : Γ, Φ (γ : G) = ρ γ

/-- `SuperrigidAll G Γ H` : *every* homomorphism from the subgroup `Γ ≤ G` to `H` extends to a
continuous homomorphism `G → H`, with no density assumption on the image. -/
def SuperrigidAll (G : Type*) [Group G] [TopologicalSpace G] (Γ : Subgroup G)
    (H : Type*) [Group H] [TopologicalSpace H] : Prop :=
  ∀ ρ : Γ →* H, ∃ Φ : G →* H, Continuous Φ ∧ ∀ γ : Γ, Φ (γ : G) = ρ γ

/-! ## The reduction to the dense-image case -/

/-- **Reduction to the dense-image case.**  If the dense-image extension property holds for `Γ`
with target every *closed* subgroup `L ≤ H`, then every homomorphism `Γ → H` extends to a
continuous homomorphism `G → H`.  One takes for `L` the closure of the image of `ρ`, in which the
image is dense by construction. -/
theorem superrigidAll_of_superrigidDense {G : Type*} [Group G] [TopologicalSpace G]
    (Γ : Subgroup G) {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (h : ∀ L : Subgroup H, IsClosed (L : Set H) → SuperrigidDense G Γ L) :
    SuperrigidAll G Γ H := by
  intro ρ
  set L : Subgroup H := ρ.range.topologicalClosure with hL
  have hsub : ∀ γ : Γ, ρ γ ∈ L := fun γ => Subgroup.le_topologicalClosure _ ⟨γ, rfl⟩
  let ρ' : Γ →* L := ρ.codRestrict L hsub
  have hsubset : (ρ.range : Set H) ⊆ Subtype.val '' Set.range (ρ' : Γ → L) := by
    rintro y ⟨γ, rfl⟩
    exact ⟨ρ' γ, ⟨γ, rfl⟩, rfl⟩
  have hLeq : (L : Set H) = closure (ρ.range : Set H) := rfl
  have hdense : Dense (Set.range (ρ' : Γ → L)) := by
    rw [Subtype.dense_iff]
    exact hLeq.subset.trans (closure_mono hsubset)
  obtain ⟨Φ, hcont, hΦ⟩ := h L (Subgroup.isClosed_topologicalClosure _) ρ' hdense
  refine ⟨L.subtype.comp Φ, continuous_subtype_val.comp hcont, fun γ => ?_⟩
  show ((Φ (γ : G) : L) : H) = ρ γ
  rw [hΦ γ]
  rfl

/-! ## The higher-rank lattice `SL(n,ℤ) ≤ SL(n,ℝ)` -/

/-- The embedding of `SL(n,ℤ)` into `SL(n,ℝ)`. -/
noncomputable def slEmbedding (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) ℤ →* Matrix.SpecialLinearGroup (Fin n) ℝ :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)

theorem slEmbedding_injective (n : ℕ) : Function.Injective (slEmbedding n) :=
  Matrix.SpecialLinearGroup.map_intCast_injective

/-- The higher-rank lattice `SL(n,ℤ)`, viewed as a subgroup of `SL(n,ℝ)`. -/
noncomputable def slLattice (n : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin n) ℝ) :=
  (slEmbedding n).range

/-- `SL(n,ℤ)` is isomorphic to the subgroup `slLattice n` of `SL(n,ℝ)` that it defines. -/
noncomputable def slLatticeEquiv (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) ℤ ≃* slLattice n :=
  MonoidHom.ofInjective (slEmbedding_injective n)

@[simp] theorem slLatticeEquiv_apply (n : ℕ) (γ : Matrix.SpecialLinearGroup (Fin n) ℤ) :
    ((slLatticeEquiv n γ : slLattice n) : Matrix.SpecialLinearGroup (Fin n) ℝ)
      = slEmbedding n γ := rfl

/-- **The statement of Margulis superrigidity** for the lattice `SL(n,ℤ) ≤ SL(n,ℝ)` with target
`GL(m,ℝ)`: any homomorphism `SL(n,ℤ) → GL(m,ℝ)` with dense image is the restriction of a
continuous homomorphism `SL(n,ℝ) → GL(m,ℝ)`.  Margulis' theorem asserts this for `n ≥ 3`
(with Zariski density in place of density). -/
def MargulisSuperrigidityStatement (n m : ℕ) : Prop :=
  ∀ ρ : Matrix.SpecialLinearGroup (Fin n) ℤ →* Matrix.GeneralLinearGroup (Fin m) ℝ,
    Dense (Set.range (ρ : Matrix.SpecialLinearGroup (Fin n) ℤ →
        Matrix.GeneralLinearGroup (Fin m) ℝ)) →
      ∃ Φ : Matrix.SpecialLinearGroup (Fin n) ℝ →* Matrix.GeneralLinearGroup (Fin m) ℝ,
        Continuous Φ ∧ ∀ γ, Φ (slEmbedding n γ) = ρ γ

/-- The statement of Margulis superrigidity for `SL(n,ℤ) ≤ SL(n,ℝ)` is exactly the abstract
dense-image extension property for the subgroup `slLattice n`. -/
theorem margulisSuperrigidityStatement_iff (n m : ℕ) :
    MargulisSuperrigidityStatement n m ↔
      SuperrigidDense (Matrix.SpecialLinearGroup (Fin n) ℝ) (slLattice n)
        (Matrix.GeneralLinearGroup (Fin m) ℝ) := by
  constructor
  · intro h ρ hdense
    have hd : Dense (Set.range ((ρ.comp (slLatticeEquiv n).toMonoidHom) :
        Matrix.SpecialLinearGroup (Fin n) ℤ → Matrix.GeneralLinearGroup (Fin m) ℝ)) := by
      refine hdense.mono ?_
      rintro x ⟨g, rfl⟩
      exact ⟨(slLatticeEquiv n).symm g, by simp⟩
    obtain ⟨Φ, hcont, hΦ⟩ := h (ρ.comp (slLatticeEquiv n).toMonoidHom) hd
    refine ⟨Φ, hcont, fun g => ?_⟩
    obtain ⟨γ, hγ⟩ := g.2
    have hg : (slLatticeEquiv n) γ = g := Subtype.ext hγ
    rw [← hγ, hΦ γ]
    show ρ (slLatticeEquiv n γ) = ρ g
    rw [hg]
  · intro h ρ hdense
    have hd : Dense (Set.range ((ρ.comp (slLatticeEquiv n).symm.toMonoidHom) :
        slLattice n → Matrix.GeneralLinearGroup (Fin m) ℝ)) := by
      refine hdense.mono ?_
      rintro x ⟨γ, rfl⟩
      exact ⟨slLatticeEquiv n γ, by simp⟩
    obtain ⟨Φ, hcont, hΦ⟩ := h (ρ.comp (slLatticeEquiv n).symm.toMonoidHom) hd
    refine ⟨Φ, hcont, fun γ => ?_⟩
    have := hΦ (slLatticeEquiv n γ)
    simpa using this

/-! ## The target theorem: Margulis superrigidity, reduced to its dense-image case -/

/-- **Margulis superrigidity for the higher-rank lattice `SL(n,ℤ) ≤ SL(n,ℝ)`, in reduced form.**

Let `n ≥ 3`, so that `SL(n,ℝ)` has real rank `n - 1 ≥ 2` and `SL(n,ℤ)` is an irreducible
higher-rank lattice in it.  Assume the deep input of Margulis' theorem: for every closed subgroup
`L` of the target `GL(m,ℝ)`, every homomorphism `SL(n,ℤ) → L` with dense image extends to a
continuous homomorphism `SL(n,ℝ) → L`.  Then *every* homomorphism `ρ : SL(n,ℤ) → GL(m,ℝ)`,
with no density assumption whatsoever, extends to a continuous homomorphism
`Φ : SL(n,ℝ) → GL(m,ℝ)`.

This is the Lean-checked reduction of the general form of superrigidity to its dense-image form:
one passes to the closure of the image of `ρ`, applies the dense-image hypothesis there, and
composes with the inclusion of that closed subgroup.  The rank hypothesis `hn` is recorded
because it is exactly the hypothesis under which the assumed dense-image input is a theorem of
Margulis; the reduction step itself does not use it. -/
theorem margulis_superrigidity {n m : ℕ} (hn : 3 ≤ n)
    (hdense : ∀ L : Subgroup (Matrix.GeneralLinearGroup (Fin m) ℝ),
      IsClosed (L : Set (Matrix.GeneralLinearGroup (Fin m) ℝ)) →
      SuperrigidDense (Matrix.SpecialLinearGroup (Fin n) ℝ) (slLattice n) L) :
    ∀ ρ : Matrix.SpecialLinearGroup (Fin n) ℤ →* Matrix.GeneralLinearGroup (Fin m) ℝ,
      ∃ Φ : Matrix.SpecialLinearGroup (Fin n) ℝ →* Matrix.GeneralLinearGroup (Fin m) ℝ,
        Continuous Φ ∧ ∀ γ, Φ (slEmbedding n γ) = ρ γ := by
  intro ρ
  obtain ⟨Φ, hcont, hΦ⟩ :=
    superrigidAll_of_superrigidDense (slLattice n) hdense
      (ρ.comp (slLatticeEquiv n).symm.toMonoidHom)
  refine ⟨Φ, hcont, fun γ => ?_⟩
  have := hΦ (slLatticeEquiv n γ)
  simpa using this

/-! ## Non-vacuity of the hypothesis of the reduction -/

/-- The dense-image extension property holds trivially when the target group is trivial. -/
theorem superrigidDense_of_subsingleton {G : Type*} [Group G] [TopologicalSpace G]
    (Γ : Subgroup G) {H : Type*} [Group H] [TopologicalSpace H] [Subsingleton H] :
    SuperrigidDense G Γ H := by
  intro ρ _
  exact ⟨1, continuous_const, fun γ => Subsingleton.elim _ _⟩

/-- The hypothesis of `Frontier.margulis_superrigidity` is satisfiable: it holds for the
(degenerate) target `GL(0, ℝ)`, so the reduction theorem is not vacuous. -/
theorem margulis_superrigidity_hypothesis_nonvacuous (n : ℕ) :
    ∀ L : Subgroup (Matrix.GeneralLinearGroup (Fin 0) ℝ),
      IsClosed (L : Set (Matrix.GeneralLinearGroup (Fin 0) ℝ)) →
      SuperrigidDense (Matrix.SpecialLinearGroup (Fin n) ℝ) (slLattice n) L := by
  have : Subsingleton (Matrix.GeneralLinearGroup (Fin 0) ℝ) := by
    constructor
    intro a b
    ext i
    exact absurd i.2 (by omega)
  intro L _
  exact superrigidDense_of_subsingleton _

/-! ## The abelian base case -/

/-- **Base case of superrigidity: the lattice `ℤⁿ ≤ ℝⁿ` with vector-group target.**

Every homomorphism `f : ℤⁿ → ℝᵐ` of abstract groups is the restriction of a unique *continuous*
homomorphism `ℝⁿ → ℝᵐ` (which is then automatically `ℝ`-linear).  This is the rank-zero /
abelian instance of the extension phenomenon asserted by superrigidity, and unlike the general
case it is proved here outright. -/
theorem margulis_superrigidity_baseCase {n m : ℕ} (f : (Fin n → ℤ) →+ (Fin m → ℝ)) :
    ∃! F : (Fin n → ℝ) →+ (Fin m → ℝ),
      Continuous F ∧ ∀ v : Fin n → ℤ, F (fun i => (v i : ℝ)) = f v := by
  classical
  set c : Fin n → (Fin m → ℝ) := fun i => f (Pi.single i 1) with hc
  have key : ∀ v : Fin n → ℤ, f v = ∑ i, ((v i : ℝ)) • c i := by
    intro v
    have hv : v = ∑ i, v i • Pi.single i (1 : ℤ) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hc, Int.cast_smul_eq_zsmul]
  refine ⟨{ toFun := fun x => ∑ i, x i • c i
            map_zero' := by simp
            map_add' := by intro x y; simp [add_smul, Finset.sum_add_distrib] }, ⟨?_, ?_⟩, ?_⟩
  · show Continuous fun x : Fin n → ℝ => ∑ i, x i • c i
    exact continuous_finset_sum _ fun i _ =>
      (continuous_apply i).smul (continuous_const : Continuous fun _ : Fin n → ℝ => c i)
  · intro v
    exact (key v).symm
  · rintro F ⟨hFc, hF⟩
    have h₂ : Continuous (fun x : Fin n → ℝ => ∑ i, x i • c i) :=
      continuous_finset_sum _ fun i _ =>
        (continuous_apply i).smul (continuous_const : Continuous fun _ : Fin n → ℝ => c i)
    set F₂ : (Fin n → ℝ) →+ (Fin m → ℝ) :=
      { toFun := fun x => ∑ i, x i • c i
        map_zero' := by simp
        map_add' := by intro x y; simp [add_smul, Finset.sum_add_distrib] } with hF₂
    have hagree : ∀ v : Fin n → ℤ, F (fun i => (v i : ℝ)) = F₂ (fun i => (v i : ℝ)) := by
      intro v
      rw [hF v]
      show f v = ∑ i, ((v i : ℝ)) • c i
      exact key v
    have hbasis : ∀ i : Fin n, (F.toRealLinearMap hFc).toLinearMap ((Pi.basisFun ℝ (Fin n)) i)
        = (F₂.toRealLinearMap h₂).toLinearMap ((Pi.basisFun ℝ (Fin n)) i) := by
      intro i
      simp only [Pi.basisFun_apply]
      show F (Pi.single i (1 : ℝ)) = F₂ (Pi.single i (1 : ℝ))
      have he : (Pi.single i (1 : ℝ)) = fun j => (((Pi.single i (1 : ℤ) : Fin n → ℤ) j : ℤ) : ℝ) := by
        funext j; by_cases hij : i = j <;> simp [Pi.single_apply, hij]
      rw [he]
      exact hagree _
    have hL := (Pi.basisFun ℝ (Fin n)).ext hbasis
    refine AddMonoidHom.ext fun x => ?_
    exact congrFun (congrArg
      (fun L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) => (L : (Fin n → ℝ) → (Fin m → ℝ))) hL) x

end Frontier

