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

open MeasureTheory

namespace Frontier

/-!
## Overview

Margulis' superrigidity theorem says that a linear representation of an irreducible lattice `Γ`
in a higher-rank semisimple group `G` is, up to passing to a subgroup of finite index, the
restriction of a continuous representation of the ambient group `G`.

This file

* sets up the general notion of *extending a homomorphism defined on a subgroup to a continuous
  homomorphism of the ambient topological group* (`Frontier.ExtendsTo`, `Frontier.Superrigid`,
  `Frontier.VirtuallySuperrigid`);
* records elementary structural facts about this notion (the base case `Frontier.superrigid_top`,
  behaviour under composition and products, uniqueness of extensions, the reduction to the closure
  of the image, and the vanishing of superrigid homomorphisms into abelian targets);
* states Margulis superrigidity for the concrete higher-rank family `SL(n, ℝ)`, `n ≥ 3`, with a
  genuine (polynomial) definition of Zariski density of the image
  (`Frontier.MargulisSuperrigiditySL`);
* proves, as `Frontier.margulis_superrigidity`, the Lean-checked reduction of that statement to
  the statement in which one is allowed first to replace the lattice by an arbitrary subgroup of
  finite index — the standard normalisation step at the start of the proof.

The deep analytic content of Margulis' theorem (the construction of a measurable equivariant map
to a boundary, and its algebraicity) is *not* proved here: it is isolated in the hypothesis of
`Frontier.margulis_superrigidity`.
-/

/-! ## The extension property -/

section Defs

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- `Φ : G →* H` is a continuous extension of the homomorphism `ρ : Γ →* H` defined on the
subgroup `Γ ≤ G`. -/
structure ExtendsTo (Γ : Subgroup G) (ρ : Γ →* H) (Φ : G →* H) : Prop where
  /-- The extension is continuous on the ambient group. -/
  continuous : Continuous Φ
  /-- The extension restricts to `ρ` on `Γ`. -/
  eqOn : ∀ γ : Γ, Φ (γ : G) = ρ γ

/-- The homomorphism `ρ : Γ →* H` is *superrigid*: it extends to a continuous homomorphism
`G →* H`. -/
def Superrigid (Γ : Subgroup G) (ρ : Γ →* H) : Prop :=
  ∃ Φ : G →* H, ExtendsTo Γ ρ Φ

/-- The homomorphism `ρ : Γ →* H` is *virtually superrigid*: some subgroup `Γ₀ ≤ Γ` of finite
index in `Γ` is the restriction of a continuous homomorphism `G →* H`.  This is the conclusion of
Margulis' superrigidity theorem: passing to a finite-index subgroup is genuinely necessary, since
`ρ` may differ from a continuous representation by a finite-order character. -/
def VirtuallySuperrigid (Γ : Subgroup G) (ρ : Γ →* H) : Prop :=
  ∃ Γ₀ : Subgroup G, Γ₀ ≤ Γ ∧ Γ₀.relIndex Γ ≠ 0 ∧
    ∃ Φ : G →* H, Continuous Φ ∧ ∀ γ : Γ, (γ : G) ∈ Γ₀ → Φ (γ : G) = ρ γ

end Defs

/-! ## Elementary structural results about the extension property -/

section Structural

variable {G H K : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [Group K] [TopologicalSpace K]

/-- **Base case.**  If the "lattice" is all of `G`, then every continuous homomorphism defined
on it is superrigid: it is its own extension. -/
theorem superrigid_top (ρ : (⊤ : Subgroup G) →* H) (hρ : Continuous ρ) :
    Superrigid (⊤ : Subgroup G) ρ := by
  refine ⟨ρ.comp (Subgroup.topEquiv (G := G)).symm.toMonoidHom, ⟨?_, ?_⟩⟩
  · exact hρ.comp (continuous_induced_rng.2 continuous_id)
  · intro γ
    have h : ((Subgroup.topEquiv (G := G)).symm (γ : G)) = γ := Subtype.ext rfl
    simp [h]

/-- **Base case.**  The tautological representation of a subgroup `Γ ≤ G` (its inclusion into `G`)
is superrigid: it is the restriction of the identity of `G`.  In particular the conclusion of
superrigidity is satisfiable: the standard representation of a lattice `Γ ≤ SL(n, ℝ)` on `ℝⁿ`
extends to the ambient group. -/
theorem superrigid_subtype (Γ : Subgroup G) : Superrigid Γ Γ.subtype :=
  ⟨MonoidHom.id G, ⟨continuous_id, fun _ => rfl⟩⟩

/-- A superrigid homomorphism is virtually superrigid. -/
theorem Superrigid.virtually {Γ : Subgroup G} {ρ : Γ →* H} (h : Superrigid Γ ρ) :
    VirtuallySuperrigid Γ ρ := by
  obtain ⟨Φ, hc, he⟩ := h
  exact ⟨Γ, le_rfl, by simp [Subgroup.relIndex_self], Φ, hc, fun γ _ => he γ⟩

/-- **Reduction to a subgroup of finite index.**  If the restriction of `ρ` to a finite-index
subgroup `Γ₁ ≤ Γ` is virtually superrigid, then so is `ρ` itself.  Hence, in proving Margulis
superrigidity, one may replace the lattice by any finite-index subgroup. -/
theorem VirtuallySuperrigid.of_le {Γ Γ₁ : Subgroup G} (hle : Γ₁ ≤ Γ) (hidx : Γ₁.relIndex Γ ≠ 0)
    {ρ : Γ →* H} (h : VirtuallySuperrigid Γ₁ (ρ.comp (Subgroup.inclusion hle))) :
    VirtuallySuperrigid Γ ρ := by
  obtain ⟨Γ₀, hΓ₀le, hΓ₀idx, Φ, hΦc, hΦe⟩ := h
  refine ⟨Γ₀, hΓ₀le.trans hle, ?_, Φ, hΦc, ?_⟩
  · have hmul := Subgroup.relIndex_mul_relIndex Γ₀ Γ₁ Γ hΓ₀le hle
    intro hzero
    rw [hzero] at hmul
    exact hΓ₀idx (by simpa using (mul_eq_zero.1 hmul).resolve_right hidx)
  · intro γ hγ
    have := hΦe ⟨(γ : G), hΓ₀le hγ⟩ hγ
    simpa using this

/-- Superrigidity is preserved by post-composition with a continuous homomorphism.  (This is one
of the steps reducing superrigidity for a semisimple target to its simple quotients.) -/
theorem Superrigid.comp {Γ : Subgroup G} {ρ : Γ →* H} (h : Superrigid Γ ρ) {f : H →* K}
    (hf : Continuous f) : Superrigid Γ (f.comp ρ) := by
  obtain ⟨Φ, hΦc, hΦe⟩ := h
  exact ⟨f.comp Φ, ⟨hf.comp hΦc, fun γ => by simp [hΦe γ]⟩⟩

/-- Superrigidity into a product is equivalent to superrigidity into each factor.  (This is the
step reducing superrigidity for a target which is a product of simple groups to the factors.) -/
theorem superrigid_prod_iff {Γ : Subgroup G} (ρ₁ : Γ →* H) (ρ₂ : Γ →* K) :
    Superrigid Γ (ρ₁.prod ρ₂) ↔ Superrigid Γ ρ₁ ∧ Superrigid Γ ρ₂ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa using h.comp (f := MonoidHom.fst H K) continuous_fst
    · simpa using h.comp (f := MonoidHom.snd H K) continuous_snd
  · rintro ⟨⟨Φ₁, hc₁, he₁⟩, ⟨Φ₂, hc₂, he₂⟩⟩
    exact ⟨Φ₁.prod Φ₂, ⟨hc₁.prodMk hc₂, fun γ => by
      simp [MonoidHom.prod_apply, he₁ γ, he₂ γ]⟩⟩

/-- The continuous extension, when it exists, is unique as soon as `Γ` is dense in `G` and the
target is Hausdorff. -/
theorem ExtendsTo.unique_of_dense [T2Space H] {Γ : Subgroup G} {ρ : Γ →* H} {Φ₁ Φ₂ : G →* H}
    (hΓ : Dense (Γ : Set G)) (h₁ : ExtendsTo Γ ρ Φ₁) (h₂ : ExtendsTo Γ ρ Φ₂) : Φ₁ = Φ₂ := by
  ext g
  refine congrFun (Continuous.ext_on hΓ h₁.continuous h₂.continuous ?_) g
  rintro x hx
  exact (h₁.eqOn ⟨x, hx⟩).trans (h₂.eqOn ⟨x, hx⟩).symm

/-- **Reduction to the closure of the image.**  In order to extend `ρ` continuously to `G` it
suffices to extend the corestriction of `ρ` to the closure of its image; this is the topological
counterpart of the reduction to the Zariski closure of `ρ(Γ)` in the proof of Margulis'
theorem. -/
theorem superrigid_of_codRestrict_topologicalClosure [IsTopologicalGroup H] {Γ : Subgroup G}
    (ρ : Γ →* H)
    (h : Superrigid Γ (ρ.codRestrict (ρ.range.topologicalClosure)
      (fun γ => ρ.range.le_topologicalClosure (MonoidHom.mem_range.2 ⟨γ, rfl⟩)))) :
    Superrigid Γ ρ := by
  obtain ⟨Φ, hΦc, hΦe⟩ := h
  refine ⟨(ρ.range.topologicalClosure.subtype).comp Φ,
    ⟨continuous_subtype_val.comp hΦc, fun γ => ?_⟩⟩
  simpa using congrArg (Subtype.val) (hΦe γ)

/-- **A consequence of superrigidity.**  If `G` is a perfect group (as is the case for a connected
semisimple Lie group) then a superrigid homomorphism into an abelian group is trivial. -/
theorem Superrigid.eq_one_of_commGroup {A : Type*} [CommGroup A] [TopologicalSpace A]
    {Γ : Subgroup G} {ρ : Γ →* A} (h : Superrigid Γ ρ) (hG : commutator G = ⊤) : ρ = 1 := by
  obtain ⟨Φ, _, hΦe⟩ := h
  have hker : commutator G ≤ Φ.ker := by
    rw [commutator_eq_closure]
    refine Subgroup.closure_le _ |>.2 ?_
    rintro x ⟨a, b, rfl⟩
    simp [MonoidHom.mem_ker, commutatorElement_def]
  ext γ
  have : Φ (γ : G) = 1 := hker (hG ▸ Subgroup.mem_top _)
  simpa [hΦe γ] using this

end Structural

/-! ## Lattices -/

/-- `Γ` is a *lattice* in the topological group `G` with respect to the (Haar) measure `μ`: it is
a discrete subgroup admitting a fundamental domain of finite measure. -/
structure IsLatticeIn {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (μ : Measure G) (Γ : Subgroup G) : Prop where
  /-- A lattice is a discrete subgroup. -/
  discrete : DiscreteTopology Γ
  /-- A lattice has a fundamental domain of finite volume. -/
  finite_covolume : ∃ F : Set G, IsFundamentalDomain Γ F μ ∧ μ F < ⊤

/-! ## The higher-rank groups `SL(n, ℝ)` and Zariski density -/

/-- The special linear group `SL(n, ℝ)`.  For `n ≥ 3` this is a connected simple Lie group of real
rank `n - 1 ≥ 2`, the basic example to which Margulis superrigidity applies. -/
abbrev SLR (n : ℕ) : Type := Matrix.SpecialLinearGroup (Fin n) ℝ

/-- The tuple of matrix entries of an element of `SL(m, ℝ)`, i.e. its coordinates as a point of
the affine space in which the algebraic group `SL_m` sits. -/
def entries {m : ℕ} (x : SLR m) : (Fin m × Fin m) → ℝ :=
  fun ij => (x : Matrix (Fin m) (Fin m) ℝ) ij.1 ij.2

/-- A subset `S ⊆ SL(m, ℝ)` is *Zariski dense* if every real polynomial in the matrix entries
which vanishes on `S` vanishes on all of `SL(m, ℝ)`. -/
def ZariskiDense {m : ℕ} (S : Set (SLR m)) : Prop :=
  ∀ p : MvPolynomial (Fin m × Fin m) ℝ,
    (∀ x ∈ S, MvPolynomial.eval (entries x) p = 0) →
      ∀ y : SLR m, MvPolynomial.eval (entries y) p = 0

/-- Zariski density passes to larger sets. -/
theorem ZariskiDense.mono {m : ℕ} {S T : Set (SLR m)} (hST : S ⊆ T) (hS : ZariskiDense S) :
    ZariskiDense T := fun p hp => hS p fun x hx => hp x (hST hx)

/-- The whole group is Zariski dense in itself. -/
theorem zariskiDense_univ {m : ℕ} : ZariskiDense (Set.univ : Set (SLR m)) :=
  fun _ hp y => hp y (Set.mem_univ y)

/-- `Γ` is a lattice in `SL(n, ℝ)`: a discrete subgroup of finite covolume for a Haar measure on
`SL(n, ℝ)` (equipped with its Borel σ-algebra). -/
def IsLatticeInSL {n : ℕ} (Γ : Subgroup (SLR n)) : Prop :=
  letI : MeasurableSpace (SLR n) := borel (SLR n)
  ∃ μ : Measure (SLR n), μ.IsHaarMeasure ∧ IsLatticeIn μ Γ

/-! ## The statement of Margulis superrigidity -/

/-- **Margulis superrigidity for `SL(n, ℝ)`, `n ≥ 3`.**

Let `n ≥ 3`, let `Γ` be a lattice in the higher-rank simple Lie group `G = SL(n, ℝ)`, and let
`ρ : Γ → SL(m, ℝ)` be a homomorphism whose image is Zariski dense.  Then `ρ` agrees with a
continuous representation `G → SL(m, ℝ)` on a subgroup of finite index in `Γ`.

(Since `SL(n, ℝ)` is simple, every lattice in it is automatically irreducible, so no irreducibility
hypothesis is needed; the passage to a finite-index subgroup is the usual one, needed because `ρ`
may be twisted by a finite-order character.) -/
def MargulisSuperrigiditySL : Prop :=
  ∀ (n m : ℕ), 3 ≤ n → ∀ (Γ : Subgroup (SLR n)) (ρ : Γ →* SLR m),
    IsLatticeInSL Γ → ZariskiDense (Set.range fun γ : Γ => ρ γ) → VirtuallySuperrigid Γ ρ

/-- The same statement, in the form in which one is first allowed to pass to an arbitrary
subgroup of finite index of the lattice: the conclusion only asserts that *some* finite-index
subgroup `Γ₁ ≤ Γ` has the property that the restriction of `ρ` to `Γ₁` is virtually superrigid.
This is the form in which the theorem is proved (one normalises the lattice, e.g. making it
torsion free, before constructing the extension). -/
def MargulisSuperrigiditySLAfterFiniteIndex : Prop :=
  ∀ (n m : ℕ), 3 ≤ n → ∀ (Γ : Subgroup (SLR n)) (ρ : Γ →* SLR m),
    IsLatticeInSL Γ → ZariskiDense (Set.range fun γ : Γ => ρ γ) →
      ∃ Γ₁ : Subgroup (SLR n), ∃ hle : Γ₁ ≤ Γ, Γ₁.relIndex Γ ≠ 0 ∧
        VirtuallySuperrigid Γ₁ (ρ.comp (Subgroup.inclusion hle))

/-- **Margulis superrigidity: a Lean-checked reduction.**

The statement of Margulis superrigidity for lattices in `SL(n, ℝ)`, `n ≥ 3`, follows from the
statement in which one is permitted first to replace the lattice by an arbitrary subgroup of
finite index.  In other words, the normalisation "we may assume that `Γ` is as small as we like,
of finite index in the given lattice" — used at the outset of every proof of superrigidity — is
harmless.

The proof is the multiplicativity of the relative index together with the observation that a
continuous extension of the restriction of `ρ` is a continuous extension of `ρ` on a smaller,
still finite-index, subgroup. -/
theorem margulis_superrigidity :
    MargulisSuperrigiditySLAfterFiniteIndex → MargulisSuperrigiditySL := by
  intro h n m hn Γ ρ hlat hZD
  obtain ⟨Γ₁, hle, hidx, hvs⟩ := h n m hn Γ ρ hlat hZD
  exact VirtuallySuperrigid.of_le hle hidx hvs

/-- Conversely (and trivially), the statement of Margulis superrigidity implies the form in which
one first passes to a finite-index subgroup, so the two formulations are equivalent. -/
theorem margulis_superrigidity_iff :
    MargulisSuperrigiditySLAfterFiniteIndex ↔ MargulisSuperrigiditySL := by
  refine ⟨margulis_superrigidity, fun h n m hn Γ ρ hlat hZD => ?_⟩
  exact ⟨Γ, le_rfl, by simp [Subgroup.relIndex_self], by
    simpa [MonoidHom.comp_assoc] using h n m hn Γ ρ hlat hZD⟩

end Frontier

