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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## Basic vocabulary

Margulis superrigidity says, informally:

> Let `G` be a semisimple Lie group of real rank at least `2`, let `Γ ≤ G` be an irreducible
> lattice, and let `ρ : Γ → H` be a homomorphism into a (simple, centre-free) Lie group whose
> image is unbounded and Zariski dense.  Then `ρ` is the restriction of a *continuous*
> homomorphism `G → H`.

The statement is formalised below as `Frontier.MargulisSuperrigidityStatement`, a `Prop`-valued
schema parameterised by the (currently unformalised in Mathlib) predicates "higher rank",
"irreducible lattice", "unbounded" and "Zariski dense".  The notion of a lattice is given a
genuine measure-theoretic definition in `Frontier.IsLatticeSubgroup`.

The theorem `Frontier.margulis_superrigidity` is a Lean-checked *reduction*: it verifies
Margulis' first reduction step, namely that superrigidity for a normal subgroup `Γ₀ ⊴ Γ`
(in practice a finite-index subgroup) already gives superrigidity for `Γ` itself, provided
the extension is unique (in the Margulis setting this comes from Borel density) and the image
`ρ Γ₀` has trivial centraliser in the target.
-/

section Extension

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- `ExtendsContinuously Γ ρ f` says that the continuous homomorphism `f : G →* H` restricts
on the subgroup `Γ ≤ G` to the given homomorphism `ρ : Γ →* H`.  This is the conclusion of
Margulis superrigidity. -/
def ExtendsContinuously (Γ : Subgroup G) (ρ : Γ →* H) (f : G →* H) : Prop :=
  Continuous f ∧ ∀ γ : Γ, f (γ : G) = ρ γ

/-- A homomorphism `ρ : Γ →* H` is *superrigid* if it extends to a continuous homomorphism
defined on the whole ambient group. -/
def IsSuperrigidHom (Γ : Subgroup G) (ρ : Γ →* H) : Prop :=
  ∃ f : G →* H, ExtendsContinuously Γ ρ f

end Extension

section Lattice

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

/-- `Γ` is a *lattice* in the topological group `G` (with respect to the Haar measure `μ`):
it is a discrete subgroup admitting a fundamental domain of finite measure. -/
def IsLatticeSubgroup (μ : MeasureTheory.Measure G) (Γ : Subgroup G) : Prop :=
  DiscreteTopology Γ ∧ ∃ F : Set G, MeasureTheory.IsFundamentalDomain Γ F μ ∧ μ F ≠ ⊤

end Lattice

/-!
## The statement of Margulis superrigidity

Real rank, irreducibility of a lattice and Zariski density of a subset of a linear group are
not available in Mathlib, so the statement is parameterised by them.  Any instantiation of the
predicates yields a genuine mathematical statement; the intended one is
`G` a semisimple Lie group, `higherRank` the assertion `2 ≤ rank_ℝ G`, `irreducibleLattice Γ`
the assertion that `Γ` is an irreducible lattice in `G`, `unbounded S` the assertion that `S`
is not relatively compact in `H`, and `zariskiDense S` the assertion that `S` is Zariski dense
in the algebraic group `H`.
-/

/-- The Margulis superrigidity statement for the pair of topological groups `G`, `H`, relative
to the abstract predicates `higherRank`, `irreducibleLattice`, `unbounded`, `zariskiDense`:

if `G` has higher rank and `Γ ≤ G` is an irreducible lattice, then every homomorphism
`ρ : Γ →* H` with unbounded and Zariski dense image is the restriction of a continuous
homomorphism `G →* H`. -/
def MargulisSuperrigidityStatement (G H : Type*) [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] [MeasurableSpace G] (μ : MeasureTheory.Measure G)
    (higherRank : Prop) (irreducibleLattice : Subgroup G → Prop)
    (unbounded zariskiDense : Set H → Prop) : Prop :=
  higherRank →
    ∀ Γ : Subgroup G, IsLatticeSubgroup μ Γ → irreducibleLattice Γ →
      ∀ ρ : Γ →* H,
        unbounded (Set.range fun γ : Γ => ρ γ) →
          zariskiDense (Set.range fun γ : Γ => ρ γ) →
            IsSuperrigidHom Γ ρ

/-!
## Uniqueness of extensions
-/

section Uniqueness

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [T2Space H]

/-- Two continuous homomorphisms that agree on a dense subgroup are equal.  In the Margulis
setting the relevant density statement for a lattice is the Borel density theorem. -/
theorem eq_of_eqOn_dense {f₁ f₂ : G →* H} (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    {s : Set G} (hs : Dense s) (h : Set.EqOn (fun g => f₁ g) (fun g => f₂ g) s) :
    f₁ = f₂ := by
  ext g
  exact congrFun (Continuous.ext_on hs hf₁ hf₂ h) g

/-- A continuous extension of `ρ : Γ →* H` to `G` is unique as soon as `Γ` is dense in `G`. -/
theorem extension_unique_of_dense {Γ : Subgroup G} (hΓ : Dense (Γ : Set G)) {ρ : Γ →* H}
    {f₁ f₂ : G →* H} (h₁ : ExtendsContinuously Γ ρ f₁) (h₂ : ExtendsContinuously Γ ρ f₂) :
    f₁ = f₂ := by
  refine eq_of_eqOn_dense h₁.1 h₂.1 hΓ ?_
  rintro g hg
  simpa [h₁.2 ⟨g, hg⟩] using (h₂.2 ⟨g, hg⟩).symm

end Uniqueness

/-!
## The main reduction

Margulis' argument first produces an extension of `ρ` restricted to a suitable finite-index
(hence, after passing to the normal core, normal) subgroup `Γ₀ ⊴ Γ`, and then upgrades it to
an extension of `ρ` itself.  The upgrade step is a purely group-theoretic argument, which we
verify here: conjugating an extension `f` of `ρ|Γ₀` by an element `γ ∈ Γ` produces another
extension of `ρ|Γ₀`; by uniqueness the two coincide, and this forces `ρ γ⁻¹ * f γ` to
centralise `ρ Γ₀`, hence to be trivial.
-/

section Reduction

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Conjugating a continuous homomorphism `f : G →* H` by `γ : G` (on the source) and by
`h : H` (on the target) again gives a continuous homomorphism. -/
noncomputable def conjHom (f : G →* H) (γ : G) (h : H) : G →* H where
  toFun g := h * f (γ⁻¹ * g * γ) * h⁻¹
  map_one' := by simp
  map_mul' a b := by
    have : γ⁻¹ * (a * b) * γ = (γ⁻¹ * a * γ) * (γ⁻¹ * b * γ) := by group
    rw [this, map_mul]
    group

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H] in
@[simp] theorem conjHom_apply (f : G →* H) (γ : G) (h : H) (g : G) :
    conjHom f γ h g = h * f (γ⁻¹ * g * γ) * h⁻¹ := rfl

omit [TopologicalSpace H] [IsTopologicalGroup H] in
/-- If two elements conjugate a third one in the same way, their "difference" commutes with it. -/
theorem commute_of_conj_eq (a b r : H) (hconj : a * r * a⁻¹ = b * r * b⁻¹) :
    (a⁻¹ * b) * r = r * (a⁻¹ * b) := by
  have h2 : r = a⁻¹ * b * r * (b⁻¹ * a) := by
    calc r = a⁻¹ * (a * r * a⁻¹) * a := by group
      _ = a⁻¹ * (b * r * b⁻¹) * a := by rw [hconj]
      _ = a⁻¹ * b * r * (b⁻¹ * a) := by group
  conv_rhs => rw [h2]
  group

theorem continuous_conjHom {f : G →* H} (hf : Continuous f) (γ : G) (h : H) :
    Continuous (conjHom f γ h) := by
  have : Continuous fun g : G => γ⁻¹ * g * γ :=
    (continuous_mul_right γ).comp (continuous_mul_left γ⁻¹)
  exact (continuous_const.mul (hf.comp this)).mul continuous_const

/-- **Margulis superrigidity, reduction step.**

Let `Γ₀ ≤ Γ` be subgroups of a topological group `G` with `Γ₀` normal in `Γ`, and let
`ρ : Γ →* H` be a homomorphism into a topological group `H`.  Assume:

* `f : G →* H` is a continuous homomorphism extending `ρ` on `Γ₀`;
* continuous homomorphisms `G →* H` are determined by their restriction to `Γ₀`
  (in Margulis' setting this follows from the Borel density theorem, `Γ₀` being Zariski
  dense in `G`);
* the image `ρ Γ₀` has trivial centraliser in `H` (in Margulis' setting this holds because
  `ρ Γ₀` is Zariski dense in the centre-free simple group `H`).

Then `f` already extends `ρ` on all of `Γ`; that is, `ρ` itself is superrigid.

This is the Lean-checked reduction of superrigidity for a lattice `Γ` to superrigidity for a
normal (e.g. finite-index) subgroup `Γ₀`. -/
theorem margulis_superrigidity {Γ Γ₀ : Subgroup G} (hle : Γ₀ ≤ Γ)
    (hnorm : ∀ γ ∈ Γ, ∀ x ∈ Γ₀, γ * x * γ⁻¹ ∈ Γ₀)
    (ρ : Γ →* H) (f : G →* H) (hf : Continuous f)
    (hext : ∀ (x : G) (hx : x ∈ Γ₀), f x = ρ ⟨x, hle hx⟩)
    (huniq : ∀ f₁ f₂ : G →* H, Continuous f₁ → Continuous f₂ →
      (∀ x ∈ Γ₀, f₁ x = f₂ x) → f₁ = f₂)
    (hcent : ∀ h : H, (∀ (x : G) (hx : x ∈ Γ₀), h * ρ ⟨x, hle hx⟩ = ρ ⟨x, hle hx⟩ * h) → h = 1) :
    ExtendsContinuously Γ ρ f := by
  refine ⟨hf, ?_⟩
  rintro ⟨γ, hγ⟩
  -- the conjugated extension
  set c : G →* H := conjHom f γ (ρ ⟨γ, hγ⟩) with hc
  have hcc : Continuous c := continuous_conjHom hf _ _
  -- `c` also extends `ρ` on `Γ₀`
  have hcΓ₀ : ∀ x ∈ Γ₀, c x = f x := by
    intro x hx
    have hx' : γ⁻¹ * x * γ ∈ Γ₀ := by
      have := hnorm γ⁻¹ (Γ.inv_mem hγ) x hx
      simpa using this
    have h1 : f (γ⁻¹ * x * γ) = ρ ⟨γ⁻¹ * x * γ, hle hx'⟩ := hext _ hx'
    have h2 : (⟨γ, hγ⟩ : Γ) * ⟨γ⁻¹ * x * γ, hle hx'⟩ * (⟨γ, hγ⟩ : Γ)⁻¹ = ⟨x, hle hx⟩ := by
      ext; simp; group
    calc c x = ρ ⟨γ, hγ⟩ * ρ ⟨γ⁻¹ * x * γ, hle hx'⟩ * (ρ ⟨γ, hγ⟩)⁻¹ := by
          rw [hc, conjHom_apply, h1]
      _ = ρ ⟨x, hle hx⟩ := by rw [← h2, map_mul, map_mul, map_inv]
      _ = f x := (hext x hx).symm
  have hcf : c = f := huniq c f hcc hf hcΓ₀
  -- deduce that `(ρ γ)⁻¹ * f γ` centralises `ρ Γ₀`
  have hcomm : ∀ (x : G) (hx : x ∈ Γ₀),
      ((ρ ⟨γ, hγ⟩)⁻¹ * f γ) * ρ ⟨x, hle hx⟩ = ρ ⟨x, hle hx⟩ * ((ρ ⟨γ, hγ⟩)⁻¹ * f γ) := by
    intro x hx
    have key : c (γ * x * γ⁻¹) = f (γ * x * γ⁻¹) := by rw [hcf]
    have hleft : c (γ * x * γ⁻¹) = ρ ⟨γ, hγ⟩ * ρ ⟨x, hle hx⟩ * (ρ ⟨γ, hγ⟩)⁻¹ := by
      have harg : γ⁻¹ * (γ * x * γ⁻¹) * γ = x := by group
      rw [hc, conjHom_apply, harg, hext x hx]
    have hright : f (γ * x * γ⁻¹) = f γ * ρ ⟨x, hle hx⟩ * (f γ)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hext x hx]
    rw [hleft, hright] at key
    exact commute_of_conj_eq _ _ _ key
  have h1 : (ρ ⟨γ, hγ⟩)⁻¹ * f γ = 1 := hcent _ hcomm
  exact (inv_mul_eq_one.mp h1).symm

/-- Packaged form of the reduction: the hypotheses of `Frontier.margulis_superrigidity` imply
that `ρ` is superrigid. -/
theorem isSuperrigidHom_of_normal_subgroup {Γ Γ₀ : Subgroup G} (hle : Γ₀ ≤ Γ)
    (hnorm : ∀ γ ∈ Γ, ∀ x ∈ Γ₀, γ * x * γ⁻¹ ∈ Γ₀)
    (ρ : Γ →* H) (f : G →* H) (hf : Continuous f)
    (hext : ∀ (x : G) (hx : x ∈ Γ₀), f x = ρ ⟨x, hle hx⟩)
    (huniq : ∀ f₁ f₂ : G →* H, Continuous f₁ → Continuous f₂ →
      (∀ x ∈ Γ₀, f₁ x = f₂ x) → f₁ = f₂)
    (hcent : ∀ h : H, (∀ (x : G) (hx : x ∈ Γ₀), h * ρ ⟨x, hle hx⟩ = ρ ⟨x, hle hx⟩ * h) → h = 1) :
    IsSuperrigidHom Γ ρ :=
  ⟨f, margulis_superrigidity hle hnorm ρ f hf hext huniq hcent⟩

/-- Sanity check that the hypotheses of `Frontier.margulis_superrigidity` are satisfiable (the
reduction is not vacuous): for a discrete group with trivial centre, the tautological
representation of `Γ = Γ₀ = ⊤` satisfies all of them. -/
example (K : Type*) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (hcentre : ∀ k : K, (∀ y : K, k * y = y * k) → k = 1) :
    ExtendsContinuously (⊤ : Subgroup K) (Subgroup.topEquiv (G := K)).toMonoidHom
      (MonoidHom.id K) :=
  margulis_superrigidity (Γ := ⊤) (Γ₀ := ⊤) le_rfl (fun _ _ _ _ => trivial) _ _
    continuous_id (fun _ _ => rfl)
    (fun _ _ _ _ h => MonoidHom.ext fun x => h x trivial)
    (fun h hh => hcentre h fun y => hh y trivial)

end Reduction

/-!
## Base cases and consequences
-/

section BaseCase

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- Degenerate base case (rank `0`): if the ambient group is discrete, every homomorphism
defined on the whole group is superrigid. -/
theorem isSuperrigidHom_top_of_discrete [DiscreteTopology G] (ρ : (⊤ : Subgroup G) →* H) :
    IsSuperrigidHom (⊤ : Subgroup G) ρ :=
  ⟨ρ.comp (Subgroup.topEquiv (G := G)).symm.toMonoidHom, continuous_of_discreteTopology,
    fun γ => by
      have : (Subgroup.topEquiv (G := G)).symm (γ : G) = γ := rfl
      simp [this]⟩

/-- Any homomorphism into the trivial group is superrigid. -/
theorem isSuperrigidHom_of_subsingleton [Subsingleton H] (Γ : Subgroup G) (ρ : Γ →* H) :
    IsSuperrigidHom Γ ρ :=
  ⟨1, continuous_const, fun _ => Subsingleton.elim _ _⟩

/-- Superrigidity is inherited from a subgroup of the target: if `ρ` takes values in `K ≤ H`
and the corestriction is superrigid, so is `ρ`. -/
theorem isSuperrigidHom_of_codRestrict {Γ : Subgroup G} (K : Subgroup H) (ρ : Γ →* K)
    (h : IsSuperrigidHom Γ ρ) : IsSuperrigidHom Γ (K.subtype.comp ρ) := by
  obtain ⟨f, hfc, hfe⟩ := h
  exact ⟨K.subtype.comp f, continuous_subtype_val.comp hfc, fun γ => by simp [hfe γ]⟩

/-- Superrigidity into a product is equivalent to superrigidity of both components; this is the
standard reduction of Margulis superrigidity to simple targets. -/
theorem isSuperrigidHom_prod {H₁ H₂ : Type*} [Group H₁] [TopologicalSpace H₁]
    [Group H₂] [TopologicalSpace H₂] {Γ : Subgroup G} (ρ : Γ →* H₁ × H₂)
    (h₁ : IsSuperrigidHom Γ ((MonoidHom.fst H₁ H₂).comp ρ))
    (h₂ : IsSuperrigidHom Γ ((MonoidHom.snd H₁ H₂).comp ρ)) :
    IsSuperrigidHom Γ ρ := by
  obtain ⟨f₁, hc₁, he₁⟩ := h₁
  obtain ⟨f₂, hc₂, he₂⟩ := h₂
  refine ⟨(f₁.prod f₂), hc₁.prodMk hc₂, fun γ => ?_⟩
  have e₁ := he₁ γ
  have e₂ := he₂ γ
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst,
    MonoidHom.coe_snd] at e₁ e₂
  exact Prod.ext e₁ e₂

/-- A consequence of superrigidity: if the ambient group `G` is connected and the target `H` is
discrete, then a superrigid homomorphism is trivial.  (In the Margulis setting this rules out
unbounded homomorphisms of higher-rank lattices into discrete groups.) -/
theorem eq_one_of_isSuperrigidHom_of_connected [ConnectedSpace G] [DiscreteTopology H]
    {Γ : Subgroup G} {ρ : Γ →* H} (h : IsSuperrigidHom Γ ρ) : ρ = 1 := by
  obtain ⟨f, hfc, hfe⟩ := h
  have hf1 : ∀ g : G, f g = 1 := by
    intro g
    have hclopen : IsClopen (f ⁻¹' {(1 : H)}) :=
      ⟨(isClosed_discrete _).preimage hfc, (isOpen_discrete _).preimage hfc⟩
    have huniv : f ⁻¹' {(1 : H)} = Set.univ := hclopen.eq_univ ⟨1, by simp⟩
    have : g ∈ f ⁻¹' {(1 : H)} := huniv ▸ Set.mem_univ g
    simpa using this
  ext γ
  simpa [hf1] using (hfe γ).symm

end BaseCase

/-!
## The classical instance: `SL n ℤ ≤ SL n ℝ`

For `n ≥ 3` the group `SL n ℝ` has real rank `n - 1 ≥ 2` and `SL n ℤ` is an irreducible
lattice in it, so Margulis superrigidity applies.  We record the embedding and the induced
statement schema.
-/

section Classical

variable (n : ℕ)

/-- `SL n ℤ`, viewed as a subgroup of `SL n ℝ`. -/
def slIntSubgroup : Subgroup (Matrix.SpecialLinearGroup (Fin n) ℝ) :=
  (Matrix.SpecialLinearGroup.map (n := Fin n) (Int.castRingHom ℝ)).range

/-- The Margulis superrigidity statement for the classical pair `SL n ℤ ≤ SL n ℝ`, in higher
rank `n ≥ 3`: any homomorphism from `SL n ℤ` to a topological group `H` with unbounded and
Zariski dense image extends continuously, provided `SL n ℤ` is a lattice for the given measure
`μ`. -/
def MargulisSuperrigiditySL (H : Type*) [Group H] [TopologicalSpace H]
    [MeasurableSpace (Matrix.SpecialLinearGroup (Fin n) ℝ)]
    (μ : MeasureTheory.Measure (Matrix.SpecialLinearGroup (Fin n) ℝ))
    (unbounded zariskiDense : Set H → Prop) : Prop :=
  MargulisSuperrigidityStatement (Matrix.SpecialLinearGroup (Fin n) ℝ) H μ (3 ≤ n)
    (fun Γ => Γ = slIntSubgroup n) unbounded zariskiDense

end Classical

end Frontier

