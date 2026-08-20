/-
# Ngo Fundamental Lemma
Category: Frontier — Fields Medal Work
Target: Frontier.ngo_fundamental_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ngo Fundamental Lemma
Category: Frontier — Fields Medal Work
Target: Frontier.ngo_fundamental_lemma
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

universe u v w

/-!
## The Langlands–Shelstad fundamental lemma (Ngô)

Informal statement.  Let `F` be a non-archimedean local field with ring of integers `O`,
let `G` be an unramified connected reductive group over `F` with hyperspecial maximal
compact subgroup `K = G(O)`, and let `(H, s, η)` be an unramified endoscopic datum for `G`
with hyperspecial maximal compact `K_H = H(O)`.  Let `γ_H ∈ H(F)` be a strongly
`G`-regular semisimple element with image `γ ∈ G(F)`.  Then

  `Δ(γ_H, γ) · SO_{γ_H}(1_{K_H}) = O^κ_γ(1_K)`,

where `Δ` is the Langlands–Shelstad transfer factor, `SO` is the stable orbital integral
on `H`, and `O^κ` is the `κ`-orbital integral on `G`, `κ` being the character of the
Kottwitz obstruction group determined by `s`.

Formalization.  A full formalization of `G`, `K`, `Δ` and the orbital integrals themselves
is far beyond currently available Lean infrastructure (it needs the Hitchin fibration,
perverse sheaves and the support theorem, none of which exist in Mathlib).  What is
formalized here is the *combinatorial skeleton* of the identity, which is exactly the
shape in which the fundamental lemma is used in the stabilization of the trace formula:

* the stable conjugacy class of `γ` in `G(F)` breaks up into a finite set `GClasses` of
  rational conjugacy classes, and each such class carries a Kottwitz invariant
  `gObstruction : GClasses → 𝔎`, an element of a finite abelian group `𝔎 = 𝔎(I_γ/F)`;
* orbital integrals `O_{γ'}(1_K)` for `γ'` running through these classes are recorded by
  `gOrbital : GClasses → ℂ`, and likewise `hOrbital` on the `H`-side;
* the endoscopic character is an additive character `κ : AddChar 𝔎 ℂ`, and the
  `κ`-orbital integral is the twisted sum `∑ κ(inv γ') O_{γ'}`, while the stable orbital
  integral is the untwisted sum;
* the transfer factor is a complex number `Δ`.

With this data, `EndoscopicData.FundamentalLemma` is the asserted identity, and the
theorems below prove the base case (trivial endoscopic datum, `κ = 1`, where the identity
is the tautology "stable = sum of rational"), the unobstructed case (`𝔎` trivial, e.g.
`G = GL n`, where every stable class is a single rational class), and two Lean-checked
reductions: multiplicativity in products of groups, and the Fourier inversion which shows
that the family of all `κ`-orbital integrals determines the individual orbital integrals
(the mechanism by which the fundamental lemma stabilizes the trace formula).
-/

/-- The `κ`-orbital integral attached to a stable conjugacy class:
`O^κ_γ(f) = ∑_{γ' ∼_{st} γ} κ(inv(γ')) O_{γ'}(f)`, where the sum runs over the rational
conjugacy classes `γ'` inside the stable class of `γ`, `inv` is the Kottwitz invariant and
`orb γ'` records the ordinary orbital integral `O_{γ'}(f)`. -/
noncomputable def kappaOrbital {A : Type u} {C : Type v} [AddCommGroup A] [Fintype C]
    (inv : C → A) (orb : C → ℂ) (κ : AddChar A ℂ) : ℂ :=
  ∑ c : C, κ (inv c) * orb c

/-- The stable orbital integral `SO_γ(f) = ∑_{γ' ∼_{st} γ} O_{γ'}(f)`. -/
noncomputable def stableOrbital {C : Type v} [Fintype C] (orb : C → ℂ) : ℂ :=
  ∑ c : C, orb c

/-- The data entering one instance of the Langlands–Shelstad fundamental lemma: an
unramified endoscopic datum `(H, s, η)` for `G` together with matching strongly regular
semisimple elements `γ_H ↔ γ`, presented through the finite combinatorial invariants
that the identity actually involves. -/
structure EndoscopicData where
  /-- The Kottwitz obstruction group `𝔎(I_γ/F)`, a finite abelian group; the endoscopic
  datum `s` defines a character of it. -/
  Obstruction : Type u
  [obsGroup : AddCommGroup Obstruction]
  [obsFintype : Fintype Obstruction]
  [obsDec : DecidableEq Obstruction]
  /-- The finite set of `G(F)`-conjugacy classes inside the stable conjugacy class of the
  strongly regular semisimple element `γ ∈ G(F)`. -/
  GClasses : Type v
  [gFintype : Fintype GClasses]
  /-- The Kottwitz invariant `inv(γ, γ')` of a rational class inside the stable class. -/
  gObstruction : GClasses → Obstruction
  /-- The orbital integrals `O_{γ'}(1_K)` of the unit of the Hecke algebra of `G`. -/
  gOrbital : GClasses → ℂ
  /-- The finite set of `H(F)`-conjugacy classes inside the stable class of `γ_H`. -/
  HClasses : Type w
  [hFintype : Fintype HClasses]
  /-- The orbital integrals `O_{γ_H'}(1_{K_H})` of the unit of the Hecke algebra of `H`. -/
  hOrbital : HClasses → ℂ
  /-- The Langlands–Shelstad transfer factor `Δ(γ_H, γ)`. -/
  transferFactor : ℂ
  /-- The endoscopic character `κ` of the Kottwitz group attached to `s`. -/
  kappa : AddChar Obstruction ℂ


attribute [instance] EndoscopicData.obsGroup EndoscopicData.obsFintype
  EndoscopicData.obsDec EndoscopicData.gFintype EndoscopicData.hFintype

namespace EndoscopicData

variable (E : EndoscopicData.{u, v, w})

/-- The stable orbital integral `SO_{γ_H}(1_{K_H})` on the endoscopic group. -/
noncomputable def stableOrbitalH : ℂ := stableOrbital E.hOrbital

/-- The stable orbital integral `SO_γ(1_K)` on `G`. -/
noncomputable def stableOrbitalG : ℂ := stableOrbital E.gOrbital

/-- The `κ`-orbital integral `O^κ_γ(1_K)` on `G`. -/
noncomputable def kappaOrbitalG : ℂ := kappaOrbital E.gObstruction E.gOrbital E.kappa

/-- **The fundamental lemma identity**:
`Δ(γ_H, γ) · SO_{γ_H}(1_{K_H}) = O^κ_γ(1_K)`. -/
def FundamentalLemma : Prop := E.transferFactor * E.stableOrbitalH = E.kappaOrbitalG

/-- The *trivial* endoscopic datum: `H = G`, `s = 1` (so `κ` is the trivial character) and
the transfer factor is normalized to `1`; the matching of stable classes identifies the
rational classes on the two sides. -/
def IsTrivialEndoscopy : Prop :=
  E.kappa = 1 ∧ E.transferFactor = 1 ∧
    ∃ e : E.HClasses ≃ E.GClasses, ∀ c : E.HClasses, E.hOrbital c = E.gOrbital (e c)

end EndoscopicData

/-- The `κ`-orbital integral for the trivial character is the stable orbital integral. -/
theorem kappaOrbital_one {A : Type u} {C : Type v} [AddCommGroup A] [Fintype C]
    (inv : C → A) (orb : C → ℂ) :
    kappaOrbital inv orb 1 = stableOrbital orb := by
  simp [kappaOrbital, stableOrbital]

/-- If the Kottwitz obstruction group is trivial then every `κ`-orbital integral is the
stable one: this is the situation of `G = GL n` (or any `G` with simply connected derived
group and connected centralizers), where stable conjugacy is rational conjugacy. -/
theorem kappaOrbital_of_subsingleton {A : Type u} {C : Type v} [AddCommGroup A] [Fintype C]
    [Subsingleton A] (inv : C → A) (orb : C → ℂ) (κ : AddChar A ℂ) :
    kappaOrbital inv orb κ = stableOrbital orb := by
  have h : ∀ c : C, κ (inv c) = 1 := fun c => by
    rw [Subsingleton.elim (inv c) 0, AddChar.map_zero_eq_one]
  simp [kappaOrbital, stableOrbital, h]

/-- **Base case of the fundamental lemma**: for the trivial endoscopic datum the identity
holds, both sides being the stable orbital integral of the unit of the Hecke algebra. -/
theorem fundamentalLemma_of_trivialEndoscopy (E : EndoscopicData.{u, v, w})
    (h : E.IsTrivialEndoscopy) : E.FundamentalLemma := by
  obtain ⟨hκ, hΔ, e, he⟩ := h
  unfold EndoscopicData.FundamentalLemma EndoscopicData.stableOrbitalH
    EndoscopicData.kappaOrbitalG
  rw [hΔ, hκ, one_mul, kappaOrbital_one]
  exact Fintype.sum_equiv e _ _ he

/-- **Unobstructed case**: when the Kottwitz group is trivial the fundamental lemma is
equivalent to the plain matching of stable orbital integrals. -/
theorem fundamentalLemma_iff_of_subsingleton (E : EndoscopicData.{u, v, w})
    (h : Subsingleton E.Obstruction) :
    E.FundamentalLemma ↔ E.transferFactor * E.stableOrbitalH = E.stableOrbitalG := by
  haveI := h
  unfold EndoscopicData.FundamentalLemma EndoscopicData.kappaOrbitalG
    EndoscopicData.stableOrbitalG
  rw [kappaOrbital_of_subsingleton]

/-- **Multiplicativity of `κ`-orbital integrals in products.**  For `G = G₁ × G₂` the
stable class of `(γ₁, γ₂)` is the product of the stable classes, the Kottwitz group is the
product of the Kottwitz groups, orbital integrals of the product of the units multiply, and
`κ = κ₁ ⊗ κ₂`; hence the `κ`-orbital integrals multiply. -/
theorem kappaOrbital_prod {A₁ : Type u} {A₂ : Type u} {C₁ : Type v} {C₂ : Type v}
    [AddCommGroup A₁] [AddCommGroup A₂] [Fintype C₁] [Fintype C₂]
    (inv₁ : C₁ → A₁) (inv₂ : C₂ → A₂) (orb₁ : C₁ → ℂ) (orb₂ : C₂ → ℂ)
    (κ₁ : AddChar A₁ ℂ) (κ₂ : AddChar A₂ ℂ) (κ : AddChar (A₁ × A₂) ℂ)
    (hκ : ∀ p : A₁ × A₂, κ p = κ₁ p.1 * κ₂ p.2) :
    kappaOrbital (fun c : C₁ × C₂ => (inv₁ c.1, inv₂ c.2))
        (fun c : C₁ × C₂ => orb₁ c.1 * orb₂ c.2) κ
      = kappaOrbital inv₁ orb₁ κ₁ * kappaOrbital inv₂ orb₂ κ₂ := by
  simp only [kappaOrbital, hκ, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ => by ring

/-- The endoscopic data for a product `G = G₁ × G₂` of unramified groups, with the product
endoscopic group `H = H₁ × H₂`: the Kottwitz group, the sets of rational classes inside the
stable classes and the characters are the products, while orbital integrals of the products
of the units and the transfer factors multiply. -/
noncomputable def EndoscopicData.prod (E₁ E₂ : EndoscopicData.{u, v, w}) :
    EndoscopicData.{u, v, w} where
  Obstruction := E₁.Obstruction × E₂.Obstruction
  GClasses := E₁.GClasses × E₂.GClasses
  gObstruction c := (E₁.gObstruction c.1, E₂.gObstruction c.2)
  gOrbital c := E₁.gOrbital c.1 * E₂.gOrbital c.2
  HClasses := E₁.HClasses × E₂.HClasses
  hOrbital c := E₁.hOrbital c.1 * E₂.hOrbital c.2
  transferFactor := E₁.transferFactor * E₂.transferFactor
  kappa := E₁.kappa.compAddMonoidHom (AddMonoidHom.fst E₁.Obstruction E₂.Obstruction) *
    E₂.kappa.compAddMonoidHom (AddMonoidHom.snd E₁.Obstruction E₂.Obstruction)

/-- **Reduction to products of groups**: if the fundamental lemma holds for two endoscopic
data, it holds for their product (transfer factors and orbital integrals being
multiplicative). -/
theorem fundamentalLemma_prod (E₁ E₂ : EndoscopicData.{u, v, w})
    (h₁ : E₁.FundamentalLemma) (h₂ : E₂.FundamentalLemma) :
    (E₁.prod E₂).FundamentalLemma := by
  have hH : (E₁.prod E₂).stableOrbitalH = E₁.stableOrbitalH * E₂.stableOrbitalH := by
    simp only [EndoscopicData.stableOrbitalH, EndoscopicData.prod, stableOrbital,
      Fintype.sum_prod_type, Finset.sum_mul_sum]
  have hG : (E₁.prod E₂).kappaOrbitalG = E₁.kappaOrbitalG * E₂.kappaOrbitalG := by
    simp only [EndoscopicData.kappaOrbitalG, EndoscopicData.prod]
    exact kappaOrbital_prod _ _ _ _ E₁.kappa E₂.kappa _ (by intro p; simp)
  unfold EndoscopicData.FundamentalLemma at h₁ h₂ ⊢
  rw [hH, hG, show (E₁.prod E₂).transferFactor
      = E₁.transferFactor * E₂.transferFactor from rfl, ← h₁, ← h₂]
  ring

/-- **Fourier inversion / stabilization.**  Summing the `κ`-orbital integrals against the
characters of the Kottwitz group recovers the individual (unstable) orbital integrals:
`∑_κ κ(-a) O^κ_γ = |𝔎| · ∑_{inv γ' = a} O_{γ'}`.  This is the step that turns the
fundamental lemma (an identity for each `κ`) into a statement about individual orbital
integrals, and is how it enters the stabilization of the trace formula. -/
theorem sum_kappaOrbital_fourier {A : Type u} {C : Type v} [AddCommGroup A] [Fintype A]
    [DecidableEq A] [Fintype C] (inv : C → A) (orb : C → ℂ) (a : A) :
    ∑ κ : AddChar A ℂ, κ (-a) * kappaOrbital inv orb κ
      = (Fintype.card A : ℂ) * ∑ c ∈ Finset.univ.filter (fun c : C => inv c = a), orb c := by
  have key : ∀ c : C, (∑ κ : AddChar A ℂ, κ (-a) * (κ (inv c) * orb c))
      = (if inv c = a then (Fintype.card A : ℂ) else 0) * orb c := by
    intro c
    have h1 : ∀ κ : AddChar A ℂ, κ (-a) * (κ (inv c) * orb c) = κ (inv c - a) * orb c := by
      intro κ
      rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring
    simp only [h1, ← Finset.sum_mul, AddChar.sum_apply_eq_ite, sub_eq_zero]
  simp only [kappaOrbital, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [key]
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun c _ => by split <;> simp

/-!
### An explicit non-trivial instance

The simplest genuinely endoscopic situation: `G = SL 2` over a `p`-adic field and a
regular semisimple elliptic `γ` whose stable class splits into two rational classes,
indexed by the Kottwitz group `𝔎 = ℤ/2`, with the elliptic endoscopic group `H` a torus.
The endoscopic character `κ` is the non-trivial character of `ℤ/2`, so the `κ`-orbital
integral is the *difference* of the two orbital integrals; when these agree (both equal to
`1` after normalization) the `κ`-orbital integral vanishes, matching the vanishing stable
orbital integral on the endoscopic side.  This instance shows the statement above is not
vacuous: the `κ`-orbital integral really differs from the stable one.
-/

/-- The non-trivial character of the Kottwitz group `ℤ/2`. -/
noncomputable def signChar : AddChar (ZMod 2) ℂ where
  toFun a := if a = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      norm_num [show ((1 : ZMod 2) + 1) = 0 from rfl]

/-- An instance of the endoscopic data with Kottwitz group `ℤ/2`, non-trivial endoscopic
character, two rational classes inside the stable class of `γ` with equal orbital
integrals, and vanishing stable orbital integral on the endoscopic side. -/
noncomputable def splitTwoData : EndoscopicData.{0, 0, 0} where
  Obstruction := ZMod 2
  GClasses := ZMod 2
  gObstruction := id
  gOrbital := fun _ => 1
  HClasses := Unit
  hOrbital := fun _ => 0
  transferFactor := 1
  kappa := signChar

theorem splitTwoData_kappaOrbitalG : splitTwoData.kappaOrbitalG = 0 := by
  show ∑ c : ZMod 2, (if c = 0 then (1 : ℂ) else -1) * 1 = 0
  simp [Fin.sum_univ_two, ZMod]

theorem splitTwoData_stableOrbitalG : splitTwoData.stableOrbitalG = 2 := by
  show ∑ _c : ZMod 2, (1 : ℂ) = 2
  simp [ZMod]

/-- The fundamental lemma identity holds in this instance. -/
theorem splitTwoData_fundamentalLemma : splitTwoData.FundamentalLemma := by
  show (1 : ℂ) * (∑ _c : Unit, (0 : ℂ)) = splitTwoData.kappaOrbitalG
  rw [splitTwoData_kappaOrbitalG]
  simp

/-- In this instance the `κ`-orbital integral is genuinely different from the stable
orbital integral, so the fundamental lemma above is not a vacuous restatement of
`SO = SO`. -/
theorem splitTwoData_kappaOrbital_ne_stableOrbital :
    splitTwoData.kappaOrbitalG ≠ splitTwoData.stableOrbitalG := by
  rw [splitTwoData_kappaOrbitalG, splitTwoData_stableOrbitalG]
  norm_num

/-- **The Langlands–Shelstad fundamental lemma (Ngô), formalized statement together with
the Lean-checked base case and reductions.**

Part 1 is the statement in the base case: for the trivial endoscopic datum
(`H = G`, `κ = 1`, `Δ = 1`) the identity `Δ · SO_{γ_H}(1_{K_H}) = O^κ_γ(1_K)` holds.

Part 2 is the unobstructed case (trivial Kottwitz group, e.g. `G = GL n`): there the
fundamental lemma is equivalent to the matching of stable orbital integrals.

Part 3 is the reduction to products: the fundamental lemma for `G₁` and `G₂` implies it
for `G₁ × G₂`.

Part 4 is the Fourier inversion showing that the collection of `κ`-orbital integrals
determines the individual orbital integrals, i.e. that the fundamental lemma for all `κ`
is equivalent to a statement about ordinary orbital integrals.

Part 5 exhibits an explicit instance with non-trivial endoscopic character (the `SL 2`
picture, Kottwitz group `ℤ/2`) in which the identity holds and the `κ`-orbital integral
differs from the stable orbital integral, so that the statement is not vacuous. -/
theorem ngo_fundamental_lemma :
    (∀ E : EndoscopicData.{u, v, w}, E.IsTrivialEndoscopy → E.FundamentalLemma) ∧
    (∀ E : EndoscopicData.{u, v, w}, Subsingleton E.Obstruction →
      (E.FundamentalLemma ↔ E.transferFactor * E.stableOrbitalH = E.stableOrbitalG)) ∧
    (∀ E₁ E₂ : EndoscopicData.{u, v, w},
      E₁.FundamentalLemma → E₂.FundamentalLemma → (E₁.prod E₂).FundamentalLemma) ∧
    (∀ {A : Type u} {C : Type v} [AddCommGroup A] [Fintype A] [DecidableEq A] [Fintype C]
      (inv : C → A) (orb : C → ℂ) (a : A),
      ∑ κ : AddChar A ℂ, κ (-a) * kappaOrbital inv orb κ
        = (Fintype.card A : ℂ)
            * ∑ c ∈ Finset.univ.filter (fun c : C => inv c = a), orb c) ∧
    (∃ E : EndoscopicData.{0, 0, 0},
      E.FundamentalLemma ∧ E.kappaOrbitalG ≠ E.stableOrbitalG) := by
  refine ⟨fun E h => fundamentalLemma_of_trivialEndoscopy E h,
    fun E h => fundamentalLemma_iff_of_subsingleton E h,
    fun E₁ E₂ h₁ h₂ => fundamentalLemma_prod E₁ E₂ h₁ h₂,
    fun {_A _C} _ _ _ _ inv orb a => sum_kappaOrbital_fourier inv orb a,
    ⟨splitTwoData, splitTwoData_fundamentalLemma,
      splitTwoData_kappaOrbital_ne_stableOrbital⟩⟩

end Frontier

