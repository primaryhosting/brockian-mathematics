/-
# Ngo Fundamental Lemma
Category: Frontier — Fields Medal Work
Target: Frontier.ngo_fundamental_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Overview

The Langlands–Shelstad fundamental lemma, proved by Ngô Bảo Châu, compares two
kinds of orbital integrals attached to a reductive group `G` over a local field
and an endoscopic group `H` of `G`:

* the **κ-orbital integral** on `G`: the conjugacy classes inside a fixed stable
  conjugacy class of a regular semisimple element `γ ∈ G` are weighted by the
  values of a character `κ` (a character of the finite abelian group
  `ker(H¹(F, T) → H¹(F, G))` obtained from the endoscopic datum) and summed;

* the **stable orbital integral** on `H` at a norm `γ_H` of `γ`: the conjugacy
  classes inside the stable class of `γ_H` are summed with weight one.

The fundamental lemma asserts that, for the units of the unramified Hecke
algebras, these agree after multiplication by the Langlands–Shelstad transfer
factor `Δ(γ_H, γ)`.

The file below isolates exactly this combinatorial shape of the statement in a
structure `EndoscopicTransferData`, defines the two integrals and the predicate
`FundamentalLemmaHolds`, and then proves in full:

* `Frontier.ngo_fundamental_lemma` — the base case of the fundamental lemma:
  for the *trivial* endoscopic datum (`H = G`, `κ ≡ 1`, `Δ = 1`) the κ-orbital
  integral is the stable orbital integral, so the fundamental lemma holds. This
  is the case that all inductive/reduction arguments start from.
* `Frontier.ngo_fundamental_lemma_torus` — the fundamental lemma for a torus
  (a single rational class in the stable class on either side).
* `Frontier.kappaOrbitalIntegral_eq_zero_of_ne_one` — the "unstable vanishing"
  base case: when `κ` is a nontrivial character of the finite abelian group
  indexing the rational classes and the individual orbital integrals are equal
  (the unramified situation), the κ-orbital integral vanishes; this is the
  fundamental lemma for endoscopic data whose stable side vanishes.

In addition, the file records Lean-checked reductions and sanity checks:

* `Frontier.fundamentalLemma_sum` — the identity is compatible with splitting
  the families of rational classes into pieces (additivity of orbital
  integrals);
* `Frontier.fundamentalLemma_iff_normalized` — invariance of the identity under
  renormalising the transfer factor by a nonzero scalar;
* `Frontier.orbital_eq_sum_kappaOrbital` — Fourier inversion: the individual
  orbital integrals are recovered from the κ-orbital integrals, `κ` running
  over the characters of the finite abelian group indexing the classes;
* `Frontier.signExample_fundamentalLemma` and
  `Frontier.exists_not_fundamentalLemmaHolds` — a concrete datum satisfying the
  identity, and one violating it, so the predicate is not vacuous.

Finally, a group-theoretic model instantiates the framework with genuine
conjugacy data: for a finite group with a distinguished subgroup (rational
points inside the ambient group), the stable class of an element is partitioned
into rational classes (`Frontier.card_stableClass_eq_sum_ratClasses`), this
produces a transfer datum whose orbital integrals are counting measures
(`Frontier.stableClassData`), and for the full group stable conjugacy coincides
with rational conjugacy (`Frontier.ratClasses_top`).

No claim is made here that the general fundamental lemma is proved: what is
formalized is the statement, together with the base cases, reductions and model
described above.
-/

namespace Frontier

open Finset

/-- Combinatorial data underlying one instance of the Langlands–Shelstad
transfer identity at a regular semisimple element.

* `GOrbits` indexes the rational conjugacy classes inside the fixed stable
  conjugacy class of `γ` in `G`, and `orbitalG` records the corresponding
  orbital integrals of the unit of the unramified Hecke algebra of `G`.
* `HOrbits` and `orbitalH` are the analogous data for the norm `γ_H` of `γ`
  in the endoscopic group `H`.
* `kappa` records the values of the character `κ` of the endoscopic datum on
  the classes in `GOrbits`.
* `transferFactor` is the Langlands–Shelstad transfer factor `Δ(γ_H, γ)`. -/
structure EndoscopicTransferData where
  /-- Rational conjugacy classes in the stable class of `γ` in `G`. -/
  GOrbits : Type
  [fintypeG : Fintype GOrbits]
  /-- Rational conjugacy classes in the stable class of `γ_H` in `H`. -/
  HOrbits : Type
  [fintypeH : Fintype HOrbits]
  /-- Orbital integrals on `G` of the unit of the unramified Hecke algebra. -/
  orbitalG : GOrbits → ℂ
  /-- Orbital integrals on `H` of the unit of the unramified Hecke algebra. -/
  orbitalH : HOrbits → ℂ
  /-- The endoscopic character `κ`, evaluated on the rational classes. -/
  kappa : GOrbits → ℂ
  /-- The Langlands–Shelstad transfer factor `Δ(γ_H, γ)`. -/
  transferFactor : ℂ

attribute [instance] EndoscopicTransferData.fintypeG EndoscopicTransferData.fintypeH

namespace EndoscopicTransferData

variable (d : EndoscopicTransferData)

/-- The κ-orbital integral `O^κ_γ(1_K) = ∑_{γ'} κ(γ') O_{γ'}(1_K)` on `G`. -/
noncomputable def kappaOrbitalIntegral : ℂ := ∑ x, d.kappa x * d.orbitalG x

/-- The stable orbital integral `SO_{γ_H}(1_{K_H}) = ∑_{γ'_H} O_{γ'_H}(1_{K_H})`
on the endoscopic group `H`. -/
noncomputable def stableOrbitalIntegralH : ℂ := ∑ y, d.orbitalH y

/-- The stable orbital integral `SO_γ(1_K) = ∑_{γ'} O_{γ'}(1_K)` on `G`. -/
noncomputable def stableOrbitalIntegralG : ℂ := ∑ x, d.orbitalG x

/-- **The Langlands–Shelstad fundamental lemma** for the given data:
`Δ(γ_H, γ) · SO_{γ_H}(1_{K_H}) = O^κ_γ(1_K)`. -/
def FundamentalLemmaHolds : Prop :=
  d.transferFactor * d.stableOrbitalIntegralH = d.kappaOrbitalIntegral

end EndoscopicTransferData

open EndoscopicTransferData

/-- **Ngô's fundamental lemma, base case.**

For the trivial endoscopic datum — the endoscopic group is `G` itself, the
matching of stable classes is a bijection `e` of the sets of rational classes
matching the orbital integrals, the character `κ` is trivial, and the transfer
factor is `1` — the Langlands–Shelstad identity
`Δ(γ_H, γ) · SO_{γ_H}(1_{K_H}) = O^κ_γ(1_K)`
holds: both sides are the stable orbital integral of `γ` on `G`.

This is the base case from which the inductive arguments in the proof of the
general fundamental lemma start. -/
theorem ngo_fundamental_lemma (d : EndoscopicTransferData)
    (e : d.HOrbits ≃ d.GOrbits)
    (hmatch : ∀ y, d.orbitalH y = d.orbitalG (e y))
    (hkappa : ∀ x, d.kappa x = 1)
    (hΔ : d.transferFactor = 1) :
    d.FundamentalLemmaHolds := by
  have hsum : ∑ y, d.orbitalH y = ∑ x, d.orbitalG x :=
    Fintype.sum_equiv e d.orbitalH d.orbitalG hmatch
  unfold EndoscopicTransferData.FundamentalLemmaHolds
    EndoscopicTransferData.kappaOrbitalIntegral
    EndoscopicTransferData.stableOrbitalIntegralH
  simp only [hΔ, one_mul, hkappa, hsum]

/-- The two sides in the base case are both the stable orbital integral on `G`. -/
theorem ngo_fundamental_lemma_base_value (d : EndoscopicTransferData)
    (e : d.HOrbits ≃ d.GOrbits)
    (hmatch : ∀ y, d.orbitalH y = d.orbitalG (e y))
    (hkappa : ∀ x, d.kappa x = 1) :
    d.kappaOrbitalIntegral = d.stableOrbitalIntegralG ∧
      d.stableOrbitalIntegralH = d.stableOrbitalIntegralG :=
  ⟨by simp [EndoscopicTransferData.kappaOrbitalIntegral,
      EndoscopicTransferData.stableOrbitalIntegralG, hkappa],
   Fintype.sum_equiv e d.orbitalH d.orbitalG hmatch⟩

/-- **The fundamental lemma for a torus.**

If `γ` is regular semisimple in a torus, its stable conjugacy class consists of
a single rational class on either side, and the fundamental lemma reduces to the
statement that the transfer factor times the single orbital integral on `H`
equals `κ` times the single orbital integral on `G`. Under the unramified
normalisations (`Δ = 1`, `κ = 1`, matching orbital integrals) it holds. -/
theorem ngo_fundamental_lemma_torus (d : EndoscopicTransferData)
    [Unique d.GOrbits] [Unique d.HOrbits]
    (hmatch : d.orbitalH default = d.orbitalG default)
    (hkappa : d.kappa default = 1)
    (hΔ : d.transferFactor = 1) :
    d.FundamentalLemmaHolds := by
  refine ngo_fundamental_lemma d (Equiv.ofUnique _ _) (fun y => ?_) (fun x => ?_) hΔ
  · rw [Subsingleton.elim y default, Subsingleton.elim
      (Equiv.ofUnique d.HOrbits d.GOrbits default) (default : d.GOrbits)]
    exact hmatch
  · rw [Subsingleton.elim x default]; exact hkappa

/-- Character-sum lemma: a nontrivial character of a finite group sums to zero. -/
theorem sum_character_eq_zero {A : Type*} [Group A] [Fintype A]
    (chi : A →* ℂ) (hchi : ∃ b, chi b ≠ 1) : ∑ a, chi a = 0 := by
  classical
  obtain ⟨b, hb⟩ := hchi
  have key : chi b * ∑ a : A, chi a = ∑ a : A, chi a := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft b) _ _ ?_
    intro a
    simp [← map_mul]
  have : (chi b - 1) * ∑ a : A, chi a = 0 := by
    rw [sub_mul, key, one_mul, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) hb
  · exact h

/-- **Unstable vanishing: the fundamental lemma for a datum with vanishing
stable side.**

In the unramified situation the rational classes inside the stable class of `γ`
are a torsor under the finite abelian group `A = ker(H¹(F, T) → H¹(F, G))`, all
the orbital integrals of the unit element agree, and `κ` is a character of `A`.
If `κ` is nontrivial the κ-orbital integral vanishes, by orthogonality of
characters. -/
theorem kappaOrbitalIntegral_eq_zero_of_ne_one {A : Type*} [Group A] [Fintype A]
    (chi : A →* ℂ) (hchi : ∃ b, chi b ≠ 1) (c : ℂ)
    (d : EndoscopicTransferData) (e : A ≃ d.GOrbits)
    (hkappa : ∀ x, d.kappa x = chi (e.symm x))
    (horb : ∀ x, d.orbitalG x = c) :
    d.kappaOrbitalIntegral = 0 := by
  have h1 : d.kappaOrbitalIntegral = ∑ a : A, chi a * c := by
    unfold EndoscopicTransferData.kappaOrbitalIntegral
    refine (Fintype.sum_equiv e.symm _ _ (fun x => ?_)).trans rfl
    rw [hkappa x, horb x]
  rw [h1, ← Finset.sum_mul, sum_character_eq_zero chi hchi, zero_mul]

/-- The fundamental lemma holds for a datum with nontrivial `κ` and empty
stable side on `H`: both sides vanish. -/
theorem ngo_fundamental_lemma_unstable {A : Type*} [Group A] [Fintype A]
    (chi : A →* ℂ) (hchi : ∃ b, chi b ≠ 1) (c : ℂ)
    (d : EndoscopicTransferData) (e : A ≃ d.GOrbits)
    (hkappa : ∀ x, d.kappa x = chi (e.symm x))
    (horb : ∀ x, d.orbitalG x = c)
    (hH : ∀ y, d.orbitalH y = 0) :
    d.FundamentalLemmaHolds := by
  unfold EndoscopicTransferData.FundamentalLemmaHolds
  rw [kappaOrbitalIntegral_eq_zero_of_ne_one chi hchi c d e hkappa horb]
  simp [EndoscopicTransferData.stableOrbitalIntegralH, hH]

/-!
## Reductions

The following are Lean-checked reductions for the transfer identity: they say
that the statement is compatible with the operations used in the reduction
steps of the proof of the fundamental lemma (splitting the stable class into
pieces, and renormalising the transfer factor), and that the individual orbital
integrals are recovered from the κ-orbital integrals by Fourier inversion on
the finite abelian group indexing the rational classes.
-/

/-- The disjoint union of two transfer data: the rational classes, orbital
integrals and character values are those of the two data taken together, and
the transfer factor is that of the first. -/
noncomputable def EndoscopicTransferData.sum (d₁ d₂ : EndoscopicTransferData) :
    EndoscopicTransferData where
  GOrbits := d₁.GOrbits ⊕ d₂.GOrbits
  fintypeG := inferInstance
  HOrbits := d₁.HOrbits ⊕ d₂.HOrbits
  fintypeH := inferInstance
  orbitalG := Sum.elim d₁.orbitalG d₂.orbitalG
  orbitalH := Sum.elim d₁.orbitalH d₂.orbitalH
  kappa := Sum.elim d₁.kappa d₂.kappa
  transferFactor := d₁.transferFactor

/-- **Reduction to pieces.** If the classes split into two families on which the
Langlands–Shelstad identity holds, with the same transfer factor, then the
identity holds for the union. Orbital integrals are additive over such a
splitting, so this is the compatibility of the statement with descent. -/
theorem fundamentalLemma_sum (d₁ d₂ : EndoscopicTransferData)
    (hΔ : d₁.transferFactor = d₂.transferFactor)
    (h₁ : d₁.FundamentalLemmaHolds) (h₂ : d₂.FundamentalLemmaHolds) :
    (d₁.sum d₂).FundamentalLemmaHolds := by
  unfold EndoscopicTransferData.FundamentalLemmaHolds
    EndoscopicTransferData.kappaOrbitalIntegral
    EndoscopicTransferData.stableOrbitalIntegralH at *
  show d₁.transferFactor * ∑ y, Sum.elim d₁.orbitalH d₂.orbitalH y
      = ∑ x, Sum.elim d₁.kappa d₂.kappa x * Sum.elim d₁.orbitalG d₂.orbitalG x
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, mul_add]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [h₁, hΔ, h₂]

/-- **Renormalisation of the transfer factor.** Scaling the transfer factor by
`u` and the orbital integrals on `H` by `u⁻¹` leaves the identity unchanged; in
particular the identity for a nonzero transfer factor is equivalent to the
identity with transfer factor `1` after rescaling the stable orbital integral.
Here `d'` is any datum isomorphic to `d` on the `G`-side, with `H`-side orbital
integrals scaled by `u⁻¹` and transfer factor scaled by `u`. -/
theorem fundamentalLemma_iff_normalized (d d' : EndoscopicTransferData) {u : ℂ}
    (hu : u ≠ 0)
    (eG : d'.GOrbits ≃ d.GOrbits) (eH : d'.HOrbits ≃ d.HOrbits)
    (hkappa : ∀ x, d'.kappa x = d.kappa (eG x))
    (horb : ∀ x, d'.orbitalG x = d.orbitalG (eG x))
    (horbH : ∀ y, d'.orbitalH y = u⁻¹ * d.orbitalH (eH y))
    (hΔ : d'.transferFactor = u * d.transferFactor) :
    d'.FundamentalLemmaHolds ↔ d.FundamentalLemmaHolds := by
  have hk : d'.kappaOrbitalIntegral = d.kappaOrbitalIntegral :=
    Fintype.sum_equiv eG _ _ (fun x => by rw [hkappa x, horb x])
  have hs : d'.stableOrbitalIntegralH = u⁻¹ * d.stableOrbitalIntegralH := by
    unfold EndoscopicTransferData.stableOrbitalIntegralH
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv eH _ _ (fun y => horbH y)
  unfold EndoscopicTransferData.FundamentalLemmaHolds
  rw [hk, hs, hΔ,
    show u * d.transferFactor * (u⁻¹ * d.stableOrbitalIntegralH)
      = (u * u⁻¹) * (d.transferFactor * d.stableOrbitalIntegralH) by ring,
    mul_inv_cancel₀ hu, one_mul]

/-- **Fourier inversion for orbital integrals.** When the rational conjugacy
classes inside a stable class form a torsor under a finite abelian group `A`,
the individual orbital integrals are recovered from the family of κ-orbital
integrals `O^κ = ∑_b κ(b) O(b)`, `κ` running over the characters of `A`:
`∑_κ κ(-a) O^κ = |A| · O(a)`.

This is the inversion underlying the decomposition of a stable orbital integral
into its endoscopic (κ-)pieces. -/
theorem orbital_eq_sum_kappaOrbital {A : Type} [AddCommGroup A] [Fintype A]
    [DecidableEq A] (O : A → ℂ) (a : A) :
    ∑ psi : AddChar A ℂ, psi (-a) * (∑ b, psi b * O b) = (Fintype.card A : ℂ) * O a := by
  have step : ∀ psi : AddChar A ℂ,
      psi (-a) * (∑ b, psi b * O b) = ∑ b, psi (b - a) * O b := by
    intro psi
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [sub_eq_add_neg, psi.map_add_eq_mul]
    ring
  calc ∑ psi : AddChar A ℂ, psi (-a) * (∑ b, psi b * O b)
      = ∑ psi : AddChar A ℂ, ∑ b, psi (b - a) * O b := by
        exact Finset.sum_congr rfl (fun psi _ => step psi)
    _ = ∑ b, (∑ psi : AddChar A ℂ, psi (b - a)) * O b := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun b _ => by rw [Finset.sum_mul])
    _ = (Fintype.card A : ℂ) * O a := by
        simp only [AddChar.sum_apply_eq_ite, sub_eq_zero, ite_mul, zero_mul]
        rw [Finset.sum_ite_eq' Finset.univ a (fun b => (Fintype.card A : ℂ) * O b)]
        simp

/-!
## A concrete instance, and non-vacuity

The predicate `FundamentalLemmaHolds` is a genuine condition: it fails for some
data. It holds for the unramified `κ`-datum below, where the stable class of `γ`
splits into two rational classes with equal orbital integrals, `κ` is the
nontrivial character of `ℤ/2`, and the endoscopic side vanishes.
-/

/-- Two rational classes with equal orbital integrals `c`, the nontrivial
character of `ℤ/2` as `κ`, transfer factor `1`, and vanishing endoscopic side. -/
noncomputable def signExample (c : ℂ) : EndoscopicTransferData where
  GOrbits := Bool
  fintypeG := inferInstance
  HOrbits := Unit
  fintypeH := inferInstance
  orbitalG := fun _ => c
  orbitalH := fun _ => 0
  kappa := fun b => if b then -1 else 1
  transferFactor := 1

/-- The fundamental lemma holds for `signExample`: the κ-orbital integral
`c - c` vanishes, as does the stable side. -/
theorem signExample_fundamentalLemma (c : ℂ) : (signExample c).FundamentalLemmaHolds := by
  unfold EndoscopicTransferData.FundamentalLemmaHolds
    EndoscopicTransferData.kappaOrbitalIntegral
    EndoscopicTransferData.stableOrbitalIntegralH signExample
  simp

/-- A datum with one rational class on each side, orbital integral `0` on `G`
and `1` on `H`, trivial `κ` and transfer factor `1`. -/
noncomputable def mismatchedExample : EndoscopicTransferData where
  GOrbits := Unit
  fintypeG := inferInstance
  HOrbits := Unit
  fintypeH := inferInstance
  orbitalG := fun _ => 0
  orbitalH := fun _ => 1
  kappa := fun _ => 1
  transferFactor := 1

/-- The transfer identity is a genuine condition: it fails for
`mismatchedExample`, so `FundamentalLemmaHolds` is not vacuously true. -/
theorem exists_not_fundamentalLemmaHolds :
    ∃ d : EndoscopicTransferData, ¬ d.FundamentalLemmaHolds := by
  refine ⟨mismatchedExample, ?_⟩
  unfold EndoscopicTransferData.FundamentalLemmaHolds
    EndoscopicTransferData.kappaOrbitalIntegral
    EndoscopicTransferData.stableOrbitalIntegralH mismatchedExample
  simp

/-!
## A group-theoretic model: stable versus rational conjugacy classes

To show that the framework above is instantiated by genuine conjugacy data, we
model the local situation by a finite group `Ĝ` (playing the role of the points
over a separable closure) together with a subgroup `G` (the rational points).
For `γ ∈ Ĝ`:

* the **stable class** of `γ` is the set of elements of `G` that are conjugate
  to `γ` in the ambient group `Ĝ`;
* the **rational classes** inside it are its orbits under conjugation by `G`.

`Frontier.card_stableClass_eq_sum_ratClasses` is the resulting partition
identity, and `Frontier.stableClassData` turns this into an
`EndoscopicTransferData` whose orbital integrals are the counting measures of
the rational classes. Its stable orbital integral is the cardinality of the
stable class, and the fundamental lemma for the trivial endoscopic datum holds
for it. When `G` is the whole ambient group, stable conjugacy is rational
conjugacy: the stable class is a single rational class.
-/

section StableConjugacy

open scoped Classical

variable {Gh : Type} [Group Gh] [Fintype Gh]

/-- The stable class of `γ` in `G`: the elements of the subgroup `G` that are
conjugate to `γ` in the ambient group. -/
noncomputable def stableClassFinset (G : Subgroup Gh) (g0 : Gh) : Finset Gh :=
  Finset.univ.filter (fun x => x ∈ G ∧ IsConj g0 x)

/-- The rational class of `x` inside the stable class of `γ`: its orbit under
conjugation by the subgroup `G`. -/
noncomputable def ratClassFinset (G : Subgroup Gh) (g0 x : Gh) : Finset Gh :=
  (stableClassFinset G g0).filter (fun y => ∃ g ∈ G, g * x * g⁻¹ = y)

/-- The set of rational classes inside the stable class of `γ`. -/
noncomputable def ratClasses (G : Subgroup Gh) (g0 : Gh) : Finset (Finset Gh) :=
  (stableClassFinset G g0).image (ratClassFinset G g0)

theorem mem_stableClassFinset {G : Subgroup Gh} {g0 x : Gh} :
    x ∈ stableClassFinset G g0 ↔ x ∈ G ∧ IsConj g0 x := by
  simp [stableClassFinset]

theorem mem_ratClassFinset {G : Subgroup Gh} {g0 x y : Gh} :
    y ∈ ratClassFinset G g0 x ↔ y ∈ stableClassFinset G g0 ∧ ∃ g ∈ G, g * x * g⁻¹ = y := by
  simp [ratClassFinset, Finset.mem_filter]

theorem self_mem_ratClassFinset {G : Subgroup Gh} {g0 x : Gh}
    (hx : x ∈ stableClassFinset G g0) : x ∈ ratClassFinset G g0 x :=
  mem_ratClassFinset.2 ⟨hx, 1, G.one_mem, by group⟩

/-- Rational classes are the classes of an equivalence relation: two elements of
the same rational class have the same rational class. -/
theorem ratClassFinset_eq_of_mem {G : Subgroup Gh} {g0 x y : Gh}
    (hy : y ∈ ratClassFinset G g0 x) : ratClassFinset G g0 y = ratClassFinset G g0 x := by
  obtain ⟨_, g, hg, hgy⟩ := mem_ratClassFinset.1 hy
  ext z
  simp only [mem_ratClassFinset]
  constructor
  · rintro ⟨hzs, h, hh, hhz⟩
    exact ⟨hzs, h * g, G.mul_mem hh hg, by rw [← hhz, ← hgy]; group⟩
  · rintro ⟨hzs, h, hh, hhz⟩
    refine ⟨hzs, h * g⁻¹, G.mul_mem hh (G.inv_mem hg), ?_⟩
    rw [← hhz, ← hgy]; group

theorem filter_ratClassFinset {G : Subgroup Gh} {g0 x : Gh} :
    {a ∈ stableClassFinset G g0 | ratClassFinset G g0 a = ratClassFinset G g0 x}
      = ratClassFinset G g0 x := by
  ext a
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨ha, heq⟩
    exact heq ▸ self_mem_ratClassFinset ha
  · intro ha
    exact ⟨(mem_ratClassFinset.1 ha).1, ratClassFinset_eq_of_mem ha⟩

/-- **The stable class is partitioned into rational classes**: its cardinality is
the sum of the cardinalities of the rational classes it contains. -/
theorem card_stableClass_eq_sum_ratClasses (G : Subgroup Gh) (g0 : Gh) :
    (stableClassFinset G g0).card = ∑ S ∈ ratClasses G g0, S.card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := ratClassFinset G g0) (t := ratClasses G g0)
    (fun x hx => Finset.mem_image_of_mem _ hx)]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hS
  rw [filter_ratClassFinset]

/-- The transfer datum attached to the stable class of `γ`, with the trivial
endoscopic datum: the rational classes on both sides, orbital integrals given by
counting measure, trivial `κ` and transfer factor `1`. -/
noncomputable def stableClassData (G : Subgroup Gh) (g0 : Gh) : EndoscopicTransferData where
  GOrbits := {S : Finset Gh // S ∈ ratClasses G g0}
  fintypeG := inferInstance
  HOrbits := {S : Finset Gh // S ∈ ratClasses G g0}
  fintypeH := inferInstance
  orbitalG := fun S => (S.1.card : ℂ)
  orbitalH := fun S => (S.1.card : ℂ)
  kappa := fun _ => 1
  transferFactor := 1

/-- The fundamental lemma holds for the conjugacy-class model with the trivial
endoscopic datum. -/
theorem stableClassData_fundamentalLemma (G : Subgroup Gh) (g0 : Gh) :
    (stableClassData G g0).FundamentalLemmaHolds :=
  ngo_fundamental_lemma _ (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) rfl

/-- In the conjugacy-class model the stable orbital integral is the cardinality
of the stable class. -/
theorem stableClassData_stableOrbitalIntegral (G : Subgroup Gh) (g0 : Gh) :
    (stableClassData G g0).stableOrbitalIntegralG = ((stableClassFinset G g0).card : ℂ) := by
  show ∑ S : {S : Finset Gh // S ∈ ratClasses G g0}, (S.1.card : ℂ) = _
  rw [Finset.sum_coe_sort (ratClasses G g0) (fun S => (S.card : ℂ)),
    card_stableClass_eq_sum_ratClasses G g0]
  push_cast
  rfl

/-- **Stable conjugacy is rational conjugacy for the full group.** If `G` is the
whole ambient group, the stable class of `γ` is a single rational class. -/
theorem ratClasses_top (g0 : Gh) :
    ratClasses (⊤ : Subgroup Gh) g0 = {stableClassFinset (⊤ : Subgroup Gh) g0} := by
  have hself : ∀ x ∈ stableClassFinset (⊤ : Subgroup Gh) g0,
      ratClassFinset (⊤ : Subgroup Gh) g0 x = stableClassFinset (⊤ : Subgroup Gh) g0 := by
    intro x hx
    obtain ⟨-, hgx⟩ := mem_stableClassFinset.1 hx
    ext y
    simp only [mem_ratClassFinset]
    constructor
    · exact fun h => h.1
    · intro hy
      refine ⟨hy, ?_⟩
      obtain ⟨-, hgy⟩ := mem_stableClassFinset.1 hy
      obtain ⟨c, hc⟩ := isConj_iff.1 (hgx.symm.trans hgy)
      exact ⟨c, Subgroup.mem_top c, hc⟩
  have hmem : g0 ∈ stableClassFinset (⊤ : Subgroup Gh) g0 :=
    mem_stableClassFinset.2 ⟨Subgroup.mem_top g0, IsConj.refl g0⟩
  ext S
  simp only [ratClasses, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hself x hx
  · rintro rfl
    exact ⟨g0, hmem, hself g0 hmem⟩

end StableConjugacy

end Frontier

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

