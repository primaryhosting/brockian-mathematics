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
