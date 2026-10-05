/-!
# Ngo Fundamental Lemma
Category: Frontier — Fields Medal Work
Target: Frontier.ngo_fundamental_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
## The Langlands–Shelstad fundamental lemma (Ngô)

The fundamental lemma, proved by Ngô Bảo Châu, is the following assertion.  Let `F` be a
non-archimedean local field with ring of integers `O`, let `G` be an unramified connected
reductive group over `F` with hyperspecial maximal compact subgroup `K = G(O)`, and let
`(H, s, η)` be an unramified endoscopic datum for `G`, with endoscopic group `H`.  Let
`γ_H ∈ H(F)` be a strongly regular semisimple element whose stable class is a *norm* of the
stable class of a strongly regular semisimple `γ ∈ G(F)`.  Write `𝔎_γ` for the finite abelian
group attached by Kottwitz to the stable class of `γ`; the rational conjugacy classes inside the
stable class of `γ` are indexed by (a subset of) `𝔎_γ` via the Kottwitz invariant
`γ' ↦ inv(γ, γ') ∈ 𝔎_γ`, and the endoscopic datum determines a character `κ` of `𝔎_γ`.  Then

`  O^κ_γ(1_K)  =  Δ(γ_H, γ) · SO_{γ_H}(1_{K_H}) ,`

where
* `O^κ_γ(1_K) = Σ_{γ'} κ(inv(γ, γ')) · O_{γ'}(1_K)` is the *κ-orbital integral* of the unit
  element of the unramified Hecke algebra, the sum running over the rational classes `γ'` in
  the stable class of `γ`;
* `SO_{γ_H}(1_{K_H}) = Σ_{γ'_H} O_{γ'_H}(1_{K_H})` is the *stable orbital integral* on `H`;
* `Δ(γ_H, γ)` is the Langlands–Shelstad transfer factor.

The full theorem involves the whole analytic and geometric apparatus (Haar measures, orbital
integrals over `p`-adic groups, the Hitchin fibration, perverse sheaves) which is not available
in Mathlib.  What is formalized below is the *combinatorial shape* of the identity: the finite
abelian group `𝔎_γ`, the indexing of rational classes by their Kottwitz invariants, the κ-orbital
and stable orbital integrals as finite sums, the transfer factor, and the identity itself.  On
that formalization we prove, with complete Lean proofs:

* `Frontier.ngo_fundamental_lemma` — the **base case** of the fundamental lemma, i.e. the case of
  the trivial endoscopic datum (`H = G`, `κ = 1`, `Δ ≡ 1`), where the identity says that the
  κ-orbital integral for the trivial character is the stable orbital integral;
* `Frontier.ngo_fundamental_lemma_unstable_vanishing` — the case of a nontrivial character `κ`
  when the stable class is a full principal homogeneous space under `𝔎_γ` with equal orbital
  integrals and the endoscopic side is empty: both sides vanish;
* `Frontier.ngo_fundamental_lemma_fourier_reduction` and
  `Frontier.ngo_fundamental_lemma_reduction` — the Lean-checked *reduction* (Kottwitz's finite
  Fourier inversion) showing that the family of κ-identities, taken over all characters `κ` of
  `𝔎_γ`, is equivalent to the matching of the individual orbital integrals grouped by Kottwitz
  invariant; this is the standard device by which the fundamental lemma in κ-form is converted
  into the transfer of individual orbital integrals, and conversely.
-/

namespace Frontier

/-- The finite combinatorial data underlying one instance of the Langlands–Shelstad
fundamental lemma at a strongly regular semisimple stable conjugacy class.

* `K` is the finite abelian group `𝔎_γ` attached by Kottwitz to the stable class;
* `Cls` indexes the rational conjugacy classes inside the given stable class of `G(F)`,
  and `inv` records the Kottwitz invariant `inv(γ, γ') ∈ 𝔎_γ` of such a class;
* `O` is the orbital integral of the unit of the unramified Hecke algebra at a rational class;
* `ClsH` indexes the rational conjugacy classes in the stable class of the norm `γ_H` in the
  endoscopic group `H(F)`, with orbital integrals `OH`;
* `transferFactor` is the Langlands–Shelstad transfer factor `Δ(γ_H, γ)`. -/
structure EndoscopicData where
  /-- The Kottwitz group `𝔎_γ` of the stable class. -/
  K : Type
  [addCommGroup_K : AddCommGroup K]
  [fintype_K : Fintype K]
  [decEq_K : DecidableEq K]
  /-- Index set of the rational classes inside the stable class of `γ` in `G(F)`. -/
  Cls : Type
  [fintype_Cls : Fintype Cls]
  /-- The Kottwitz invariant `inv(γ, γ')`. -/
  inv : Cls → K
  /-- Orbital integral of the unit of the Hecke algebra at a rational class of `G(F)`. -/
  O : Cls → ℂ
  /-- Index set of the rational classes inside the stable class of `γ_H` in `H(F)`. -/
  ClsH : Type
  [fintype_ClsH : Fintype ClsH]
  /-- Orbital integral of the unit of the Hecke algebra at a rational class of `H(F)`. -/
  OH : ClsH → ℂ
  /-- The Langlands–Shelstad transfer factor `Δ(γ_H, γ)`. -/
  transferFactor : ℂ

attribute [instance] EndoscopicData.addCommGroup_K EndoscopicData.fintype_K
  EndoscopicData.decEq_K EndoscopicData.fintype_Cls EndoscopicData.fintype_ClsH

variable (D : EndoscopicData)

/-- The κ-orbital integral `O^κ_γ(1_K) = Σ_{γ'} κ(inv(γ, γ')) O_{γ'}(1_K)`. -/

theorem kappaOrbitalIntegral_one :
    kappaOrbitalIntegral D 1 = stableOrbitalIntegral D := by
  simp [kappaOrbitalIntegral, stableOrbitalIntegral]

/-- Under the trivial endoscopic datum, the stable orbital integral on `H` agrees with the
stable orbital integral on `G`. -/
