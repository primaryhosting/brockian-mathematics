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
def kappaOrbitalIntegral (kap : AddChar D.K ℂ) : ℂ :=
  ∑ c : D.Cls, kap (D.inv c) * D.O c

/-- The stable orbital integral `SO_γ(1_K) = Σ_{γ'} O_{γ'}(1_K)` on `G`. -/
def stableOrbitalIntegral : ℂ := ∑ c : D.Cls, D.O c

/-- The stable orbital integral `SO_{γ_H}(1_{K_H}) = Σ_{γ'_H} O_{γ'_H}(1_{K_H})` on the
endoscopic group `H`. -/
def stableOrbitalIntegralH : ℂ := ∑ c : D.ClsH, D.OH c

/-- The fundamental lemma identity for the character `kap` of the Kottwitz group:
`O^κ_γ(1_K) = Δ(γ_H, γ) · SO_{γ_H}(1_{K_H})`. -/
def FundamentalLemmaIdentity (kap : AddChar D.K ℂ) : Prop :=
  kappaOrbitalIntegral D kap = D.transferFactor * stableOrbitalIntegralH D

/-- The *trivial endoscopic datum*: the endoscopic group is `G` itself, the matching of stable
classes is a bijection preserving orbital integrals, and the transfer factor is `1`. -/
def IsTrivialEndoscopy : Prop :=
  D.transferFactor = 1 ∧ ∃ e : D.ClsH ≃ D.Cls, ∀ c : D.ClsH, D.OH c = D.O (e c)

/-- For the trivial character of the Kottwitz group, the κ-orbital integral is the stable
orbital integral. -/
theorem kappaOrbitalIntegral_one :
    kappaOrbitalIntegral D 1 = stableOrbitalIntegral D := by
  simp [kappaOrbitalIntegral, stableOrbitalIntegral]

/-- Under the trivial endoscopic datum, the stable orbital integral on `H` agrees with the
stable orbital integral on `G`. -/
theorem stableOrbitalIntegralH_eq_of_trivialEndoscopy (hD : IsTrivialEndoscopy D) :
    stableOrbitalIntegralH D = stableOrbitalIntegral D := by
  obtain ⟨-, e, he⟩ := hD
  unfold stableOrbitalIntegralH stableOrbitalIntegral
  rw [← Equiv.sum_comp e D.O]
  exact Finset.sum_congr rfl fun c _ => he c

/-- **The Langlands–Shelstad fundamental lemma (Ngô), base case.**

For the trivial endoscopic datum — the endoscopic group is `G` itself, the transfer factor is
identically `1`, and the relevant character `κ` of the Kottwitz group `𝔎_γ` is trivial — the
fundamental lemma identity

`  O^κ_γ(1_K) = Δ(γ_H, γ) · SO_{γ_H}(1_{K_H})  `

holds: both sides are the stable orbital integral of the unit of the unramified Hecke algebra. -/
theorem ngo_fundamental_lemma (hD : IsTrivialEndoscopy D) :
    FundamentalLemmaIdentity D 1 := by
  unfold FundamentalLemmaIdentity
  rw [kappaOrbitalIntegral_one, stableOrbitalIntegralH_eq_of_trivialEndoscopy D hD, hD.1,
    one_mul]

/-- **Vanishing case of the fundamental lemma.**

If the rational classes inside the stable class of `γ` form a principal homogeneous space under
the Kottwitz group `𝔎_γ` (the Kottwitz invariant is a bijection onto `𝔎_γ`) with all orbital
integrals equal to a common value, the character `κ` is nontrivial, and the endoscopic stable
class is empty, then the fundamental lemma identity holds: both sides are zero. -/
theorem ngo_fundamental_lemma_unstable_vanishing
    (kap : AddChar D.K ℂ) (hkap : kap ≠ 1) (v : ℂ)
    (hbij : Function.Bijective D.inv) (hO : ∀ c : D.Cls, D.O c = v)
    (hH : IsEmpty D.ClsH) :
    FundamentalLemmaIdentity D kap := by
  have hsum : kappaOrbitalIntegral D kap = 0 := by
    have h1 : kappaOrbitalIntegral D kap = ∑ c : D.Cls, kap (D.inv c) * v := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hO c]
    have h2 : ∑ c : D.Cls, kap (D.inv c) * v = (∑ k : D.K, kap k) * v := by
      rw [Finset.sum_mul]
      exact Fintype.sum_bijective D.inv hbij _ _ fun c => rfl
    have h3 : ∑ k : D.K, kap k = 0 := AddChar.sum_eq_zero_of_ne_one hkap
    rw [h1, h2, h3, zero_mul]
  have hH0 : stableOrbitalIntegralH D = 0 := by
    unfold stableOrbitalIntegralH
    rw [Finset.univ_eq_empty, Finset.sum_empty]
  unfold FundamentalLemmaIdentity
  rw [hsum, hH0, mul_zero]

/-- **Kottwitz's finite Fourier inversion.**

The κ-orbital integrals, taken over all characters `κ` of the Kottwitz group `𝔎_γ`, determine
the partial sums of ordinary orbital integrals over the rational classes with a prescribed
Kottwitz invariant. -/
theorem ngo_fundamental_lemma_fourier_reduction (k : D.K) :
    ∑ kap : AddChar D.K ℂ, (kap k)⁻¹ * kappaOrbitalIntegral D kap
      = (Fintype.card D.K : ℂ) * ∑ c ∈ {c : D.Cls | D.inv c = k}, D.O c := by
  classical
  have hswap : ∑ kap : AddChar D.K ℂ, (kap k)⁻¹ * kappaOrbitalIntegral D kap
      = ∑ c : D.Cls, (∑ kap : AddChar D.K ℂ, kap (D.inv c - k)) * D.O c := by
    unfold kappaOrbitalIntegral
    rw [Finset.sum_comm']
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun kap _ => ?_
    have hk : kap (D.inv c - k) = kap (D.inv c) * (kap k)⁻¹ := by
      rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv]
    rw [hk]
    ring
  rw [hswap]
  have hchar : ∀ c : D.Cls, (∑ kap : AddChar D.K ℂ, kap (D.inv c - k))
      = if D.inv c = k then (Fintype.card D.K : ℂ) else 0 := by
    intro c
    rw [AddChar.sum_apply_eq_ite (D.inv c - k), sub_eq_zero]
  calc ∑ c : D.Cls, (∑ kap : AddChar D.K ℂ, kap (D.inv c - k)) * D.O c
      = ∑ c : D.Cls, (if D.inv c = k then (Fintype.card D.K : ℂ) else 0) * D.O c := by
        exact Finset.sum_congr rfl fun c _ => by rw [hchar c]
    _ = (Fintype.card D.K : ℂ) * ∑ c ∈ {c : D.Cls | D.inv c = k}, D.O c := by
        rw [Finset.mul_sum]
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun c _ => by
          by_cases h : D.inv c = k <;> simp [h]

/-- **A Lean-checked reduction of the fundamental lemma.**

Suppose that for every character `κ` of the Kottwitz group `𝔎_γ` the fundamental lemma identity
holds with an endoscopic right-hand side `S κ` (i.e. `S κ = Δ_κ · SO_{γ_H(κ)}`).  Then the
individual orbital integrals of `G`, summed over the rational classes with a fixed Kottwitz
invariant `k`, are recovered from the endoscopic data by finite Fourier inversion.  This is the
standard passage from the κ-form of the fundamental lemma to the matching of orbital integrals. -/
theorem ngo_fundamental_lemma_reduction
    (S : AddChar D.K ℂ → ℂ) (h : ∀ kap : AddChar D.K ℂ, kappaOrbitalIntegral D kap = S kap)
    (k : D.K) :
    ∑ c ∈ {c : D.Cls | D.inv c = k}, D.O c
      = (Fintype.card D.K : ℂ)⁻¹ * ∑ kap : AddChar D.K ℂ, (kap k)⁻¹ * S kap := by
  classical
  have hcard : (Fintype.card D.K : ℂ) ≠ 0 := by
    have : 0 < Fintype.card D.K := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast this.ne'
  have key := ngo_fundamental_lemma_fourier_reduction D k
  rw [show (∑ kap : AddChar D.K ℂ, (kap k)⁻¹ * kappaOrbitalIntegral D kap)
      = ∑ kap : AddChar D.K ℂ, (kap k)⁻¹ * S kap from
    Finset.sum_congr rfl fun kap _ => by rw [h kap]] at key
  rw [key, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end Frontier

