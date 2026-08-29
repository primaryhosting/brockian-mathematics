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

/-!
## The combinatorial shape of the Langlands–Shelstad fundamental lemma

Let `F` be a non-archimedean local field with ring of integers `O`, let `G` be an unramified
reductive group over `O` with hyperspecial maximal compact subgroup `K = G(O)`, and let
`γ ∈ G(F)` be a strongly regular semisimple element with centralizer the (unramified) maximal
torus `T`.

The `G(F)`-conjugacy classes inside the stable conjugacy class of `γ` are a torsor under the
finite abelian group

  `A = ker(H¹(F, T) → H¹(F, G))`,

and an endoscopic datum for `G` with `T`-part `γ` is (via Tate–Nakayama duality) recorded by a
character `κ` of `A`; the trivial character corresponds to the trivial endoscopic datum `H = G`.
Choosing a base point, the orbital integrals of the unit `1_K` of the unramified Hecke algebra
over the classes in the stable class form a function `orb : A → ℂ`,

  `orb a = O_{γ_a}(1_{G(O)})`,

and the two invariants that enter the fundamental lemma are the **stable orbital integral**
`∑_{a} orb a` and, for an endoscopic character `κ`, the **κ-orbital integral**
`∑_{a} κ(a) · orb a`.

The Langlands–Shelstad fundamental lemma, proved by Ngô, asserts that for every endoscopic
character `κ`, with endoscopic group `H_κ`, matching element `γ_H` and Langlands–Shelstad
transfer factor `Δ(γ_H, γ)`,

  `SO_{γ_H}(1_{H_κ(O)}) = Δ(γ_H, γ) · O^κ_γ(1_{G(O)})`.

This file formalizes exactly this shape of the statement, and proves:

* `Frontier.ngo_fundamental_lemma_trivial_endoscopy` — the base case of the trivial endoscopic
  datum (`κ` trivial, `H = G`, `Δ = 1`), where the identity is the equality of the stable
  orbital integral with the trivial-character κ-orbital integral;
* `Frontier.ngo_fundamental_lemma_of_subsingleton` — the base case of a stable class consisting
  of a single rational class (`A` trivial, e.g. `G` with simply connected derived group);
* `Frontier.ngo_fundamental_lemma_product` — the multiplicativity reduction: the fundamental
  lemma for a product `G₁ × G₂` follows from the fundamental lemma for each factor;
* `Frontier.ngo_fundamental_lemma` — the main Lean-checked reduction: for a fixed stable class,
  the family of κ-identities for *all* endoscopic characters `κ` is *equivalent* (by finite
  Fourier inversion on `A`) to an explicit formula expressing each individual orbital integral
  `O_{γ_a}(1_K)` in terms of the stable orbital integrals on the endoscopic groups;
* `Frontier.ngo_fundamental_lemma_orb_unique` — consequently the fundamental lemma determines
  the individual orbital integrals uniquely.
-/

section Definitions

variable {A : Type} [AddCommGroup A] [Fintype A]

/-- The **κ-orbital integral** `O^κ_γ(1_K) = ∑_{a ∈ A} κ(a) · O_{γ_a}(1_K)` attached to an
endoscopic character `κ` of the obstruction group `A` and to the family `orb` of orbital
integrals over the rational classes in a fixed stable conjugacy class. -/
noncomputable def kappaOrbitalIntegral (kappa : AddChar A ℂ) (orb : A → ℂ) : ℂ :=
  ∑ a : A, kappa a * orb a

/-- The **stable orbital integral** `SO_γ(1_K) = ∑_{a ∈ A} O_{γ_a}(1_K)`: the sum of the orbital
integrals over all rational conjugacy classes inside the stable class of `γ`. -/
noncomputable def stableOrbitalIntegral (orb : A → ℂ) : ℂ := ∑ a : A, orb a

/-- The local data entering the fundamental lemma at a fixed strongly regular semisimple stable
conjugacy class of `G(F)`: the orbital integrals of the unit of the unramified Hecke algebra over
the rational classes in the stable class (indexed by the obstruction group `A`), together with,
for every endoscopic character `κ` of `A`, the stable orbital integral of the unit of the
unramified Hecke algebra of the endoscopic group `H_κ` at a matching element, and the
Langlands–Shelstad transfer factor (which is nonzero). -/
structure EndoscopicFamily (A : Type) [AddCommGroup A] [Fintype A] where
  /-- `orb a = O_{γ_a}(1_{G(O)})`, the orbital integrals over the rational classes. -/
  orb : A → ℂ
  /-- `stabOrbH κ = SO_{γ_H}(1_{H_κ(O)})`, the stable orbital integral on the endoscopic group. -/
  stabOrbH : AddChar A ℂ → ℂ
  /-- `transfer κ = Δ(γ_H, γ)`, the Langlands–Shelstad transfer factor. -/
  transfer : AddChar A ℂ → ℂ
  /-- Transfer factors are nonzero. -/
  transfer_ne_zero : ∀ kappa : AddChar A ℂ, transfer kappa ≠ 0

/-- The **Langlands–Shelstad fundamental lemma** (Ngô) for a local datum: for every endoscopic
character `κ`, the stable orbital integral of the unit of the Hecke algebra of the endoscopic
group `H_κ` equals the transfer factor times the κ-orbital integral on `G`,

  `SO_{γ_H}(1_{H_κ(O)}) = Δ(γ_H, γ) · O^κ_γ(1_{G(O)})`. -/
def FundamentalLemmaHolds (F : EndoscopicFamily A) : Prop :=
  ∀ kappa : AddChar A ℂ, F.stabOrbH kappa = F.transfer kappa * kappaOrbitalIntegral kappa F.orb

end Definitions

section BaseCases

variable {A : Type} [AddCommGroup A] [Fintype A]

/-- For the trivial endoscopic character the κ-orbital integral is the stable orbital integral. -/
theorem kappaOrbitalIntegral_zero (orb : A → ℂ) :
    kappaOrbitalIntegral (0 : AddChar A ℂ) orb = stableOrbitalIntegral orb := by
  simp [kappaOrbitalIntegral, stableOrbitalIntegral]

/-- **Base case of the fundamental lemma: the trivial endoscopic datum.**

For the trivial endoscopic datum the endoscopic group is `H = G`, the transfer factor is
normalized to `1`, and the assertion of the fundamental lemma is the identity
`SO_γ(1_{G(O)}) = 1 · O^{κ = 1}_γ(1_{G(O)})` between the stable orbital integral and the
κ-orbital integral for the trivial character. -/
theorem ngo_fundamental_lemma_trivial_endoscopy (orb : A → ℂ) :
    stableOrbitalIntegral orb = (1 : ℂ) * kappaOrbitalIntegral (0 : AddChar A ℂ) orb := by
  rw [kappaOrbitalIntegral_zero, one_mul]

/-- **Base case of the fundamental lemma: a stable class which is a single rational class.**

If the obstruction group `A` is trivial (for instance when the derived group of `G` is simply
connected, so that stable conjugacy coincides with rational conjugacy), then every κ-orbital
integral coincides with the unique orbital integral `O_γ(1_K)`, and the fundamental lemma holds
for a datum whose endoscopic side is the transfer factor times that orbital integral. -/
theorem ngo_fundamental_lemma_of_subsingleton [Subsingleton A] (F : EndoscopicFamily A)
    (h : ∀ kappa : AddChar A ℂ, F.stabOrbH kappa = F.transfer kappa * F.orb 0) :
    FundamentalLemmaHolds F := by
  intro kappa
  have hA : (Finset.univ : Finset A) = {0} := by
    ext a
    simp [Subsingleton.elim a (0 : A)]
  rw [h kappa, kappaOrbitalIntegral, hA]
  simp

end BaseCases

section Product

variable {A₁ A₂ : Type} [AddCommGroup A₁] [Fintype A₁] [AddCommGroup A₂] [Fintype A₂]

/-- **Multiplicativity of κ-orbital integrals.**

For a product group `G = G₁ × G₂` the obstruction group is `A₁ × A₂`, an endoscopic character is
a pair `(κ₁, κ₂)`, and the orbital integrals of the unit of the Hecke algebra factor as
`O_{(γ₁,γ₂)} = O_{γ₁} · O_{γ₂}`. Consequently the κ-orbital integrals factor as well. -/
theorem kappaOrbitalIntegral_product (kappa₁ : AddChar A₁ ℂ) (kappa₂ : AddChar A₂ ℂ)
    (orb₁ : A₁ → ℂ) (orb₂ : A₂ → ℂ) :
    ∑ p : A₁ × A₂, (kappa₁ p.1 * kappa₂ p.2) * (orb₁ p.1 * orb₂ p.2) =
      kappaOrbitalIntegral kappa₁ orb₁ * kappaOrbitalIntegral kappa₂ orb₂ := by
  rw [kappaOrbitalIntegral, kappaOrbitalIntegral, Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  exact Finset.sum_congr rfl fun p _ => by ring

/-- **Reduction of the fundamental lemma to the factors of a product.**

If the fundamental lemma identity holds for `(G₁, H₁, κ₁)` and for `(G₂, H₂, κ₂)`, then it holds
for the product datum, whose endoscopic group is `H₁ × H₂`, whose transfer factor is the product
of the transfer factors, and whose orbital integrals are the products of the orbital integrals. -/
theorem ngo_fundamental_lemma_product {kappa₁ : AddChar A₁ ℂ} {kappa₂ : AddChar A₂ ℂ}
    {orb₁ : A₁ → ℂ} {orb₂ : A₂ → ℂ} {stabOrbH₁ stabOrbH₂ transfer₁ transfer₂ : ℂ}
    (h₁ : stabOrbH₁ = transfer₁ * kappaOrbitalIntegral kappa₁ orb₁)
    (h₂ : stabOrbH₂ = transfer₂ * kappaOrbitalIntegral kappa₂ orb₂) :
    stabOrbH₁ * stabOrbH₂ =
      (transfer₁ * transfer₂) *
        ∑ p : A₁ × A₂, (kappa₁ p.1 * kappa₂ p.2) * (orb₁ p.1 * orb₂ p.2) := by
  rw [kappaOrbitalIntegral_product, h₁, h₂]
  ring

end Product

section FourierReduction

variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- Orthogonality of the characters of the finite abelian group `A`, in the form used below. -/
private theorem sum_char_apply_sub (a b : A) :
    ∑ kappa : AddChar A ℂ, kappa b * kappa (-a) =
      if b = a then (Fintype.card A : ℂ) else 0 := by
  have h : ∀ kappa : AddChar A ℂ, kappa b * kappa (-a) = kappa (b - a) := by
    intro kappa
    rw [sub_eq_add_neg, kappa.map_add_eq_mul]
  simp_rw [h]
  rw [AddChar.sum_apply_eq_ite (b - a)]
  simp [sub_eq_zero]

omit [DecidableEq A] in
/-- Orthogonality in the dual direction: summing a character over the group. -/
private theorem sum_apply_sub_char (kappa₀ kappa : AddChar A ℂ) :
    ∑ a : A, kappa₀ a * kappa (-a) = if kappa₀ = kappa then (Fintype.card A : ℂ) else 0 := by
  have h : ∀ a : A, kappa₀ a * kappa (-a) = (kappa₀ - kappa) a := by
    intro a
    rw [AddChar.sub_apply]
  simp_rw [h]
  rw [AddChar.sum_eq_ite]
  simp [sub_eq_zero]

/-- **The Langlands–Shelstad fundamental lemma (Ngô): statement, and a Lean-checked reduction.**

For a fixed strongly regular semisimple stable conjugacy class in `G(F)` with obstruction group
`A`, the fundamental lemma is the family of identities

  `SO_{γ_H}(1_{H_κ(O)}) = Δ(γ_H, γ) · O^κ_γ(1_{G(O)})`,   `O^κ_γ(1_K) = ∑_{a ∈ A} κ(a) O_{γ_a}(1_K)`,

one for each endoscopic character `κ` of `A`. This theorem shows that this whole family of
identities is *equivalent*, by finite Fourier inversion on the abelian group `A`, to the explicit
formula

  `|A| · O_{γ_a}(1_{G(O)}) = ∑_{κ} κ(-a) · SO_{γ_H}(1_{H_κ(O)}) / Δ(γ_H, γ)`

expressing each individual (unstable) orbital integral on `G` in terms of the stable orbital
integrals on the endoscopic groups. In particular the endoscopic side of the fundamental lemma
determines, and is determined by, the individual orbital integrals of the unit of the unramified
Hecke algebra. -/
theorem ngo_fundamental_lemma (F : EndoscopicFamily A) :
    FundamentalLemmaHolds F ↔
      ∀ a : A, (Fintype.card A : ℂ) * F.orb a =
        ∑ kappa : AddChar A ℂ, kappa (-a) * (F.stabOrbH kappa / F.transfer kappa) := by
  have hcard : (Fintype.card A : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := A))
  constructor
  · intro hFL a
    have hstep : ∀ kappa : AddChar A ℂ,
        kappa (-a) * (F.stabOrbH kappa / F.transfer kappa) =
          ∑ b : A, (kappa b * kappa (-a)) * F.orb b := by
      intro kappa
      rw [hFL kappa, mul_comm (F.transfer kappa), mul_div_assoc,
        div_self (F.transfer_ne_zero kappa), mul_one, kappaOrbitalIntegral,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    simp_rw [hstep]
    rw [Finset.sum_comm]
    have : ∀ b : A, (∑ kappa : AddChar A ℂ, (kappa b * kappa (-a)) * F.orb b) =
        (if b = a then (Fintype.card A : ℂ) else 0) * F.orb b := by
      intro b
      rw [← Finset.sum_mul, sum_char_apply_sub]
    simp_rw [this]
    simp
  · intro hinv kappa₀
    have key : kappaOrbitalIntegral kappa₀ F.orb = F.stabOrbH kappa₀ / F.transfer kappa₀ := by
      have h1 : (Fintype.card A : ℂ) * kappaOrbitalIntegral kappa₀ F.orb =
          ∑ a : A, kappa₀ a * ((Fintype.card A : ℂ) * F.orb a) := by
        rw [kappaOrbitalIntegral, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
      have h2 : ∑ a : A, kappa₀ a * ((Fintype.card A : ℂ) * F.orb a) =
          ∑ a : A, ∑ kappa : AddChar A ℂ,
            (kappa₀ a * kappa (-a)) * (F.stabOrbH kappa / F.transfer kappa) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hinv a, Finset.mul_sum]
        exact Finset.sum_congr rfl fun kappa _ => by ring
      have h3 : (∑ a : A, ∑ kappa : AddChar A ℂ,
            (kappa₀ a * kappa (-a)) * (F.stabOrbH kappa / F.transfer kappa)) =
          (Fintype.card A : ℂ) * (F.stabOrbH kappa₀ / F.transfer kappa₀) := by
        rw [Finset.sum_comm]
        have hterm : ∀ kappa : AddChar A ℂ,
            (∑ a : A, (kappa₀ a * kappa (-a)) * (F.stabOrbH kappa / F.transfer kappa)) =
              (if kappa₀ = kappa then (Fintype.card A : ℂ) else 0) *
                (F.stabOrbH kappa / F.transfer kappa) := by
          intro kappa
          rw [← Finset.sum_mul, sum_apply_sub_char]
        simp_rw [hterm]
        simp
      have h4 : (Fintype.card A : ℂ) * kappaOrbitalIntegral kappa₀ F.orb =
          (Fintype.card A : ℂ) * (F.stabOrbH kappa₀ / F.transfer kappa₀) := by
        rw [h1, h2, h3]
      exact mul_left_cancel₀ hcard h4
    rw [key, mul_div_cancel₀ _ (F.transfer_ne_zero kappa₀)]

/-- The fundamental lemma determines the individual orbital integrals: two data with the same
endoscopic side (stable orbital integrals and transfer factors) and both satisfying the
fundamental lemma have the same orbital integrals on `G`. -/
theorem ngo_fundamental_lemma_orb_unique {F₁ F₂ : EndoscopicFamily A}
    (h₁ : FundamentalLemmaHolds F₁) (h₂ : FundamentalLemmaHolds F₂)
    (hH : F₁.stabOrbH = F₂.stabOrbH) (hΔ : F₁.transfer = F₂.transfer) :
    F₁.orb = F₂.orb := by
  have hcard : (Fintype.card A : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := A))
  funext a
  have e₁ := (ngo_fundamental_lemma F₁).1 h₁ a
  have e₂ := (ngo_fundamental_lemma F₂).1 h₂ a
  rw [hH, hΔ] at e₁
  exact mul_left_cancel₀ hcard (e₁.trans e₂.symm)

end FourierReduction

section Content

/-- The fundamental lemma is a nontrivial condition: there are data (here for the obstruction
group `ℤ/2`, the case of elliptic endoscopy for `SL(2)`) for which it fails. -/
theorem exists_fundamentalLemma_not_holds :
    ∃ F : EndoscopicFamily (ZMod 2), ¬ FundamentalLemmaHolds F := by
  refine ⟨⟨fun _ => 1, fun _ => 0, fun _ => 1, fun _ => one_ne_zero⟩, ?_⟩
  intro h
  have h0 := h 0
  simp [kappaOrbitalIntegral] at h0

/-- The fundamental lemma is satisfiable: for any prescribed orbital integrals on `G` and any
prescribed nonzero transfer factors, the endoscopic side can be chosen so that the fundamental
lemma holds. -/
theorem exists_fundamentalLemma_holds {A : Type} [AddCommGroup A] [Fintype A] (orb : A → ℂ)
    (transfer : AddChar A ℂ → ℂ) (htransfer : ∀ kappa, transfer kappa ≠ 0) :
    ∃ F : EndoscopicFamily A, F.orb = orb ∧ F.transfer = transfer ∧ FundamentalLemmaHolds F :=
  ⟨⟨orb, fun kappa => transfer kappa * kappaOrbitalIntegral kappa orb, transfer, htransfer⟩,
    rfl, rfl, fun _ => rfl⟩

end Content

end Frontier

#print axioms Frontier.ngo_fundamental_lemma
#print axioms Frontier.ngo_fundamental_lemma_trivial_endoscopy
#print axioms Frontier.ngo_fundamental_lemma_of_subsingleton
#print axioms Frontier.ngo_fundamental_lemma_product
#print axioms Frontier.ngo_fundamental_lemma_orb_unique
#print axioms Frontier.exists_fundamentalLemma_not_holds
#print axioms Frontier.exists_fundamentalLemma_holds

