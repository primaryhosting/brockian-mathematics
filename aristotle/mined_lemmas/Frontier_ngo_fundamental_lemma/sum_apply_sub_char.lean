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
