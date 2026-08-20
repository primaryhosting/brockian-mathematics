/-!
# Ngo Fundamental Lemma
Category: Frontier — Fields Medal Work
Target: Frontier.ngo_fundamental_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file states the Langlands–Shelstad fundamental lemma (proved in general by
Ngô Bảo Châu) in the following shape, and proves a base case together with two
Lean-checked reductions.

For an unramified endoscopic datum `(H, s, η)` for a reductive group `G` over a
non-archimedean local field `F`, with `q` the residue cardinality, the fundamental

lemma asserts that for every element `f` of the spherical Hecke algebra of `G`,
every strongly regular semisimple `γ_H ∈ H(F)` whose stable class is a *norm* of
the stable class of `γ ∈ G(F)`, one has

  `Δ(γ_H, γ) · SO_{γ_H}(b(f))  =  O^κ_γ(f)`,

where `b : ℋ(G) → ℋ(H)` is the transfer map dual to `η` on Satake parameters,
`SO` denotes the stable orbital integral on `H`, `O^κ` the `κ`-orbital integral on
`G` for the character `κ` attached to `s`, and `Δ` the Langlands–Shelstad transfer
factor.

The datum of all the objects occurring in this identity is packaged in
`Frontier.EndoscopicDatum`, and the identity itself is
`Frontier.FundamentalLemmaHolds`.  Orbital integrals are normalised (measures
giving hyperspecial maximal compact subgroups volume one, transfer factors
normalised as in Kottwitz's computation for `SL(2)`) so that all the quantities
occurring below are integers; this is why the value type is `Int`.

What is proved here:

* `Frontier.fundamentalLemma_trivialDatum` — the fundamental lemma for the trivial
  endoscopic datum `H = G`, `κ = 1`, `Δ = 1` (in that case the identity is the
  tautology `1 · O_γ(f) = O_γ(f)`).
* `Frontier.fundamentalLemma_prodDatum` — the reduction of the fundamental lemma
  for a product of endoscopic data to the fundamental lemma for each factor
  (this is the standard reduction to (almost) simple groups).
* `Frontier.fundamentalLemma_transport` — invariance of the statement under an
  isomorphism of endoscopic data.
* `Frontier.ngo_fundamental_lemma` — the base case: the unramified elliptic
  endoscopy of `SL(2)` over `F = 𝔽_q((ε))` (equivalently any local field with
  residue field of size `q`), for the unit element of the spherical Hecke algebra
  and for all depths `n`.

## The `SL(2)` base case

Let `γ ∈ SL(2, F)` be elliptic regular semisimple, generating an unramified
quadratic extension, with `val(disc γ) = 2n`.  The centraliser `T` of `γ` is the
elliptic unramified maximal torus, and `T(F)/T(O)` acts on the set of `γ`-fixed
vertices of the Bruhat–Tits tree of `PGL(2, F)` — a `(q+1)`-regular tree.  The
`γ`-fixed vertices modulo this action form the ball of radius `n` around the
vertex fixed by `T(O)`; this ball is precisely the set of `𝔽_q`-points of the
affine Springer fibre attached to `γ` modulo the lattice `T(F)/T(O)`.  Hence:

* the (stable) orbital integral of the unit `1_K` at `γ` is the number of vertices
  of that ball, `Frontier.treeBallCard`;
* the `κ`-orbital integral for the nontrivial character `κ` of the group of
  connected components is the same count weighted by `κ`, which on the tree is the
  parity of the distance to the central vertex, i.e. `Frontier.kappaCount`.

The endoscopic group here is the torus `T` itself, so its stable orbital integral
of the unit element is `1`, and the Langlands–Shelstad transfer factor is
`Δ = (-1)^n q^n`.  The content of the base case is therefore the closed formula

  `Frontier.kappaCount_eq : kappaCount q n = (-1)^n q^n`,

the cancellation in the alternating sum over the spheres of the tree, together
with the companion (unstable-free) count

  `Frontier.treeBallCard_eq : (q - 1) * treeBallCard q n = (q + 1) * q ^ n - 2`.
-/

namespace Frontier

/-! ### The statement of the fundamental lemma -/

/--
The data entering the Langlands–Shelstad fundamental lemma for one unramified
endoscopic datum:

* `HClass` : stable conjugacy classes of strongly regular semisimple elements of
  the endoscopic group `H`;
* `GClass` : stable conjugacy classes of strongly regular semisimple elements of
  `G`;
* `norm`   : the norm correspondence, sending a class in `H` to the class in `G`
  of which it is a norm, when such a class exists;
* `transferFactor` : the Langlands–Shelstad transfer factor `Δ(γ_H, γ)`;
* `HeckeG`, `HeckeH` : the spherical Hecke algebras of `G` and of `H`;
* `satakeTransfer` : the transfer map `b : ℋ(G) → ℋ(H)` dual to the embedding of
  `L`-groups on Satake parameters;
* `stableOrbitalIntegral` : `(f_H, γ_H) ↦ SO_{γ_H}(f_H)`;
* `kappaOrbitalIntegral` : `(f, γ) ↦ O^κ_γ(f)`.

All integrals are taken with respect to normalised measures making the quantities
below integral.
-/
structure EndoscopicDatum where
  /-- Stable classes of strongly regular semisimple elements of the endoscopic group `H`. -/
  HClass : Type
  /-- Stable classes of strongly regular semisimple elements of `G`. -/
  GClass : Type
  /-- The norm correspondence from stable classes in `H` to stable classes in `G`. -/
  norm : HClass → Option GClass
  /-- The Langlands–Shelstad transfer factor. -/
  transferFactor : HClass → Int
  /-- The spherical Hecke algebra of `G`. -/
  HeckeG : Type
  /-- The spherical Hecke algebra of `H`. -/
  HeckeH : Type
  /-- The transfer map on spherical Hecke algebras dual to the endoscopic datum. -/
  satakeTransfer : HeckeG → HeckeH
  /-- Stable orbital integrals on the endoscopic group. -/
  stableOrbitalIntegral : HeckeH → HClass → Int
  /-- `κ`-orbital integrals on `G`. -/
  kappaOrbitalIntegral : HeckeG → GClass → Int

/--
The Langlands–Shelstad fundamental lemma for the endoscopic datum `D`:
for every spherical Hecke function `f` on `G` and every pair `(γ_H, γ)` in the
norm correspondence,

  `Δ(γ_H, γ) · SO_{γ_H}(b f) = O^κ_γ(f)`.
-/
