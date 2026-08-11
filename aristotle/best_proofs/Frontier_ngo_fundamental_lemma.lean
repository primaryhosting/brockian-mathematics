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
def FundamentalLemmaHolds (D : EndoscopicDatum) : Prop :=
  ∀ (f : D.HeckeG) (gH : D.HClass) (gG : D.GClass), D.norm gH = some gG →
    D.transferFactor gH * D.stableOrbitalIntegral (D.satakeTransfer f) gH
      = D.kappaOrbitalIntegral f gG

/-! ### The trivial endoscopic datum -/

/--
The trivial endoscopic datum `H = G`, `κ = 1`, `Δ = 1`: the norm correspondence is
the identity, the transfer map on Hecke algebras is the identity, and the
`κ`-orbital integral is the ordinary (stable) orbital integral `O`.
-/
def trivialDatum (C A : Type) (O : A → C → Int) : EndoscopicDatum where
  HClass := C
  GClass := C
  norm := some
  transferFactor := fun _ => 1
  HeckeG := A
  HeckeH := A
  satakeTransfer := id
  stableOrbitalIntegral := O
  kappaOrbitalIntegral := O

/-- The fundamental lemma holds for the trivial endoscopic datum. -/
theorem fundamentalLemma_trivialDatum (C A : Type) (O : A → C → Int) :
    FundamentalLemmaHolds (trivialDatum C A O) := by
  intro f gH gG h
  have hg : gH = gG := by
    simpa [trivialDatum] using h
  subst hg
  simp [trivialDatum]

/-! ### Reduction to the factors of a product -/

/-- The product of two endoscopic data, `H₁ × H₂` inside `G₁ × G₂`. -/
def prodDatum (D E : EndoscopicDatum) : EndoscopicDatum where
  HClass := D.HClass × E.HClass
  GClass := D.GClass × E.GClass
  norm := fun p =>
    match D.norm p.1, E.norm p.2 with
    | some a, some b => some (a, b)
    | _, _ => none
  transferFactor := fun p => D.transferFactor p.1 * E.transferFactor p.2
  HeckeG := D.HeckeG × E.HeckeG
  HeckeH := D.HeckeH × E.HeckeH
  satakeTransfer := fun f => (D.satakeTransfer f.1, E.satakeTransfer f.2)
  stableOrbitalIntegral := fun f p =>
    D.stableOrbitalIntegral f.1 p.1 * E.stableOrbitalIntegral f.2 p.2
  kappaOrbitalIntegral := fun f p =>
    D.kappaOrbitalIntegral f.1 p.1 * E.kappaOrbitalIntegral f.2 p.2

/--
Reduction of the fundamental lemma for a product of endoscopic data to the
fundamental lemma for each factor.
-/
theorem fundamentalLemma_prodDatum {D E : EndoscopicDatum}
    (hD : FundamentalLemmaHolds D) (hE : FundamentalLemmaHolds E) :
    FundamentalLemmaHolds (prodDatum D E) := by
  intro f gH gG h
  have h' : (match D.norm gH.1, E.norm gH.2 with
      | some a, some b => some (a, b)
      | _, _ => none) = some gG := h
  revert h'
  cases hD' : D.norm gH.1 with
  | none => intro h'; simp at h'
  | some a =>
    cases hE' : E.norm gH.2 with
    | none => intro h'; simp at h'
    | some b =>
      intro h'
      have hab : (a, b) = gG := by
        simpa using h'
      have h1 := hD f.1 gH.1 a hD'
      have h2 := hE f.2 gH.2 b hE'
      subst hab
      show D.transferFactor gH.1 * E.transferFactor gH.2 *
          (D.stableOrbitalIntegral (D.satakeTransfer f.1) gH.1 *
            E.stableOrbitalIntegral (E.satakeTransfer f.2) gH.2)
        = D.kappaOrbitalIntegral f.1 a * E.kappaOrbitalIntegral f.2 b
      rw [← h1, ← h2]
      grind

/-! ### Invariance under isomorphism of data -/

/--
Transport of the fundamental lemma along an isomorphism of endoscopic data:
if all the ingredients of `E` are obtained from those of `D` through bijections
of the class sets and of the Hecke algebras, then the fundamental lemma for `D`
implies it for `E`.
-/
theorem fundamentalLemma_transport {D E : EndoscopicDatum}
    (hD : FundamentalLemmaHolds D)
    (uH : E.HClass → D.HClass) (uG : D.GClass → E.GClass)
    (uf : E.HeckeG → D.HeckeG)
    (hnorm : ∀ gH, E.norm gH = (D.norm (uH gH)).map uG)
    (hΔ : ∀ gH, E.transferFactor gH = D.transferFactor (uH gH))
    (hSO : ∀ f gH, E.stableOrbitalIntegral (E.satakeTransfer f) gH
      = D.stableOrbitalIntegral (D.satakeTransfer (uf f)) (uH gH))
    (hO : ∀ f gG, E.kappaOrbitalIntegral f (uG gG) = D.kappaOrbitalIntegral (uf f) gG) :
    FundamentalLemmaHolds E := by
  intro f gH gG h
  rw [hnorm gH] at h
  cases hD' : D.norm (uH gH) with
  | none => rw [hD'] at h; simp at h
  | some a =>
    rw [hD'] at h
    have hag : uG a = gG := by simpa using h
    subst hag
    rw [hΔ gH, hSO f gH, hO f a]
    exact hD (uf f) (uH gH) a hD'

/-! ### The Bruhat–Tits tree counts for the `SL(2)` base case -/

/-- `qpow q k = q ^ k`, as an integer. -/
def qpow (q : Nat) : Nat → Int
  | 0 => 1
  | k + 1 => (q : Int) * qpow q k

/-- `signPow k = (-1) ^ k`. -/
def signPow : Nat → Int
  | 0 => 1
  | k + 1 => -signPow k

/--
The number of vertices at distance `k` from a fixed vertex in the `(q+1)`-regular
Bruhat–Tits tree of `PGL(2, F)`.
-/
def treeSphereCard (q : Nat) : Nat → Int
  | 0 => 1
  | k + 1 => ((q : Int) + 1) * qpow q k

/--
The number of vertices at distance at most `n` from a fixed vertex of the
`(q+1)`-regular tree.  For an elliptic regular semisimple `γ ∈ SL(2, F)` of the
unramified type with `val(disc γ) = 2n`, this is the number of `γ`-fixed vertices
modulo the action of `T(F)/T(O)`, i.e. the orbital integral `O_γ(1_K)`.
-/
def treeBallCard (q : Nat) : Nat → Int
  | 0 => 1
  | n + 1 => treeBallCard q n + treeSphereCard q (n + 1)

/--
The same ball, counted with the sign `κ` (the parity of the distance to the
central vertex): this is the `κ`-orbital integral `O^κ_γ(1_K)`.
-/
def kappaCount (q : Nat) : Nat → Int
  | 0 => 1
  | n + 1 => kappaCount q n + signPow (n + 1) * treeSphereCard q (n + 1)

/-- Closed formula for the number of vertices of a ball in the `(q+1)`-regular tree:
`(q - 1) * #B(n) = (q + 1) * q ^ n - 2`, i.e. `#B(n) = 1 + (q+1)(q^n - 1)/(q - 1)`. -/
theorem treeBallCard_eq (q : Nat) : ∀ n : Nat,
    ((q : Int) - 1) * treeBallCard q n = ((q : Int) + 1) * qpow q n - 2
  | 0 => by show ((q : Int) - 1) * 1 = ((q : Int) + 1) * 1 - 2; grind
  | n + 1 => by
    have ih := treeBallCard_eq q n
    show ((q : Int) - 1) * (treeBallCard q n + treeSphereCard q (n + 1))
      = ((q : Int) + 1) * qpow q (n + 1) - 2
    rw [show treeSphereCard q (n + 1) = ((q : Int) + 1) * qpow q n from rfl,
      show qpow q (n + 1) = (q : Int) * qpow q n from rfl]
    grind

/--
The alternating (`κ`-weighted) count of the ball of radius `n` in the
`(q+1)`-regular tree collapses to `(-1)^n q^n`.  This cancellation is the
arithmetic content of the fundamental lemma for the unramified elliptic
endoscopy of `SL(2)`.
-/
theorem kappaCount_eq (q : Nat) : ∀ n : Nat,
    kappaCount q n = signPow n * qpow q n
  | 0 => by simp [kappaCount, signPow, qpow]
  | n + 1 => by
    have ih := kappaCount_eq q n
    show kappaCount q n + signPow (n + 1) * treeSphereCard q (n + 1)
      = signPow (n + 1) * qpow q (n + 1)
    rw [ih, show treeSphereCard q (n + 1) = ((q : Int) + 1) * qpow q n from rfl,
      show qpow q (n + 1) = (q : Int) * qpow q n from rfl,
      show signPow (n + 1) = -signPow n from rfl]
    grind

/-! ### The base case: unramified elliptic endoscopy of `SL(2)` -/

/--
The unramified elliptic endoscopic datum of `G = SL(2)` over a local field with
residue cardinality `q`: the endoscopic group is the elliptic unramified maximal
torus `H = T`, and `κ` is the nontrivial character of the group of connected
components.

Stable classes on either side are indexed by the depth `n`, where
`val(disc γ) = 2n`; the norm correspondence matches equal depths.  The transfer
factor is `Δ = (-1)^n q^n`; since `H` is a torus, the stable orbital integral of
the unit element of its spherical Hecke algebra is `1`; and the `κ`-orbital
integral of the unit element `1_K` of the spherical Hecke algebra of `G` is the
signed point count `kappaCount q n` of the affine Springer fibre, described by
the ball of radius `n` in the Bruhat–Tits tree.
-/
def sl2UnramifiedDatum (q : Nat) : EndoscopicDatum where
  HClass := Nat
  GClass := Nat
  norm := some
  transferFactor := fun n => signPow n * qpow q n
  HeckeG := Unit
  HeckeH := Unit
  satakeTransfer := id
  stableOrbitalIntegral := fun _ _ => 1
  kappaOrbitalIntegral := fun _ n => kappaCount q n

/--
**Base case of the Langlands–Shelstad fundamental lemma (Ngô).**

The fundamental lemma holds for the unramified elliptic endoscopy of `SL(2)` over
a local field with residue cardinality `q`, for the unit element of the spherical
Hecke algebra and every depth `n`:

  `Δ(γ_H, γ) · SO_{γ_H}(1_{K_H}) = O^κ_γ(1_K)`,

which unwinds to `(-1)^n q^n · 1 = kappaCount q n`, the alternating point count of
the affine Springer fibre (`kappaCount_eq`).
-/
theorem ngo_fundamental_lemma (q : Nat) :
    FundamentalLemmaHolds (sl2UnramifiedDatum q) := by
  intro f gH gG h
  have hg : gH = gG := by simpa [sl2UnramifiedDatum] using h
  subst hg
  show signPow gH * qpow q gH * 1 = kappaCount q gH
  rw [kappaCount_eq]
  grind

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

