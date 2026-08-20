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

noncomputable def stableOrbitalH : ℂ := stableOrbital E.hOrbital

/-- The stable orbital integral `SO_γ(1_K)` on `G`. -/
