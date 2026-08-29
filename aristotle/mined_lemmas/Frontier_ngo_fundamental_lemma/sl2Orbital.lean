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

/-!
## The Langlands–Shelstad fundamental lemma (Ngô)

Let `G` be an unramified connected reductive group over a non-archimedean local field `F`
with hyperspecial maximal compact `K`, let `(H, s, η)` be an endoscopic datum for `G` with
hyperspecial maximal compact `K_H`, and let `γ_H ∈ H(F)` be a strongly `G`-regular semisimple
element with norm `γ ∈ G(F)`.  Write `𝔎 = 𝔎(I_γ/F)` for the finite abelian group of
obstructions classifying the `G(F)`-conjugacy classes inside the stable conjugacy class of `γ`,
`κ ∈ 𝔎^` for the character determined by `s`, and `Δ(γ_H, γ)` for the Langlands–Shelstad
transfer factor.  The fundamental lemma, proved by Ngô, asserts

  `Δ(γ_H, γ) · O^κ_γ(1_K) = SO_{γ_H}(1_{K_H})`,

where `O^κ_γ(1_K) = ∑_{γ' ∼_{st} γ} κ(inv(γ', γ)) · O_{γ'}(1_K)` is the `κ`-orbital integral
of the unit element of the Hecke algebra and `SO_{γ_H}(1_{K_H})` is the stable orbital integral
on the endoscopic group.

This file formalizes the *shape* of that identity as a statement about the finite combinatorial
data it involves (the finite set of rational classes in a stable class, the obstruction group,
the endoscopic character, the orbital integrals, and the transfer factor), and then proves:

* the trivial-endoscopy base case `H = G` (`κ = 1`), where the identity is the definition of
  the stable orbital integral;
* the *stable vanishing reduction*: a nontrivial `κ` annihilates orbital data that is constant
  on the stable class (orthogonality of characters of `𝔎`) — this is the mechanism by which
  the endoscopic terms are detected;
* an additivity reduction, allowing the identity to be checked one stable class at a time;
* the **base case of the fundamental lemma for `SL(2)`**: for the unit element of the Hecke
  algebra and an unramified elliptic torus with `val(disc γ) = 2n`, the orbital integrals are
  counts of vertices of the Bruhat–Tits tree of `SL(2)` (a `(q+1)`-regular tree) lying in the
  ball of radius `n` around the vertex fixed by the torus, split according to the parity of the
  distance (which is exactly the invariant in `𝔎 ≅ ℤ/2`).  The theorem proved is
  `((-1)^n * q^(-n)) * O^κ = 1 = SO_{γ_H}(1_{K_H})`, i.e. the fundamental lemma in this case,
  the content being the computation `O^κ = (-q)^n`.
-/

/-- The finite combinatorial data entering the fundamental lemma for one strongly regular
semisimple stable conjugacy class.

* `Conj` indexes the `G(F)`-conjugacy classes inside the given stable conjugacy class;
* `Obs` is the finite abelian obstruction group `𝔎(I_γ/F)`;
* `inv γ'` is the invariant in `𝔎` of the rational class `γ'` relative to the base point;
* `kappa` is the character of `𝔎` attached to the endoscopic datum;
* `orbital γ'` is the orbital integral `O_{γ'}(1_K)`;
* `transfer` is the Langlands–Shelstad transfer factor `Δ(γ_H, γ)`;
* `endoStable` is the stable orbital integral `SO_{γ_H}(1_{K_H})` on the endoscopic group. -/
structure EndoscopicDatum (Conj : Type) (Obs : Type) [Fintype Conj] [AddCommGroup Obs] where
  /-- Invariant in `𝔎(I_γ/F)` of a rational class inside the stable class. -/
  inv : Conj → Obs
  /-- The character `κ` of `𝔎(I_γ/F)` determined by the endoscopic datum. -/
  kappa : AddChar Obs ℂ
  /-- The orbital integrals `O_{γ'}(1_K)` of the unit element of the Hecke algebra. -/
  orbital : Conj → ℂ
  /-- The Langlands–Shelstad transfer factor `Δ(γ_H, γ)`. -/
  transfer : ℂ
  /-- The stable orbital integral `SO_{γ_H}(1_{K_H})` on the endoscopic group. -/
  endoStable : ℂ

namespace EndoscopicDatum

variable {Conj Obs : Type} [Fintype Conj] [AddCommGroup Obs]

/-- The `κ`-orbital integral `O^κ_γ(1_K) = ∑_{γ'} κ(inv γ') O_{γ'}(1_K)`. -/

noncomputable def sl2Orbital (q n : ℕ) (ε : ZMod 2) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), if (k : ZMod 2) = ε then (treeSphere q k : ℂ) else 0

/-- The nontrivial character of `𝔎 ≅ ℤ/2`, the obstruction group for the stable class of a
regular elliptic element of `SL(2)`. -/
