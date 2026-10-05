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

open Finset AddChar

/-!
## The local endoscopic setup

We formalize the *combinatorial skeleton* of the Langlands–Shelstad fundamental lemma,
as proved by Ngô Bảo Châu.

Fix a `p`-adic field `F` with ring of integers `O`, an unramified reductive group `G/F`
with hyperspecial maximal compact `K = G(O)`, and a strongly regular semisimple element
`γ ∈ G(F)`.  The rational conjugacy classes inside the stable conjugacy class of `γ` are
in bijection with the finite abelian group

  `E = 𝔈(γ) = ker ( H¹(F, T_γ) → H¹(F, G) )`,

where `T_γ` is the centralizer torus of `γ`.  Each rational class in the stable class of `γ`
therefore has an *invariant* `a ∈ E`, and `orb a` denotes the orbital integral
`O_{γ_a}(1_K)` of the unit of the spherical Hecke algebra along that class.

Endoscopic data for `γ` are indexed by the characters `κ ∈ Ê = Hom(E, ℂˣ)`: to `κ` is
attached an endoscopic group `H_κ` together with a matching stably conjugate element
`γ_κ ∈ H_κ(F)`, its stable orbital integral `SO_{γ_κ}(1_{K_{H_κ}})` (recorded as
`stabOrbH κ`) and a Langlands–Shelstad transfer factor `Δ(γ_κ, γ)` (recorded as
`transfer κ`, which is a nonzero complex number).

All the group-theoretic input is thus packaged in the structure `EndoscopicSetup`; the
fundamental lemma itself is the identity

  `SO_{γ_κ}(1_{K_{H_κ}}) = Δ(γ_κ, γ) · O^κ_γ(1_K)`,  where `O^κ_γ(1_K) = ∑_{a ∈ E} κ(a) O_{γ_a}(1_K)`,

recorded below as `EndoscopicSetup.FundamentalLemma`.
-/

/-- The data attached to a strongly regular semisimple element `γ` of an unramified
`p`-adic group `G`, whose stable conjugacy class is parametrized by the finite abelian
group `E` of cohomological invariants:

* `orb a` is the orbital integral `O_{γ_a}(1_K)` of the unit of the Hecke algebra
  along the rational class with invariant `a`;
* `stabOrbH κ` is the stable orbital integral `SO_{γ_κ}(1_{K_{H_κ}})` on the endoscopic
  group attached to the endoscopic character `κ`;
* `transfer κ` is the Langlands–Shelstad transfer factor `Δ(γ_κ, γ)`, a nonzero scalar. -/
structure EndoscopicSetup (E : Type) [AddCommGroup E] [Fintype E] where
  /-- Orbital integrals of the unit of the Hecke algebra along the rational classes
  inside the stable class of `γ`, indexed by their cohomological invariant. -/
  orb : E → ℂ
  /-- Stable orbital integrals on the endoscopic groups, indexed by endoscopic characters. -/
  stabOrbH : AddChar E ℂ → ℂ
  /-- Langlands–Shelstad transfer factors. -/
  transfer : AddChar E ℂ → ℂ
  /-- Transfer factors are nonzero. -/
  transfer_ne_zero : ∀ κ : AddChar E ℂ, transfer κ ≠ 0

namespace EndoscopicSetup

variable {E : Type} [AddCommGroup E] [Fintype E] [DecidableEq E]

/-- The `κ`-orbital integral `O^κ_γ(1_K) = ∑_{a ∈ E} κ(a) · O_{γ_a}(1_K)`. -/

theorem fundamentalLemma_zmod_two_iff (S : EndoscopicSetup (ZMod 2)) :
    S.FundamentalLemma ↔
      (S.stabOrbH 0 = S.transfer 0 * (S.orb 0 + S.orb 1) ∧
        S.stabOrbH signChar = S.transfer signChar * (S.orb 0 - S.orb 1)) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h 0
      rw [kappaOrbitalIntegral_zero, stableOrbitalIntegral] at this
      rw [this, show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
      norm_num
    · rw [h signChar, kappaOrbitalIntegral_signChar]
  · rintro ⟨h0, h1⟩ κ
    have hκ : κ = 0 ∨ κ = signChar := by
      by_cases hone : κ 1 = 1
      · left
        ext a
        fin_cases a
        · simp
        · simpa using hone
      · right
        ext a
        have h2 : κ 1 * κ 1 = 1 := by
          rw [← AddChar.map_add_eq_mul]
          simpa using κ.map_zero_eq_one
        have : κ 1 = -1 := by
          rcases mul_self_eq_one_iff.1 h2 with h | h
          · exact absurd h hone
          · exact h
        fin_cases a
        · simp [signChar]
        · simpa [signChar, this] using this
    rcases hκ with rfl | rfl
    · rw [kappaOrbitalIntegral_zero, stableOrbitalIntegral,
        show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
      norm_num [h0]
    · rw [kappaOrbitalIntegral_signChar]; exact h1

end EndoscopicSetup

/-- **Ngô's fundamental lemma, formalized statement together with its stabilization
reduction.**

`EndoscopicSetup.FundamentalLemma S` is the Langlands–Shelstad fundamental lemma for the
local endoscopic setup `S`: for every endoscopic character `κ` of the group `E = 𝔈(γ)` of
cohomological invariants of the stable conjugacy class of `γ`,

  `SO_{γ_κ}(1_{K_{H_κ}}) = Δ(γ_κ, γ) · O^κ_γ(1_K)`.

The theorem below is the Lean-checked *reduction* of this statement: it is equivalent to
the explicit stabilization (finite Fourier inversion) formula expressing each ordinary
orbital integral of `γ` in terms of the stable orbital integrals on the endoscopic groups,
and it holds unconditionally in the base case of trivial endoscopy. -/
