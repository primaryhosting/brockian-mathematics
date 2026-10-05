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

theorem fundamentalLemma_iff_inversion (S : EndoscopicSetup E) :
    S.FundamentalLemma ↔
      ∀ a : E, S.orb a =
        (Fintype.card E : ℂ)⁻¹ * ∑ κ : AddChar E ℂ, (κ a)⁻¹ * (S.stabOrbH κ / S.transfer κ) := by
  have hcard : (Fintype.card E : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  set g : AddChar E ℂ → ℂ := fun κ => S.stabOrbH κ / S.transfer κ with hg
  have hFL : S.FundamentalLemma ↔ ∀ κ : AddChar E ℂ, g κ = ∑ b : E, κ b * S.orb b := by
    refine forall_congr' fun κ => ?_
    rw [hg, kappaOrbitalIntegral]
    constructor
    · intro h; rw [h]; field_simp
    · intro h; field_simp at h ⊢; rw [← h]; ring
  rw [hFL]
  constructor
  · intro h a
    have step : ∑ κ : AddChar E ℂ, (κ a)⁻¹ * g κ
        = ∑ b : E, (∑ κ : AddChar E ℂ, κ b / κ a) * S.orb b := by
      rw [Finset.sum_congr rfl (fun κ _ => by rw [h κ, Finset.mul_sum]), Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun κ _ => by field_simp
    rw [step]
    simp only [sum_dual_char]
    rw [Finset.sum_eq_single a]
    · rw [if_pos rfl, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
    · intro b _ hb; rw [if_neg hb, zero_mul]
    · intro hb; exact absurd (Finset.mem_univ a) hb
  · intro h lam
    have e1 : ∀ b : E, lam b * S.orb b
        = (Fintype.card E : ℂ)⁻¹ * ∑ κ : AddChar E ℂ, (lam b / κ b) * g κ := by
      intro b
      simp only [h b, Finset.mul_sum, div_eq_mul_inv]
      exact Finset.sum_congr rfl fun κ _ => by ring
    have step : ∑ b : E, lam b * S.orb b
        = (Fintype.card E : ℂ)⁻¹ * ∑ κ : AddChar E ℂ, (∑ b : E, lam b / κ b) * g κ := by
      rw [Finset.sum_congr rfl (fun b _ => e1 b), ← Finset.mul_sum, Finset.sum_comm]
      congr 1
      exact Finset.sum_congr rfl fun κ _ => (Finset.sum_mul _ _ _).symm
    rw [step]
    simp only [sum_char_div_char]
    rw [Finset.sum_eq_single lam]
    · rw [if_pos rfl, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
    · intro κ _ hκ; rw [if_neg (Ne.symm hκ), zero_mul]
    · intro hκ; exact absurd (Finset.mem_univ lam) hκ

/-- The fundamental lemma determines the individual orbital integrals of `γ`: two setups
with the same endoscopic stable orbital integrals and transfer factors, both satisfying
the fundamental lemma, have the same orbital integrals. -/
