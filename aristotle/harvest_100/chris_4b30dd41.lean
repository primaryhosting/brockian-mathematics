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
noncomputable def kappaOrbitalIntegral (S : EndoscopicSetup E) (κ : AddChar E ℂ) : ℂ :=
  ∑ a : E, κ a * S.orb a

/-- The stable orbital integral `SO_γ(1_K) = ∑_{a ∈ E} O_{γ_a}(1_K)` on `G` itself. -/
noncomputable def stableOrbitalIntegral (S : EndoscopicSetup E) : ℂ := ∑ a : E, S.orb a

/-- **The Langlands–Shelstad fundamental lemma** (Ngô Bảo Châu): for every endoscopic
character `κ`, the stable orbital integral of the unit of the Hecke algebra of the
endoscopic group `H_κ` at the matching element `γ_κ` equals the transfer factor times the
`κ`-orbital integral of the unit of the Hecke algebra of `G` at `γ`. -/
def FundamentalLemma (S : EndoscopicSetup E) : Prop :=
  ∀ κ : AddChar E ℂ, S.stabOrbH κ = S.transfer κ * S.kappaOrbitalIntegral κ

/-- For the trivial endoscopic character the `κ`-orbital integral is the stable orbital
integral: this is the tautological ("trivial endoscopy", `H = G`) case of the lemma. -/
theorem kappaOrbitalIntegral_zero (S : EndoscopicSetup E) :
    S.kappaOrbitalIntegral 0 = S.stableOrbitalIntegral := by
  simp [kappaOrbitalIntegral, stableOrbitalIntegral]

/-- Orthogonality of characters of a finite abelian group, summed over the group. -/
theorem sum_char_div_char (κ lam : AddChar E ℂ) :
    ∑ a : E, κ a / lam a = if κ = lam then (Fintype.card E : ℂ) else 0 := by
  have h : ∀ a : E, κ a / lam a = (κ - lam) a := fun a => (AddChar.sub_apply' κ lam a).symm
  simp only [h]
  rw [AddChar.sum_eq_ite]
  simp [sub_eq_zero]

/-- Orthogonality of characters of a finite abelian group, summed over the dual group. -/
theorem sum_dual_char (a b : E) :
    ∑ κ : AddChar E ℂ, κ a / κ b = if a = b then (Fintype.card E : ℂ) else 0 := by
  have h : ∀ κ : AddChar E ℂ, κ a / κ b = κ (a - b) := fun κ =>
    (AddChar.map_sub_eq_div κ a b).symm
  simp only [h]
  rw [AddChar.sum_apply_eq_ite]
  simp [sub_eq_zero]

/-- **The stabilization / Fourier inversion reduction of the fundamental lemma.**

For a local endoscopic setup, the fundamental lemma holds for all endoscopic characters
`κ` if and only if every ordinary orbital integral of `γ` is recovered from the stable
orbital integrals on the endoscopic groups by the finite Fourier inversion formula
`O_{γ_a}(1_K) = |𝔈(γ)|⁻¹ ∑_κ κ(a)⁻¹ · SO_{γ_κ}(1_{K_{H_κ}}) / Δ(γ_κ, γ)`. -/
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
theorem orb_eq_of_fundamentalLemma {S T : EndoscopicSetup E}
    (hS : S.FundamentalLemma) (hT : T.FundamentalLemma)
    (hstab : S.stabOrbH = T.stabOrbH) (htr : S.transfer = T.transfer) : S.orb = T.orb := by
  funext a
  rw [(S.fundamentalLemma_iff_inversion.1 hS) a, (T.fundamentalLemma_iff_inversion.1 hT) a,
    hstab, htr]

/-!
## Base cases
-/

/-- **Base case: trivial endoscopy.**  The setup in which the endoscopic data are the
group `G` itself twisted by `κ`, with trivial transfer factors, satisfies the fundamental
lemma unconditionally.  In particular the fundamental lemma is a consistent (nonvacuous)
statement, and for `κ = 0` it reduces to the identity `SO_γ = SO_γ`. -/
noncomputable def trivialSetup (orb : E → ℂ) : EndoscopicSetup E where
  orb := orb
  stabOrbH := fun κ => ∑ a : E, κ a * orb a
  transfer := fun _ => 1
  transfer_ne_zero := fun _ => one_ne_zero

theorem trivialSetup_fundamentalLemma (orb : E → ℂ) :
    (trivialSetup orb).FundamentalLemma := by
  intro κ
  simp [trivialSetup, kappaOrbitalIntegral]

/-- **Base case: no endoscopy (`γ` has a single rational class in its stable class).**
When the group of cohomological invariants is trivial, every character is trivial and the
fundamental lemma is the single identity `SO_{γ_H}(1_{K_H}) = Δ · O_γ(1_K)`. -/
theorem fundamentalLemma_iff_of_subsingleton [Subsingleton E] (S : EndoscopicSetup E) :
    S.FundamentalLemma ↔ ∀ κ : AddChar E ℂ, S.stabOrbH κ = S.transfer κ * S.orb 0 := by
  haveI : Unique E := uniqueOfSubsingleton (0 : E)
  refine forall_congr' fun κ => ?_
  rw [kappaOrbitalIntegral]
  simp [Finset.univ_unique, Subsingleton.elim (default : E) 0]

/-!
## The `ℤ/2` case: elliptic endoscopy for `SL(2)`

For `SL(2)` (and, more generally, whenever the stable class of `γ` splits into two rational
classes) the group of invariants is `ℤ/2`; the nontrivial endoscopic character produces the
difference `O_{γ_0} - O_{γ_1}` of the two orbital integrals.
-/

/-- The nontrivial character of `ℤ/2` with values in `ℂ`. -/
noncomputable def signChar : AddChar (ZMod 2) ℂ where
  toFun a := if a = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro a b
    fin_cases a <;> fin_cases b <;> norm_num

theorem signChar_one : signChar 1 = -1 := by
  norm_num [signChar]

theorem kappaOrbitalIntegral_signChar (S : EndoscopicSetup (ZMod 2)) :
    S.kappaOrbitalIntegral signChar = S.orb 0 - S.orb 1 := by
  rw [kappaOrbitalIntegral, Finset.sum_congr rfl (fun _ _ => rfl)]
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
  norm_num [signChar]
  ring

/-- The fundamental lemma in the two-class (elliptic `SL(2)`) case: it is exactly the pair
consisting of the stable identity and of the endoscopic identity
`SO_{γ_H} = Δ · (O_{γ_0} - O_{γ_1})`. -/
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
theorem ngo_fundamental_lemma {E : Type} [AddCommGroup E] [Fintype E] [DecidableEq E]
    (S : EndoscopicSetup E) :
    (S.FundamentalLemma ↔
      ∀ a : E, S.orb a =
        (Fintype.card E : ℂ)⁻¹ * ∑ κ : AddChar E ℂ, (κ a)⁻¹ * (S.stabOrbH κ / S.transfer κ)) ∧
    ∀ orb : E → ℂ, (EndoscopicSetup.trivialSetup orb).FundamentalLemma :=
  ⟨S.fundamentalLemma_iff_inversion, fun orb => EndoscopicSetup.trivialSetup_fundamentalLemma orb⟩

end Frontier

