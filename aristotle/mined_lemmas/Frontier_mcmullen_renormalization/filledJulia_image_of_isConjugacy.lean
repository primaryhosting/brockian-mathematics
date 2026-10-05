/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not allow a module
-- docstring before the `import` line; the same text is reproduced as the module docstring below.)

import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
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

/-! ## Quadratic-like maps (Douady–Hubbard) -/

/-- A *quadratic-like map* in the sense of Douady–Hubbard: a proper degree-two
holomorphic branched covering `f : V → U` between two bounded, connected open subsets of `ℂ`
with `closure V ⊆ U`.

Degree two is encoded concretely: there is a (unique) critical point `c ∈ V` whose fibre is the
singleton `{c}`, and every other fibre over `U` consists of exactly two points. -/
structure QuadraticLike : Type where
  /-- The larger domain. -/
  U : Set ℂ
  /-- The smaller domain, compactly contained in `U`. -/
  V : Set ℂ
  /-- The map (defined on all of `ℂ`, but only its restriction to `V` matters). -/
  f : ℂ → ℂ
  /-- The critical point. -/
  c : ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  closure_V_subset : closure V ⊆ U
  isBounded_V : Bornology.IsBounded V
  isPreconnected_U : IsPreconnected U
  isPreconnected_V : IsPreconnected V
  analyticOn : AnalyticOnNhd ℂ f V
  mapsTo : Set.MapsTo f V U
  surjOn : Set.SurjOn f V U
  /-- Properness of `f : V → U`. -/
  proper : ∀ L ⊆ U, IsCompact L → IsCompact (V ∩ f ⁻¹' L)
  crit_mem : c ∈ V
  /-- The critical fibre is a single point. -/
  crit_fiber : V ∩ f ⁻¹' {f c} = {c}
  /-- Every non-critical fibre has exactly two points: `f : V → U` has degree two. -/
  deg_two : ∀ w ∈ U, w ≠ f c → (V ∩ f ⁻¹' {w}).ncard = 2

namespace QuadraticLike

variable (F : QuadraticLike)

/-- The filled Julia set of a quadratic-like map: the points of `V` whose whole forward
orbit stays in `V`. -/

theorem filledJulia_image_of_isConjugacy {F G : QuadraticLike} {h : ℂ → ℂ}
    (hc : IsConjugacy F G h) : h '' F.filledJulia = G.filledJulia := by
  obtain ⟨hU, hV, hcomm⟩ := hc
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩ n
    have : h (F.f^[n] z) = G.f^[n] (h z) :=
      iterate_conj ⟨hU, hV, hcomm⟩ n fun k _ => hz k
    rw [← this]
    exact hV.mapsTo (hz n)
  · intro w hw
    obtain ⟨z, hzV, rfl⟩ := hV.surjOn (by simpa using hw 0)
    have key : ∀ n : ℕ, ∀ k ≤ n, F.f^[k] z ∈ F.V := by
      intro n
      induction n with
      | zero => intro k hk; interval_cases k; simpa using hzV
      | succ n ih =>
          intro k hk
          rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hk) with hk' | rfl
          · exact ih k (by omega)
          · have hiter : h (F.f^[n + 1] z) = G.f^[n + 1] (h z) :=
              iterate_conj ⟨hU, hV, hcomm⟩ (n + 1) fun j hj => ih j (by omega)
            have hmemG : G.f^[n + 1] (h z) ∈ G.V := hw (n + 1)
            obtain ⟨y, hyV, hy⟩ := hV.surjOn (by rw [← hiter] at hmemG; exact hmemG)
            have hzU : F.f^[n + 1] z ∈ F.U := by
              rw [Function.iterate_succ_apply']
              exact F.mapsTo (ih n le_rfl)
            have : F.f^[n + 1] z = y :=
              hU.injOn hzU (F.V_subset_U hyV) (by rw [hy])
            rw [this]
            exact hyV
    exact ⟨z, fun n => key n n le_rfl, rfl⟩

/-! ## A concrete quadratic-like map: the squaring map -/

/-- Iterates of the squaring map. -/
