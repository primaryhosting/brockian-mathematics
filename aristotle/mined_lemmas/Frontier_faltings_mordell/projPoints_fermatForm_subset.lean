import Mathlib

/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MvPolynomial

/-! ## Setting up plane curves over `ℚ` -/

/-- The set of `ℚ`-rational points of the projective plane curve cut out by a homogeneous
form `F` in three variables. A point of `ℙ²(ℚ)` is represented as a point of
`Projectivization ℚ (Fin 3 → ℚ)`; since `F` is homogeneous, vanishing of `F` at a
representative does not depend on the chosen representative (see
`Frontier.mem_projPoints_fermatForm_iff` for the case used below). -/

theorem projPoints_fermatForm_subset (n : ℕ) (hn : 4 ∣ n) (hn0 : n ≠ 0) :
    projPoints (fermatForm n) ⊆
      ({Projectivization.mk ℚ ![1, 0, 1] (vec_ne_zero 1 0),
        Projectivization.mk ℚ ![-1, 0, 1] (vec_ne_zero (-1) 0),
        Projectivization.mk ℚ ![0, 1, 1] (vec_ne_zero 0 1),
        Projectivization.mk ℚ ![0, -1, 1] (vec_ne_zero 0 (-1))} :
        Set (Projectivization ℚ (Fin 3 → ℚ))) := by
  have heven : Even n := by
    obtain ⟨k, rfl⟩ := hn
    exact ⟨2 * k, by ring⟩
  intro P hP
  set v : Fin 3 → ℚ := P.rep with hvdef
  have hv : v ≠ 0 := P.rep_nonzero
  have hzero : v 0 ^ n + v 1 ^ n - v 2 ^ n = 0 := by
    have h := hP
    simp only [projPoints, Set.mem_setOf_eq, eval_fermatForm] at h
    exact h
  have heq : v 0 ^ n + v 1 ^ n = v 2 ^ n := by linarith
  -- one of the coordinates vanishes, by Fermat's Last Theorem for exponent `n`
  have hcase : v 0 = 0 ∨ v 1 = 0 ∨ v 2 = 0 := by
    by_contra hc
    push_neg at hc
    exact flt_rat_of_four_dvd hn (v 0) (v 1) (v 2) hc.1 hc.2.1 hc.2.2 heq
  -- a helper: identifying `P` with the projectivization of an explicit vector
  have hmk : ∀ (c x y : ℚ), c ≠ 0 → (v 0 = c * x) → (v 1 = c * y) → (v 2 = c) →
      P = Projectivization.mk ℚ ![x, y, 1] (vec_ne_zero x y) := by
    intro c x y hc h0 h1 h2
    have : Projectivization.mk ℚ v hv = Projectivization.mk ℚ ![x, y, 1] (vec_ne_zero x y) := by
      rw [Projectivization.mk_eq_mk_iff]
      refine ⟨Units.mk0 c hc, ?_⟩
      funext i
      fin_cases i <;>
        simp [Units.smul_def, h0, h1, h2]
    exact (Projectivization.mk_rep P).symm.trans this
  have hv2 : v 2 ≠ 0 := by
    intro h2
    have h01 : v 0 ^ n + v 1 ^ n = 0 := by rw [heq, h2]; simp [hn0]
    have hp0 : (0 : ℚ) ≤ v 0 ^ n := heven.pow_nonneg _
    have hp1 : (0 : ℚ) ≤ v 1 ^ n := heven.pow_nonneg _
    have e0 : v 0 ^ n = 0 := by linarith
    have e1 : v 1 ^ n = 0 := by linarith
    have z0 : v 0 = 0 := pow_eq_zero_iff hn0 |>.mp e0
    have z1 : v 1 = 0 := pow_eq_zero_iff hn0 |>.mp e1
    exact hv (funext fun i => by fin_cases i <;> simpa using ‹_›)
  rcases hcase with h0 | h1 | h2
  · -- `v 0 = 0`, so `v 1 = ± v 2`
    have hpow : v 1 ^ n = v 2 ^ n := by rw [← heq, h0]; simp [hn0]
    rcases eq_or_eq_neg_of_pow_eq_pow hn0 heven hpow with h | h
    · right; right; left
      exact hmk (v 2) 0 1 hv2 (by rw [h0]; ring) (by rw [h]; ring) rfl
    · right; right; right
      simp only [Set.mem_singleton_iff]
      exact hmk (v 2) 0 (-1) hv2 (by rw [h0]; ring) (by rw [h]; ring) rfl
  · -- `v 1 = 0`, so `v 0 = ± v 2`
    have hpow : v 0 ^ n = v 2 ^ n := by rw [← heq, h1]; simp [hn0]
    rcases eq_or_eq_neg_of_pow_eq_pow hn0 heven hpow with h | h
    · left
      exact hmk (v 2) 1 0 hv2 (by rw [h]; ring) (by rw [h1]; ring) rfl
    · right; left
      exact hmk (v 2) (-1) 0 hv2 (by rw [h]; ring) (by rw [h1]; ring) rfl
  · exact absurd h2 hv2

