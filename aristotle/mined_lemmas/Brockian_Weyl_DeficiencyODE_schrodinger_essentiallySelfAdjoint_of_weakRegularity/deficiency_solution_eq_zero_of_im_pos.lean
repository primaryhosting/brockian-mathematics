import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
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

set_option grind.warning false

namespace Brockian.Weyl.DeficiencyODE

open scoped InnerProductSpace
open Filter Topology

/-!
## Unbounded operators: graphs, adjoints, essential self-adjointness
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The graph of the (generally unbounded) operator `T` defined on the domain `D ≤ E`,
viewed as a submodule of `E × E`. -/

lemma deficiency_solution_eq_zero_of_im_pos (q : ℤ → ℝ) (z : ℂ) (hz : 0 < z.im) (c : ℤ → ℂ)
    (hsum : Summable fun n => ‖c n‖ ^ 2)
    (heq : ∀ n, (q n : ℂ) * c n - c (n + 1) - c (n - 1) = z * c n) : ∀ n, c n = 0 := by
  have hkey := wronskian_sub q z c heq
  have hstep : ∀ n : ℤ, wronskian c n ≤ wronskian c (n - 1) := by
    intro n
    have h := hkey n
    nlinarith [sq_nonneg ‖c n‖]
  have hanti : ∀ m n : ℤ, m ≤ n → wronskian c n ≤ wronskian c m := by
    intro m n hmn
    induction n, hmn using Int.le_induction with
    | base => exact le_rfl
    | succ n hn ih =>
        have h := hstep (n + 1)
        simp only [add_sub_cancel_right] at h
        linarith
  obtain ⟨htop, hbot⟩ := tendsto_wronskian c hsum
  have hnonneg : ∀ n, 0 ≤ wronskian c n := by
    intro n
    refine le_of_tendsto htop ?_
    filter_upwards [eventually_ge_atTop n] with m hm using hanti n m hm
  have hnonpos : ∀ n, wronskian c n ≤ 0 := by
    intro n
    refine ge_of_tendsto hbot ?_
    filter_upwards [eventually_le_atBot n] with m hm using hanti m n hm
  intro n
  have h := hkey n
  rw [le_antisymm (hnonpos _) (hnonneg _), le_antisymm (hnonpos _) (hnonneg _)] at h
  have h0 : z.im * ‖c n‖ ^ 2 = 0 := by linarith
  have : ‖c n‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 (ne_of_gt hz)
    · exact h1
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

/-- **No nonzero `ℓ²` solutions of the deficiency equation.**  For a non-real spectral parameter
`z` and an arbitrary real potential `q`, the second order difference equation
`q n * c n - c (n+1) - c (n-1) = z * c n` has no nonzero square-summable solution. -/
