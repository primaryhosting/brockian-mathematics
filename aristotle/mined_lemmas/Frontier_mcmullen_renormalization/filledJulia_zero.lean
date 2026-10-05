/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

namespace Frontier

/-! ## Quadratic-like maps

A *quadratic-like map* (Douady–Hubbard; the basic object of McMullen's work on
renormalization) is a holomorphic proper degree-two branched cover `f : U → V`
between open subsets of `ℂ` with `U` compactly contained in `V`.  The
degree-two condition is encoded concretely below: there is one critical value,
whose fiber is a single point, and every other value has exactly two
preimages. -/

/-- The quadratic family `z ↦ z ^ 2 + c`. -/

theorem filledJulia_zero {R : ℝ} (hR : 1 < R) :
    filledJulia (qmap 0) R = Metric.closedBall (0 : ℂ) 1 := by
  ext z
  simp only [filledJulia, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt R hcon
    have hmn : m ≤ 2 ^ m := Nat.le_of_lt (Nat.lt_two_pow_self)
    have h1 : ‖z‖ ^ m ≤ ‖z‖ ^ (2 ^ m) := pow_le_pow_right₀ (le_of_lt hcon) hmn
    have h2 : ‖(qmap 0)^[m] z‖ ≤ R := h m
    rw [iterate_qmap_zero, norm_pow] at h2
    linarith
  · intro h n
    rw [iterate_qmap_zero, norm_pow]
    calc ‖z‖ ^ (2 ^ n) ≤ 1 ^ (2 ^ n) := pow_le_pow_left₀ (norm_nonneg z) h _
      _ = 1 := one_pow _
      _ ≤ R := le_of_lt hR

/-! ## Renormalization: the small filled Julia set sits inside the big one -/

/-- **Reduction for renormalization.**  If `f^[p] : U' → V'` is a
renormalization of `f` of period `p` (so that the first `p` iterates of `f`
map `U'` into `U`), then the filled Julia set of the renormalization is
contained in the filled Julia set of `f`. -/
