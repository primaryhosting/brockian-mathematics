import Mathlib

/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open MeasureTheory Filter Metric Set

/-- A point `x` is an *energy concentration point* (a *bubble point*) at level `eps`
for a sequence of energy measures `mu n` (think: `mu n = |F_{A n}|² dvol`, the Yang–Mills
energy density of a sequence of connections `A n`) if on *every* ball around `x` the
asymptotic energy is at least `eps`. -/

theorem nat_mul_le_of_forall_lt (k : ℕ) (x y : ℝ≥0∞) (h : ∀ c < x, (k : ℝ≥0∞) * c ≤ y) :
    (k : ℝ≥0∞) * x ≤ y := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rcases eq_or_ne y ⊤ with rfl | hy
  · simp
  by_contra hcon
  push_neg at hcon
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  have hkt : (k : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top k
  have hlt : y / (k : ℝ≥0∞) < x := by
    rw [ENNReal.div_lt_iff (Or.inl hk0) (Or.inl hkt)]
    rwa [mul_comm] at hcon
  obtain ⟨c, hc1, hc2⟩ := exists_between hlt
  have hle := h c hc2
  have hmul : y < (k : ℝ≥0∞) * c := by
    calc y = (k : ℝ≥0∞) * (y / k) := (ENNReal.mul_div_cancel hk0 hkt).symm
      _ < (k : ℝ≥0∞) * c := ENNReal.mul_lt_mul_right hk0 hkt hc1
  exact absurd hle (not_le.2 hmul)

/-- **Energy counting bound.** Any finite set of bubble points at level `eps` for a
sequence of energy measures of total mass at most `Lam` satisfies `#S * eps ≤ Lam`. -/
