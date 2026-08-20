/-
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
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

/-! ## The finite-volume Ising model -/

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The real spin value `±1` attached to a Boolean spin variable. -/

theorem exp_decay_of_geometric (θ : ℕ → ℝ) (hnn : ∀ n, 0 ≤ θ n) (hle : ∀ n, θ n ≤ 1)
    (L : ℕ) (hL : 1 ≤ L) (c : ℝ) (hc1 : c < 1)
    (hstep : ∀ n, θ (n + L) ≤ c * θ n) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧ ∀ n, θ n ≤ C * Real.exp (-a * n) := by
  set c' : ℝ := max c (1/2) with hc'
  have hc'pos : 0 < c' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hc'1 : c' < 1 := max_lt hc1 (by norm_num)
  have hstep' : ∀ n, θ (n + L) ≤ c' * θ n := fun n =>
    (hstep n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hnn n))
  have hpow : ∀ q r : ℕ, θ (r + q * L) ≤ c' ^ q := by
    intro q
    induction q with
    | zero => intro r; simpa using hle r
    | succ q ih =>
      intro r
      have hrw : r + (q + 1) * L = (r + q * L) + L := by ring
      rw [hrw]
      calc θ ((r + q * L) + L) ≤ c' * θ (r + q * L) := hstep' _
        _ ≤ c' * c' ^ q := mul_le_mul_of_nonneg_left (ih r) (le_of_lt hc'pos)
        _ = c' ^ (q + 1) := by ring
  have hlogneg : Real.log c' < 0 := Real.log_neg hc'pos hc'1
  have hLpos : (0:ℝ) < L := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hL
  refine ⟨1 / c', -Real.log c' / L, by positivity, div_pos (by linarith) hLpos, ?_⟩
  intro n
  have hn : n % L + (n / L) * L = n := Nat.mod_add_div' n L
  have h1 : θ n ≤ c' ^ (n / L) := by
    have h := hpow (n / L) (n % L)
    rwa [hn] at h
  have h2 : c' ^ (n / L) = Real.exp ((n / L : ℕ) * Real.log c') := by
    rw [Real.exp_nat_mul, Real.exp_log hc'pos]
  have hq : (n:ℝ) / L - 1 ≤ ((n / L : ℕ) : ℝ) := by
    have hmod : n % L < L := Nat.mod_lt _ (by omega)
    have hlt : n < (n / L) * L + L := by omega
    have hlt' : (n:ℝ) < ((n / L : ℕ) : ℝ) * L + L := by exact_mod_cast hlt
    rw [sub_le_iff_le_add, div_le_iff₀ hLpos]
    nlinarith
  have h3 : ((n / L : ℕ) : ℝ) * Real.log c' ≤ ((n:ℝ)/L - 1) * Real.log c' :=
    mul_le_mul_of_nonpos_right hq (le_of_lt hlogneg)
  have key : Real.exp (((n:ℝ)/L - 1) * Real.log c')
      = 1 / c' * Real.exp (-(-Real.log c' / L) * n) := by
    rw [show (-(-Real.log c'/(L:ℝ)) * n) = ((n:ℝ)/L) * Real.log c' by ring,
      sub_mul, one_mul, Real.exp_sub, Real.exp_log hc'pos]
    ring
  calc θ n ≤ Real.exp ((n / L : ℕ) * Real.log c') := by rw [← h2]; exact h1
    _ ≤ Real.exp (((n:ℝ)/L - 1) * Real.log c') := Real.exp_le_exp.mpr h3
    _ = 1 / c' * Real.exp (-(-Real.log c' / L) * n) := key

/-- **Supercritical reduction.** A magnetization vanishing at `βc`, continuous on
`[βc, ∞)` and with derivative at least `c₀` above `βc`, obeys the mean-field type
lower bound `M β ≥ c₀ (β - βc)`.

The analytic core is the Mathlib mean-value estimate
`Convex.mul_sub_le_image_sub_of_le_deriv`. -/
