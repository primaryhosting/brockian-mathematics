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

/-!
## The finite-volume Ising model

We set up the ferromagnetic Ising model on a finite graph `G` at inverse temperature `β`
with external field `h`: spins `σ : V → Bool` with values `spinVal (σ x) ∈ {-1, +1}`,
Gibbs weights `exp (-β * energy + h * ∑ spins)`, and the associated expectations,
two-point functions and magnetisation.
-/

section IsingFinite

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The spin value `±1` attached to a Boolean spin variable. -/

theorem exp_decay_of_recursive_bound (a : ℕ → ℝ) (L : ℕ) (hL : 0 < L) (c : ℝ) (hc1 : c < 1)
    (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1) (hrec : ∀ n, a (n + L) ≤ c * a n) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ n : ℕ, a n ≤ C * Real.exp (-α * n) := by
  set c' : ℝ := max c (1 / 2) with hc'def
  have hc'pos : 0 < c' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hc'lt : c' < 1 := max_lt hc1 (by norm_num)
  have hcc' : c ≤ c' := le_max_left _ _
  have hrec' : ∀ n, a (n + L) ≤ c' * a n := fun n =>
    le_trans (hrec n) (mul_le_mul_of_nonneg_right hcc' (ha0 n))
  have hpow : ∀ n, a n ≤ c' ^ (n / L) :=
    le_pow_div_of_recursive_bound a L hL c' hc'pos.le ha1 hrec'
  have hlog : Real.log c' < 0 := Real.log_neg hc'pos hc'lt
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  refine ⟨1 / c', -Real.log c' / L, by positivity,
    div_pos (neg_pos.mpr hlog) hLR, fun n => ?_⟩
  -- key: `c' ^ (n / L + 1) ≤ exp (-α n)`
  have hnle : (n : ℝ) / (L : ℝ) ≤ ((n / L : ℕ) : ℝ) + 1 := by
    have hn : n < (n / L + 1) * L := by
      have hmod := Nat.div_add_mod n L
      have hltm := Nat.mod_lt n hL
      calc n = L * (n / L) + n % L := hmod.symm
        _ < L * (n / L) + L := by omega
        _ = (n / L + 1) * L := by ring
    have : (n : ℝ) < ((n / L : ℕ) + 1) * (L : ℝ) := by exact_mod_cast hn
    rw [div_le_iff₀ hLR]
    linarith
  have hexp : c' ^ (n / L + 1) ≤ Real.exp (-(-Real.log c' / L) * n) := by
    have h1 : c' ^ (n / L + 1) = Real.exp (((n / L : ℕ) + 1 : ℕ) * Real.log c') := by
      rw [Real.exp_nat_mul, Real.exp_log hc'pos]
    rw [h1]
    apply Real.exp_le_exp.mpr
    have h2 : ((((n / L : ℕ) + 1 : ℕ) : ℝ)) * Real.log c' ≤ ((n : ℝ) / L) * Real.log c' := by
      have := mul_le_mul_of_nonpos_right hnle hlog.le
      push_cast
      push_cast at this
      linarith
    have h3 : ((n : ℝ) / L) * Real.log c' = -(-Real.log c' / L) * n := by
      field_simp
    linarith [h2, h3]
  calc a n ≤ c' ^ (n / L) := hpow n
    _ = (1 / c') * c' ^ (n / L + 1) := by
        field_simp [pow_succ]
        ring
    _ ≤ (1 / c') * Real.exp (-(-Real.log c' / L) * n) := by
        exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- **Supercritical lower bound on the magnetisation.** This is the analytic core of the
supercritical half of sharpness: the Duminil-Copin–Tassion differential inequality
`∂_β M ≥ (1 - M) / β` for `β > β_c` integrates to the mean-field-type lower bound
`M (β) ≥ (β - β_c) / β`, in particular `M (β) > 0` strictly above `β_c`. -/
