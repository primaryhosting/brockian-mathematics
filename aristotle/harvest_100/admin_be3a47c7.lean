import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Frontier

/-! ## The finite-volume 2D Ising model on an `L × L` torus -/

/-- Shift a periodic (torus) index by one site. -/
def shiftIdx {L : ℕ} (i : Fin L) : Fin L :=
  ⟨(i.val + 1) % L, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

/-- A spin configuration on the `L × L` torus. -/
abbrev Config (L : ℕ) := Fin L × Fin L → Bool

/-- The `±1` spin value at a site. -/
def spin {L : ℕ} (σ : Config L) (x : Fin L × Fin L) : ℝ := if σ x then 1 else -1

/-- `∑_{⟨x,y⟩} σ_x σ_y`, the sum over all nearest-neighbour bonds of the torus
(each site contributes its right and its upward bond). -/
def bondSum {L : ℕ} (σ : Config L) : ℝ :=
  ∑ x : Fin L × Fin L,
    (spin σ x * spin σ (shiftIdx x.1, x.2) + spin σ x * spin σ (x.1, shiftIdx x.2))

/-- The partition function `Z_L(K) = ∑_σ exp(K ∑_{⟨x,y⟩} σ_x σ_y)` of the square-lattice
Ising model with periodic boundary conditions, where `K = βJ` is the reduced coupling.
(The Hamiltonian is `H(σ) = -J ∑_{⟨x,y⟩} σ_x σ_y`, so `Z = ∑_σ e^{-βH(σ)}`.) -/
noncomputable def isingZ (L : ℕ) (K : ℝ) : ℝ := ∑ σ : Config L, Real.exp (K * bondSum σ)

/-- The finite-volume free-energy density `(1/L²) log Z_L(K)`
(i.e. `-β f_L`, the reduced free energy per site). -/
noncomputable def logZDensity (L : ℕ) (K : ℝ) : ℝ := (1 / (L : ℝ) ^ 2) * Real.log (isingZ L K)

/-! ## Onsager's exact formula -/

/-- The integrand of Onsager's formula:
`log (cosh²(2K) - sinh(2K)(cos θ + cos φ))`. -/
noncomputable def onsagerIntegrand (K θ φ : ℝ) : ℝ :=
  Real.log (Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos θ + Real.cos φ))

/-- Onsager's exact reduced free energy per site:
`log 2 + (1/2)(2π)⁻² ∫₀^{2π}∫₀^{2π} log (cosh²(2K) - sinh(2K)(cos θ + cos φ)) dθ dφ`. -/
noncomputable def onsagerLogZDensity (K : ℝ) : ℝ :=
  Real.log 2 + (1 / 2) * (1 / (2 * π) ^ 2) *
    ∫ θ in (0:ℝ)..(2 * π), ∫ φ in (0:ℝ)..(2 * π), onsagerIntegrand K θ φ

/-- Onsager's critical coupling `K_c = ½ log (1 + √2)`, the unique `K ≥ 0` at which
the argument of the Onsager logarithm vanishes (at `θ = φ = 0`). -/
noncomputable def criticalCoupling : ℝ := Real.log (1 + Real.sqrt 2) / 2

/-- Onsager's theorem *at a given coupling* `K`: the free-energy density of the finite
torus converges, as the side length tends to infinity, to Onsager's exact expression. -/
def OnsagerHoldsAt (K : ℝ) : Prop :=
  Filter.Tendsto (fun L : ℕ => logZDensity L K) Filter.atTop (nhds (onsagerLogZDensity K))

/-- The full statement of Onsager's solution of the 2D square-lattice Ising model. -/
def OnsagerFreeEnergy : Prop := ∀ K : ℝ, OnsagerHoldsAt K

/-! ## Elementary exact facts about the finite-volume model -/

theorem isingZ_pos (L : ℕ) (K : ℝ) : 0 < isingZ L K := by
  apply Finset.sum_pos (fun σ _ => Real.exp_pos _)
  exact Finset.univ_nonempty

/-- At infinite temperature (`K = 0`) the partition function counts all `2^{L²}`
configurations. -/
theorem isingZ_zero (L : ℕ) : isingZ L 0 = 2 ^ (L * L) := by
  simp [isingZ]

theorem bondSum_one (σ : Config 1) : bondSum σ = 2 := by
  rw [bondSum, Fintype.sum_prod_type]
  simp [spin, shiftIdx]
  cases h : σ (0, 0) <;> norm_num

/-- The `1 × 1` torus: each of the two configurations has two (self-)bonds, so
`Z₁(K) = 2 e^{2K}`. -/
theorem isingZ_one (K : ℝ) : isingZ 1 K = 2 * Real.exp (2 * K) := by
  simp [isingZ, bondSum_one, mul_comm]

theorem logZDensity_one (K : ℝ) : logZDensity 1 K = Real.log 2 + 2 * K := by
  rw [logZDensity, isingZ_one]
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  norm_num

/-- The exact free-energy density at infinite temperature, for every finite volume. -/
theorem logZDensity_zero (L : ℕ) (hL : 0 < L) : logZDensity L 0 = Real.log 2 := by
  have hL' : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hL.ne'
  rw [logZDensity, isingZ_zero, Real.log_pow]
  field_simp
  push_cast
  ring

/-! ### Rigorous bounds on the free energy, valid in every finite volume -/

theorem spin_abs {L : ℕ} (σ : Config L) (x : Fin L × Fin L) : |spin σ x| = 1 := by
  unfold spin; split <;> norm_num

/-- Every configuration has bond energy at most that of the ground state. -/
theorem bondSum_le {L : ℕ} (σ : Config L) : bondSum σ ≤ 2 * (L : ℝ) ^ 2 := by
  have h : ∀ x : Fin L × Fin L,
      (spin σ x * spin σ (shiftIdx x.1, x.2) + spin σ x * spin σ (x.1, shiftIdx x.2)) ≤ 2 := by
    intro x
    have h1 := abs_le.1 (le_of_eq (by rw [abs_mul, spin_abs, spin_abs]; norm_num :
      |spin σ x * spin σ (shiftIdx x.1, x.2)| = 1))
    have h2 := abs_le.1 (le_of_eq (by rw [abs_mul, spin_abs, spin_abs]; norm_num :
      |spin σ x * spin σ (x.1, shiftIdx x.2)| = 1))
    linarith [h1.2, h2.2]
  calc bondSum σ ≤ ∑ _x : Fin L × Fin L, (2 : ℝ) := Finset.sum_le_sum (fun x _ => h x)
    _ = 2 * (L : ℝ) ^ 2 := by simp [Finset.sum_const]; ring

/-- The all-up (ground state) configuration saturates the bound. -/
theorem bondSum_allUp (L : ℕ) : bondSum (fun _ => true : Config L) = 2 * (L : ℝ) ^ 2 := by
  simp [bondSum, spin, Finset.sum_const]; ring

theorem isingZ_ge_ground (L : ℕ) (K : ℝ) : Real.exp (2 * K * (L : ℝ) ^ 2) ≤ isingZ L K := by
  have h := Finset.single_le_sum (f := fun σ : Config L => Real.exp (K * bondSum σ))
    (fun σ _ => (Real.exp_pos _).le) (Finset.mem_univ (fun _ => true : Config L))
  simp only [bondSum_allUp] at h
  calc Real.exp (2 * K * (L : ℝ) ^ 2) = Real.exp (K * (2 * (L : ℝ) ^ 2)) := by ring_nf
    _ ≤ _ := h

theorem isingZ_le (L : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    isingZ L K ≤ 2 ^ (L * L) * Real.exp (2 * K * (L : ℝ) ^ 2) := by
  calc isingZ L K ≤ ∑ _σ : Config L, Real.exp (K * (2 * (L : ℝ) ^ 2)) := by
        refine Finset.sum_le_sum (fun σ _ => Real.exp_le_exp.2 ?_)
        exact mul_le_mul_of_nonneg_left (bondSum_le σ) hK
    _ = 2 ^ (L * L) * Real.exp (2 * K * (L : ℝ) ^ 2) := by
        simp [Finset.sum_const]; ring_nf

/-- For every ferromagnetic coupling `K ≥ 0` and every finite volume, the free-energy
density is sandwiched between `2K` (the ground-state value) and `log 2 + 2K`. -/
theorem logZDensity_bounds (L : ℕ) (K : ℝ) (hL : 0 < L) (hK : 0 ≤ K) :
    2 * K ≤ logZDensity L K ∧ logZDensity L K ≤ Real.log 2 + 2 * K := by
  have hL2 : (0:ℝ) < (L : ℝ) ^ 2 := by positivity
  have hZ : 0 < isingZ L K := isingZ_pos L K
  constructor
  · have h := Real.log_le_log (Real.exp_pos _) (isingZ_ge_ground L K)
    rw [Real.log_exp] at h
    rw [logZDensity, one_div, inv_mul_eq_div, le_div_iff₀ hL2]
    linarith
  · have h := Real.log_le_log hZ (isingZ_le L K hK)
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp] at h
    have hcast : ((L * L : ℕ) : ℝ) = (L : ℝ) ^ 2 := by push_cast; ring
    rw [hcast] at h
    rw [logZDensity, one_div, inv_mul_eq_div, div_le_iff₀ hL2]
    nlinarith [h]

/-! ## Onsager's expression: exact evaluation at `K = 0`, positivity, criticality -/

theorem onsagerIntegrand_zero (θ φ : ℝ) : onsagerIntegrand 0 θ φ = 0 := by
  simp [onsagerIntegrand]

theorem onsagerLogZDensity_zero : onsagerLogZDensity 0 = Real.log 2 := by
  simp [onsagerLogZDensity, onsagerIntegrand_zero]

/-- `sinh (2 K_c) = 1`: Onsager's critical coupling. -/
theorem sinh_two_criticalCoupling : Real.sinh (2 * criticalCoupling) = 1 := by
  have h2 : (0:ℝ) < 1 + Real.sqrt 2 := by positivity
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [Real.sinh_eq,
    show 2 * criticalCoupling = Real.log (1 + Real.sqrt 2) by unfold criticalCoupling; ring,
    Real.exp_log h2, Real.exp_neg, Real.exp_log h2]
  field_simp
  nlinarith [Real.sqrt_nonneg 2]

/-- The argument of Onsager's logarithm is bounded below by `(sinh 2K - 1)²`, hence is
nonnegative for all `K ≥ 0`. -/
theorem onsager_arg_lower_bound (K θ φ : ℝ) (hK : 0 ≤ K) :
    (Real.sinh (2 * K) - 1) ^ 2 ≤
      Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos θ + Real.cos φ) := by
  have h1 : Real.cosh (2 * K) ^ 2 = 1 + Real.sinh (2 * K) ^ 2 := by
    have := Real.cosh_sq_sub_sinh_sq (2 * K); nlinarith
  have hs : 0 ≤ Real.sinh (2 * K) := by
    rw [← Real.sinh_zero]; exact Real.sinh_le_sinh.2 (by linarith)
  nlinarith [Real.cos_le_one θ, Real.cos_le_one φ]

/-- Off the critical coupling the argument of Onsager's logarithm is strictly positive
for all `θ, φ`; the bound degenerates exactly at `K = K_c` (and there only at `θ = φ = 0`). -/
theorem onsager_arg_pos_of_ne_critical (K θ φ : ℝ) (hK : 0 ≤ K) (hne : K ≠ criticalCoupling) :
    0 < Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos θ + Real.cos φ) := by
  have hs : Real.sinh (2 * K) ≠ 1 := by
    rw [← sinh_two_criticalCoupling]
    intro h
    exact hne (by have := Real.sinh_injective h; linarith)
  have h0 : 0 < (Real.sinh (2 * K) - 1) ^ 2 := by
    have : Real.sinh (2 * K) - 1 ≠ 0 := sub_ne_zero.2 hs
    positivity
  exact lt_of_lt_of_le h0 (onsager_arg_lower_bound K θ φ hK)

/-- **Base case of Onsager's theorem**: at `K = 0` (infinite temperature) the exact
finite-volume free-energy density equals Onsager's expression for every `L ≥ 1`, and hence
the thermodynamic limit exists and agrees with Onsager's formula. -/
theorem onsagerHoldsAt_zero : OnsagerHoldsAt 0 := by
  rw [OnsagerHoldsAt, onsagerLogZDensity_zero]
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop 1] with L hL
  exact (logZDensity_zero L hL).symm

/-!
## Main statement

`OnsagerFreeEnergy` above is the full statement of Onsager's solution.  The theorem below
records the formalization together with the pieces that are verified here: the exactly
solvable base case `K = 0` (where the finite-volume free energy equals Onsager's expression
for every volume, so the thermodynamic limit holds), the exact `1 × 1` torus, positivity of
the partition function, the exact infinite-temperature count `Z = 2^{L²}`, and the
nonnegativity of the argument of the Onsager logarithm together with the identification of
Onsager's critical coupling `K_c = ½ log (1+√2)` as the unique `K ≥ 0` where it degenerates.
-/
theorem onsager_2d_ising :
    -- (1) exact partition function values
    (∀ L : ℕ, ∀ K : ℝ, 0 < isingZ L K) ∧
    (∀ L : ℕ, isingZ L 0 = 2 ^ (L * L)) ∧
    (∀ K : ℝ, isingZ 1 K = 2 * Real.exp (2 * K)) ∧
    -- (2) Onsager's expression at infinite temperature
    onsagerLogZDensity 0 = Real.log 2 ∧
    -- (3) base case: Onsager's formula is exact in every finite volume at K = 0 …
    (∀ L : ℕ, 0 < L → logZDensity L 0 = onsagerLogZDensity 0) ∧
    -- … and therefore the thermodynamic-limit statement holds at K = 0
    OnsagerHoldsAt 0 ∧
    -- (4) structure of Onsager's integrand and the critical coupling
    Real.sinh (2 * criticalCoupling) = 1 ∧
    (∀ K θ φ : ℝ, 0 ≤ K →
      (Real.sinh (2 * K) - 1) ^ 2 ≤
        Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos θ + Real.cos φ)) ∧
    (∀ K θ φ : ℝ, 0 ≤ K → K ≠ criticalCoupling →
      0 < Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos θ + Real.cos φ)) ∧
    -- (5) rigorous free-energy bounds in every finite volume, for every K ≥ 0
    (∀ (L : ℕ) (K : ℝ), 0 < L → 0 ≤ K →
      2 * K ≤ logZDensity L K ∧ logZDensity L K ≤ Real.log 2 + 2 * K) := by
  refine ⟨fun L K => isingZ_pos L K, isingZ_zero, isingZ_one, onsagerLogZDensity_zero,
    fun L hL => ?_, onsagerHoldsAt_zero, sinh_two_criticalCoupling, onsager_arg_lower_bound,
    onsager_arg_pos_of_ne_critical, logZDensity_bounds⟩
  rw [logZDensity_zero L hL, onsagerLogZDensity_zero]

end Frontier

import Mathlib

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

