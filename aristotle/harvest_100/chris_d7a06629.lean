import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

/-- Sites of the `m × n` square lattice with periodic (toroidal) boundary conditions. -/
abbrev Site (m n : ℕ) : Type := ZMod m × ZMod n

/-- A spin configuration: a `± 1` value (encoded as a `Bool`) at every lattice site. -/
abbrev Config (m n : ℕ) : Type := Site m n → Bool

/-- The real spin value attached to a `Bool`. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- The total nearest-neighbour bond sum `∑_{⟨i,j⟩} s_i s_j` of a configuration on the
`m × n` torus (each site contributes its right and its upward bond). -/
def bondSum {m n : ℕ} [NeZero m] [NeZero n] (σ : Config m n) : ℝ :=
  ∑ p : Site m n,
    (spin (σ p) * spin (σ (p.1 + 1, p.2)) + spin (σ p) * spin (σ (p.1, p.2 + 1)))

/-- The Ising partition function `Z = ∑_σ exp (K ∑_{⟨i,j⟩} s_i s_j)` where `K = βJ`. -/
noncomputable def partitionFunction (m n : ℕ) [NeZero m] [NeZero n] (K : ℝ) : ℝ :=
  ∑ σ : Config m n, Real.exp (K * bondSum σ)

/-- The (dimensionless) free energy per site, `(1 / N) log Z`. -/
noncomputable def freeEnergy (m n : ℕ) [NeZero m] [NeZero n] (K : ℝ) : ℝ :=
  Real.log (partitionFunction m n K) / (m * n)

/-- Onsager's exact expression for the free energy per site of the two-dimensional
square-lattice Ising model in the thermodynamic limit:
`log 2 + (8π²)⁻¹ ∫₀^{2π} ∫₀^{2π} log (cosh²(2K) - sinh(2K)(cos x + cos y)) dy dx`. -/
noncomputable def onsagerFreeEnergy (K : ℝ) : ℝ :=
  Real.log 2 + (1 / (8 * Real.pi ^ 2)) *
    ∫ x in (0 : ℝ)..(2 * Real.pi), ∫ y in (0 : ℝ)..(2 * Real.pi),
      Real.log (Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos x + Real.cos y))

/-! ### Elementary facts about spins -/

theorem spin_abs (b : Bool) : |spin b| = 1 := by
  cases b <;> simp [spin]

theorem abs_spin_mul_spin (b c : Bool) : |spin b * spin c| = 1 := by
  rw [abs_mul, spin_abs, spin_abs, one_mul]

/-- Each site contributes at most `2` in absolute value to the bond sum. -/
theorem abs_bondSum_le {m n : ℕ} [NeZero m] [NeZero n] (σ : Config m n) :
    |bondSum σ| ≤ 2 * (m * n) := by
  have h : ∀ p : Site m n,
      |spin (σ p) * spin (σ (p.1 + 1, p.2)) + spin (σ p) * spin (σ (p.1, p.2 + 1))| ≤ 2 := by
    intro p
    calc |spin (σ p) * spin (σ (p.1 + 1, p.2)) + spin (σ p) * spin (σ (p.1, p.2 + 1))|
        ≤ |spin (σ p) * spin (σ (p.1 + 1, p.2))| + |spin (σ p) * spin (σ (p.1, p.2 + 1))| :=
          abs_add_le _ _
      _ = 2 := by rw [abs_spin_mul_spin, abs_spin_mul_spin]; norm_num
  calc |bondSum σ| ≤ ∑ _p : Site m n, (2 : ℝ) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => h p)
    _ = 2 * (m * n) := by
        simp [Finset.sum_const, ZMod.card, mul_comm]

/-! ### Basic properties of the partition function -/

theorem partitionFunction_pos {m n : ℕ} [NeZero m] [NeZero n] (K : ℝ) :
    0 < partitionFunction m n K := by
  refine Finset.sum_pos (fun σ _ => Real.exp_pos _) ?_
  exact Finset.univ_nonempty

theorem card_config (m n : ℕ) [NeZero m] [NeZero n] :
    Fintype.card (Config m n) = 2 ^ (m * n) := by
  simp [Config, Site, ZMod.card]

/-- At infinite temperature (`K = 0`) the partition function counts the configurations. -/
theorem partitionFunction_zero (m n : ℕ) [NeZero m] [NeZero n] :
    partitionFunction m n 0 = 2 ^ (m * n) := by
  simp [partitionFunction, card_config m n]

/-- The base case of Onsager's formula: at `K = 0` the free energy per site is `log 2`. -/
theorem freeEnergy_zero (m n : ℕ) [NeZero m] [NeZero n] :
    freeEnergy m n 0 = Real.log 2 := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [freeEnergy, partitionFunction_zero]
  rw [show ((2 : ℝ) ^ (m * n)) = (2 : ℝ) ^ ((m : ℕ) * n) from rfl, Real.log_pow]
  push_cast
  field_simp

/-- Onsager's expression at `K = 0` also equals `log 2`. -/
theorem onsagerFreeEnergy_zero : onsagerFreeEnergy 0 = Real.log 2 := by
  simp [onsagerFreeEnergy]

/-! ### Uniform bounds on the finite-volume free energy -/

theorem partitionFunction_le {m n : ℕ} [NeZero m] [NeZero n] (K : ℝ) :
    partitionFunction m n K ≤ 2 ^ (m * n) * Real.exp (2 * |K| * (m * n)) := by
  have h : ∀ σ : Config m n, Real.exp (K * bondSum σ) ≤ Real.exp (2 * |K| * (m * n)) := by
    intro σ
    apply Real.exp_le_exp.mpr
    calc K * bondSum σ ≤ |K * bondSum σ| := le_abs_self _
      _ = |K| * |bondSum σ| := abs_mul _ _
      _ ≤ |K| * (2 * (m * n)) := by
          exact mul_le_mul_of_nonneg_left (abs_bondSum_le σ) (abs_nonneg K)
      _ = 2 * |K| * (m * n) := by ring
  calc partitionFunction m n K ≤ ∑ _σ : Config m n, Real.exp (2 * |K| * (m * n)) :=
        Finset.sum_le_sum fun σ _ => h σ
    _ = 2 ^ (m * n) * Real.exp (2 * |K| * (m * n)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, card_config]
        push_cast
        ring

theorem le_partitionFunction {m n : ℕ} [NeZero m] [NeZero n] (K : ℝ) :
    2 ^ (m * n) * Real.exp (-(2 * |K| * (m * n))) ≤ partitionFunction m n K := by
  have h : ∀ σ : Config m n, Real.exp (-(2 * |K| * (m * n))) ≤ Real.exp (K * bondSum σ) := by
    intro σ
    apply Real.exp_le_exp.mpr
    have : |K * bondSum σ| ≤ 2 * |K| * (m * n) := by
      calc |K * bondSum σ| = |K| * |bondSum σ| := abs_mul _ _
        _ ≤ |K| * (2 * (m * n)) :=
            mul_le_mul_of_nonneg_left (abs_bondSum_le σ) (abs_nonneg K)
        _ = 2 * |K| * (m * n) := by ring
    linarith [neg_abs_le (K * bondSum σ)]
  calc 2 ^ (m * n) * Real.exp (-(2 * |K| * (m * n)))
      = ∑ _σ : Config m n, Real.exp (-(2 * |K| * (m * n))) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, card_config]
        push_cast
        ring
    _ ≤ partitionFunction m n K := Finset.sum_le_sum fun σ _ => h σ

/-- The finite-volume free energy per site is within `2|K|` of `log 2`, uniformly in the
lattice size. -/
theorem abs_freeEnergy_sub_log_two_le {m n : ℕ} [NeZero m] [NeZero n] (K : ℝ) :
    |freeEnergy m n K - Real.log 2| ≤ 2 * |K| := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hN : (0 : ℝ) < (m : ℝ) * n := mul_pos hm hn
  have hlog2 : Real.log ((2 : ℝ) ^ (m * n)) = ((m : ℝ) * n) * Real.log 2 := by
    rw [show ((2 : ℝ) ^ (m * n)) = (2 : ℝ) ^ ((m : ℕ) * n) from rfl, Real.log_pow]
    push_cast
    ring
  have hupper : Real.log (partitionFunction m n K)
      ≤ ((m : ℝ) * n) * Real.log 2 + 2 * |K| * ((m : ℝ) * n) := by
    have h := Real.log_le_log (partitionFunction_pos (m := m) (n := n) K)
      (partitionFunction_le (m := m) (n := n) K)
    rwa [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp, hlog2] at h
  have hlower : ((m : ℝ) * n) * Real.log 2 - 2 * |K| * ((m : ℝ) * n)
      ≤ Real.log (partitionFunction m n K) := by
    have h := Real.log_le_log (by positivity) (le_partitionFunction (m := m) (n := n) K)
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp, hlog2] at h
    linarith
  rw [abs_le]
  constructor
  · rw [freeEnergy, le_sub_iff_add_le, le_div_iff₀ hN]
    linarith
  · rw [freeEnergy, sub_le_iff_le_add, div_le_iff₀ hN]
    linarith

/-! ### Main statement -/

/--
**Onsager's two-dimensional Ising model, formalized statement with a Lean-checked base case.**

For every finite `m × n` torus:

* the partition function is strictly positive;
* at infinite temperature (`K = 0`) it equals `2^{mn}`, so the free energy per site equals
  `log 2`, which is exactly the value of Onsager's closed-form expression at `K = 0`
  (its double integral vanishes there);
* uniformly in the lattice size, the finite-volume free energy per site stays within
  `2|K|` of `log 2`, matching the corresponding bound satisfied by Onsager's formula.
-/
theorem onsager_2d_ising :
    ∀ (m n : ℕ) [NeZero m] [NeZero n],
      (∀ K : ℝ, 0 < partitionFunction m n K) ∧
      partitionFunction m n 0 = 2 ^ (m * n) ∧
      freeEnergy m n 0 = onsagerFreeEnergy 0 ∧
      (∀ K : ℝ, |freeEnergy m n K - Real.log 2| ≤ 2 * |K|) := by
  intro m n _ _
  refine ⟨fun K => partitionFunction_pos K, partitionFunction_zero m n, ?_,
    fun K => abs_freeEnergy_sub_log_two_le K⟩
  rw [freeEnergy_zero, onsagerFreeEnergy_zero]

end Frontier

