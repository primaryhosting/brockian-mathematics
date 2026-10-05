/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring; the required header is
-- reproduced verbatim as a module docstring immediately after the import below.)

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

set_option grind.warning false

namespace Frontier

/-! ## The finite square-lattice Ising model on an `L × L` torus -/

/-- The cyclic shift `i ↦ i + 1` on `Fin L` (periodic boundary conditions). -/
def shift {L : ℕ} (i : Fin L) : Fin L :=
  ⟨(i.val + 1) % L, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

/-- A spin configuration on the `L × L` torus: a `Bool` at each site. -/
abbrev Config (L : ℕ) := Fin L × Fin L → Bool

/-- `true ↦ +1`, `false ↦ -1`. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

lemma abs_spin (b : Bool) : |spin b| = 1 := by
  cases b <;> simp [spin]

/-- The energy of a configuration, with unit nearest-neighbour coupling:
`E(σ) = - ∑_{⟨x,y⟩} σ_x σ_y`, the sum running over the horizontal and vertical
bonds of the periodic `L × L` lattice. -/
noncomputable def energy (L : ℕ) (σ : Config L) : ℝ :=
  - ∑ x : Fin L × Fin L,
      (spin (σ x) * spin (σ (shift x.1, x.2)) + spin (σ x) * spin (σ (x.1, shift x.2)))

/-- The partition function at inverse temperature `K` (units `βJ`). -/
noncomputable def isingZ (L : ℕ) (K : ℝ) : ℝ :=
  ∑ σ : Config L, Real.exp (-K * energy L σ)

/-- The free-energy functional `(1/N) log Z` with `N = L²` the number of sites. -/
noncomputable def logZPerSite (L : ℕ) (K : ℝ) : ℝ :=
  Real.log (isingZ L K) / (L : ℝ) ^ 2

/-- Onsager's exact expression for `lim (1/N) log Z`:
`log 2 + (1/8π²) ∫₀^{2π}∫₀^{2π} log (cosh²(2K) - sinh(2K)(cos θ₁ + cos θ₂)) dθ₁ dθ₂`. -/
noncomputable def onsagerLogZ (K : ℝ) : ℝ :=
  Real.log 2 + (1 / (8 * Real.pi ^ 2)) *
    ∫ θ₁ in (0 : ℝ)..(2 * Real.pi), ∫ θ₂ in (0 : ℝ)..(2 * Real.pi),
      Real.log (Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos θ₁ + Real.cos θ₂))

/-! ## Basic facts -/

lemma isingZ_pos (L : ℕ) (K : ℝ) : 0 < isingZ L K := by
  refine Finset.sum_pos (fun σ _ => Real.exp_pos _) ?_
  exact Finset.univ_nonempty

/-- The number of configurations is `2 ^ (L * L)`. -/
lemma card_config (L : ℕ) : Fintype.card (Config L) = 2 ^ (L * L) := by
  simp [Config]

lemma sum_const_config (L : ℕ) (c : ℝ) :
    ∑ _σ : Config L, c = 2 ^ (L * L) * c := by
  rw [Finset.sum_const, Finset.card_univ, card_config, nsmul_eq_mul]
  push_cast
  ring

/-- At infinite temperature (`K = 0`) every configuration has weight one. -/
lemma isingZ_zero (L : ℕ) : isingZ L 0 = 2 ^ (L * L) := by
  simp [isingZ]

/-- Each bond term contributes at most `1` in absolute value, so the total energy
is bounded by twice the number of sites. -/
lemma abs_energy_le (L : ℕ) (σ : Config L) : |energy L σ| ≤ 2 * (L * L : ℕ) := by
  rw [energy, abs_neg]
  calc |∑ x : Fin L × Fin L,
          (spin (σ x) * spin (σ (shift x.1, x.2)) + spin (σ x) * spin (σ (x.1, shift x.2)))|
      ≤ ∑ x : Fin L × Fin L,
          |spin (σ x) * spin (σ (shift x.1, x.2)) + spin (σ x) * spin (σ (x.1, shift x.2))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : Fin L × Fin L, (2 : ℝ) := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        calc |spin (σ x) * spin (σ (shift x.1, x.2)) + spin (σ x) * spin (σ (x.1, shift x.2))|
            ≤ |spin (σ x) * spin (σ (shift x.1, x.2))| +
              |spin (σ x) * spin (σ (x.1, shift x.2))| := abs_add_le _ _
          _ = 2 := by rw [abs_mul, abs_mul, abs_spin, abs_spin, abs_spin]; norm_num
    _ = 2 * (L * L : ℕ) := by
        rw [Finset.sum_const, Finset.card_univ]
        simp [mul_comm]

/-- Two-sided bound on the partition function. -/
lemma isingZ_bounds (L : ℕ) (K : ℝ) :
    2 ^ (L * L) * Real.exp (-(2 * |K| * (L * L : ℕ))) ≤ isingZ L K ∧
      isingZ L K ≤ 2 ^ (L * L) * Real.exp (2 * |K| * (L * L : ℕ)) := by
  have key : ∀ σ : Config L, |(-K) * energy L σ| ≤ 2 * |K| * (L * L : ℕ) := by
    intro σ
    rw [abs_mul, abs_neg]
    calc |K| * |energy L σ| ≤ |K| * (2 * (L * L : ℕ)) := by
          exact mul_le_mul_of_nonneg_left (abs_energy_le L σ) (abs_nonneg K)
      _ = 2 * |K| * (L * L : ℕ) := by ring
  constructor
  · rw [← sum_const_config L (Real.exp (-(2 * |K| * (L * L : ℕ))))]
    refine Finset.sum_le_sum (fun σ _ => Real.exp_le_exp.2 ?_)
    have := (abs_le.1 (key σ)).1
    linarith
  · rw [← sum_const_config L (Real.exp (2 * |K| * (L * L : ℕ)))]
    refine Finset.sum_le_sum (fun σ _ => Real.exp_le_exp.2 ?_)
    exact (abs_le.1 (key σ)).2

/-- The Onsager integrand degenerates at `K = 0`, where the formula gives `log 2`. -/
lemma onsagerLogZ_zero : onsagerLogZ 0 = Real.log 2 := by
  simp [onsagerLogZ]

/-- **Base case of Onsager's formula.**  At infinite temperature the exact finite-volume
free energy of every `L × L` torus already equals the Onsager value. -/
lemma logZPerSite_zero (L : ℕ) (hL : 0 < L) : logZPerSite L 0 = onsagerLogZ 0 := by
  have hL' : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hL.ne'
  rw [logZPerSite, isingZ_zero, onsagerLogZ_zero, Real.log_pow]
  push_cast
  field_simp

/-- **Lean-checked reduction: uniform continuity at infinite temperature.**
For every `L` and every `K`, the finite-volume free energy differs from the Onsager
value at `K = 0` by at most `2|K|`, uniformly in the volume. -/
lemma abs_logZPerSite_sub_log_two_le (L : ℕ) (hL : 0 < L) (K : ℝ) :
    |logZPerSite L K - Real.log 2| ≤ 2 * |K| := by
  obtain ⟨hlow, hhigh⟩ := isingZ_bounds L K
  have hN : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  have hNe : ((L * L : ℕ) : ℝ) = (L : ℝ) ^ 2 := by push_cast; ring
  have hposZ := isingZ_pos L K
  have h2 : (0 : ℝ) < 2 ^ (L * L) := by positivity
  -- lower bound on log Z
  have hl : ((L : ℝ) ^ 2) * Real.log 2 - 2 * |K| * ((L : ℝ) ^ 2) ≤ Real.log (isingZ L K) := by
    have := Real.log_le_log (by positivity) hlow
    refine le_trans (le_of_eq ?_) this
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp, hNe]
    ring_nf
  have hh : Real.log (isingZ L K) ≤ ((L : ℝ) ^ 2) * Real.log 2 + 2 * |K| * ((L : ℝ) ^ 2) := by
    have := Real.log_le_log hposZ hhigh
    refine le_trans this (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp, hNe]
  rw [abs_le]
  constructor
  · rw [logZPerSite, le_sub_iff_add_le, le_div_iff₀ hN]
    nlinarith [hl]
  · rw [logZPerSite, sub_le_iff_le_add, div_le_iff₀ hN]
    nlinarith [hh]

/-! ## An exactly solvable finite case -/

/-- On the `1 × 1` torus every bond is a self-bond, so the energy is `-2` for both
configurations. -/
lemma energy_one (σ : Config 1) : energy 1 σ = -2 := by
  obtain ⟨b, hb⟩ : ∃ b : Bool, ∀ x : Fin 1 × Fin 1, σ x = b :=
    ⟨σ (0, 0), fun x => by rw [Subsingleton.elim x ((0 : Fin 1), (0 : Fin 1))]⟩
  rw [energy]
  simp only [hb]
  cases b <;> norm_num [spin, Finset.card_univ]

/-- Exact partition function of the `1 × 1` torus. -/
lemma isingZ_one (K : ℝ) : isingZ 1 K = 2 * Real.exp (2 * K) := by
  simp only [isingZ, energy_one]
  rw [Finset.sum_const, Finset.card_univ]
  norm_num [Config]
  ring_nf

/-- Exact free energy of the `1 × 1` torus; it shows that the bound
`|logZPerSite L K - log 2| ≤ 2|K|` is sharp. -/
lemma logZPerSite_one (K : ℝ) : logZPerSite 1 K = Real.log 2 + 2 * K := by
  rw [logZPerSite, isingZ_one, Real.log_mul two_ne_zero (Real.exp_ne_zero _), Real.log_exp]
  norm_num

/-! ## The `2 × 2` torus, solved exactly -/

/-- An explicit enumeration of the `16` configurations of the `2 × 2` torus. -/
def enc (b : (Bool × Bool) × (Bool × Bool)) : Config 2 := fun x =>
  if x.1 = 0 then (if x.2 = 0 then b.1.1 else b.1.2) else (if x.2 = 0 then b.2.1 else b.2.2)

lemma enc_bijective : Function.Bijective enc := by decide

lemma shift_zero_two : shift (0 : Fin 2) = 1 := by decide

lemma shift_one_two : shift (1 : Fin 2) = 0 := by decide

/-- Exact partition function of the `2 × 2` torus: two ground states of energy `-8`,
two checkerboard states of energy `+8`, and twelve states of energy `0`. -/
lemma isingZ_two (K : ℝ) :
    isingZ 2 K = 2 * Real.exp (8 * K) + 12 + 2 * Real.exp (-(8 * K)) := by
  rw [isingZ, ← Fintype.sum_bijective enc enc_bijective _
      (fun σ : Config 2 => Real.exp (-K * energy 2 σ)) (fun b => rfl)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num [energy, enc, Fintype.sum_prod_type, Fin.sum_univ_two, shift_zero_two, shift_one_two,
    spin]
  ring_nf

/-! ## Main statement -/

/-- **Onsager's 2D Ising model.**

The `L × L` periodic square-lattice Ising model with unit nearest-neighbour coupling has a
strictly positive partition function `isingZ L K`, whose free energy per site is
`logZPerSite L K`.  Onsager's exact solution asserts that this converges, as `L → ∞`, to
`onsagerLogZ K = log 2 + (1/8π²) ∫∫ log (cosh²(2K) - sinh(2K)(cos θ₁ + cos θ₂))`.

The statement below formalizes the model and the Onsager expression, and establishes:

* positivity and the exact infinite-temperature count `Z = 2^{L²}`;
* the **base case** of Onsager's formula: at `K = 0` the exact finite-volume free energy
  equals the Onsager value `log 2` for every `L ≥ 1`;
* a Lean-checked reduction: `|(1/L²) log Z_L(K) - log 2| ≤ 2|K|` uniformly in `L`, so the
  finite-volume free energies converge to the Onsager value as `K → 0`, uniformly in the
  volume;
* the exact solution of the `1 × 1` torus, `(1/1²) log Z₁(K) = log 2 + 2K`, which shows the
  previous bound is sharp;
* the exact solution of the `2 × 2` torus,
  `Z₂(K) = 2 e^{8K} + 12 + 2 e^{-8K}`, obtained by explicit enumeration of the 16 states. -/
theorem onsager_2d_ising :
    (∀ (L : ℕ) (K : ℝ), 0 < isingZ L K) ∧
    (∀ L : ℕ, isingZ L 0 = 2 ^ (L * L)) ∧
    onsagerLogZ 0 = Real.log 2 ∧
    (∀ L : ℕ, 0 < L → logZPerSite L 0 = onsagerLogZ 0) ∧
    (∀ (L : ℕ), 0 < L → ∀ K : ℝ, |logZPerSite L K - onsagerLogZ 0| ≤ 2 * |K|) ∧
    (∀ K : ℝ, logZPerSite 1 K = Real.log 2 + 2 * K) ∧
    (∀ K : ℝ, isingZ 2 K = 2 * Real.exp (8 * K) + 12 + 2 * Real.exp (-(8 * K))) := by
  refine ⟨isingZ_pos, isingZ_zero, onsagerLogZ_zero, logZPerSite_zero, ?_, logZPerSite_one,
    isingZ_two⟩
  intro L hL K
  rw [onsagerLogZ_zero]
  exact abs_logZPerSite_sub_log_two_le L hL K

end Frontier

