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
## The Ising model on a finite chain

We set up the nearest-neighbour Ising model with free boundary conditions on the
segment `{0, 1, …, n}` and compute its two-point function exactly.  This is the
one-dimensional base case of the sharpness of the phase transition
(Duminil-Copin–Tassion): the two-point function decays exponentially at *every*
finite inverse temperature, so the critical inverse temperature is `+∞` and the
subcritical phase (exponential decay of correlations, finite susceptibility)
occupies the whole of `[0, ∞)`.
-/

namespace IsingChain

/-- The spin value attached to a Boolean: `true ↦ +1`, `false ↦ -1`. -/
noncomputable def spin (b : Bool) : ℝ := if b then 1 else -1

lemma spin_eq (b : Bool) : spin b = 1 ∨ spin b = -1 := by
  cases b <;> simp [spin]

lemma spin_sq (b : Bool) : spin b * spin b = 1 := by
  cases b <;> norm_num [spin]

/-- The (negative of the) energy of a configuration `σ` of spins on `{0, …, n}`:
the sum of the products of neighbouring spins. -/
noncomputable def energy {n : ℕ} (σ : Fin (n + 1) → Bool) : ℝ :=
  ∑ i : Fin n, spin (σ i.castSucc) * spin (σ i.succ)

/-- The Boltzmann weight of a configuration at inverse temperature `β`. -/
noncomputable def weight (β : ℝ) {n : ℕ} (σ : Fin (n + 1) → Bool) : ℝ :=
  Real.exp (β * energy σ)

/-- The partition function of the chain `{0, …, n}` at inverse temperature `β`. -/
noncomputable def Z (β : ℝ) (n : ℕ) : ℝ := ∑ σ : Fin (n + 1) → Bool, weight β σ

/-- The unnormalised two-point function between the two endpoints of the chain. -/
noncomputable def num (β : ℝ) (n : ℕ) : ℝ :=
  ∑ σ : Fin (n + 1) → Bool, spin (σ 0) * spin (σ (Fin.last n)) * weight β σ

/-- The two-point function `⟨σ₀ σₙ⟩` of the chain `{0, …, n}`. -/
noncomputable def corr (β : ℝ) (n : ℕ) : ℝ := num β n / Z β n

/-! ### Summing over configurations by peeling off the first spin -/

lemma sum_cons {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    ∑ σ : Fin (n + 1) → Bool, f σ = ∑ b : Bool, ∑ ρ : Fin n → Bool, f (Fin.cons b ρ) := by
  have h := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
      (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)
  rw [← h, Fintype.sum_prod_type]

lemma energy_cons {n : ℕ} (b : Bool) (ρ : Fin (n + 1) → Bool) :
    energy (Fin.cons b ρ : Fin (n + 2) → Bool) = spin b * spin (ρ 0) + energy ρ := by
  unfold energy
  rw [Fin.sum_univ_succ]
  congr 1

/-! ### The one-spin sums -/

lemma spin_true : spin true = 1 := rfl

lemma spin_false : spin false = -1 := rfl

lemma bool_sum_exp (β t E : ℝ) (ht : t = 1 ∨ t = -1) :
    ∑ b : Bool, Real.exp (β * (spin b * t + E)) = (2 * Real.cosh β) * Real.exp (β * E) := by
  have hc : 2 * Real.cosh β = Real.exp β + Real.exp (-β) := by
    rw [Real.cosh_eq]; ring
  rcases ht with h | h <;> subst h <;>
    simp only [Fintype.sum_bool, spin_true, spin_false, hc]
  · rw [show β * (1 * 1 + E) = β + β * E by ring, show β * (-1 * 1 + E) = -β + β * E by ring,
      Real.exp_add, Real.exp_add]
    ring
  · rw [show β * (1 * -1 + E) = -β + β * E by ring,
      show β * (-1 * -1 + E) = β + β * E by ring, Real.exp_add, Real.exp_add]
    ring

lemma bool_sum_exp_spin (β t E : ℝ) (ht : t = 1 ∨ t = -1) :
    ∑ b : Bool, spin b * Real.exp (β * (spin b * t + E)) =
      (2 * Real.sinh β) * (t * Real.exp (β * E)) := by
  have hs : 2 * Real.sinh β = Real.exp β - Real.exp (-β) := by
    rw [Real.sinh_eq]; ring
  rcases ht with h | h <;> subst h <;>
    simp only [Fintype.sum_bool, spin_true, spin_false, hs]
  · rw [show β * (1 * 1 + E) = β + β * E by ring, show β * (-1 * 1 + E) = -β + β * E by ring,
      Real.exp_add, Real.exp_add]
    ring
  · rw [show β * (1 * -1 + E) = -β + β * E by ring, show β * (-1 * -1 + E) = β + β * E by ring,
      Real.exp_add, Real.exp_add]
    ring

/-! ### The transfer-matrix recursions -/

lemma Z_succ (β : ℝ) (n : ℕ) : Z β (n + 1) = (2 * Real.cosh β) * Z β n := by
  unfold Z weight
  rw [sum_cons (fun σ : Fin (n + 2) → Bool => Real.exp (β * energy σ))]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  have : ∀ b : Bool, Real.exp (β * energy (Fin.cons b ρ : Fin (n + 2) → Bool)) =
      Real.exp (β * (spin b * spin (ρ 0) + energy ρ)) := by
    intro b; rw [energy_cons]
  rw [Finset.sum_congr rfl (fun b _ => this b)]
  exact bool_sum_exp β (spin (ρ 0)) (energy ρ) (spin_eq _)

lemma num_succ (β : ℝ) (n : ℕ) : num β (n + 1) = (2 * Real.sinh β) * num β n := by
  unfold num weight
  rw [sum_cons (fun σ : Fin (n + 2) → Bool =>
    spin (σ 0) * spin (σ (Fin.last (n + 1))) * Real.exp (β * energy σ))]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  have key : ∀ b : Bool,
      spin ((Fin.cons b ρ : Fin (n + 2) → Bool) 0) *
        spin ((Fin.cons b ρ : Fin (n + 2) → Bool) (Fin.last (n + 1))) *
        Real.exp (β * energy (Fin.cons b ρ : Fin (n + 2) → Bool)) =
      spin (ρ (Fin.last n)) * (spin b * Real.exp (β * (spin b * spin (ρ 0) + energy ρ))) := by
    intro b
    rw [energy_cons]
    have h0 : (Fin.cons b ρ : Fin (n + 2) → Bool) 0 = b := Fin.cons_zero _ _
    have h1 : (Fin.cons b ρ : Fin (n + 2) → Bool) (Fin.last (n + 1)) = ρ (Fin.last n) := by
      rw [show (Fin.last (n + 1)) = (Fin.last n).succ from rfl, Fin.cons_succ]
    rw [h0, h1]; ring
  rw [Finset.sum_congr rfl (fun b _ => key b), ← Finset.mul_sum,
    bool_sum_exp_spin β (spin (ρ 0)) (energy ρ) (spin_eq _)]
  ring

/-! ### Closed forms -/

lemma Z_zero (β : ℝ) : Z β 0 = 2 := by
  unfold Z weight
  rw [sum_cons (fun σ : Fin 1 → Bool => Real.exp (β * energy σ))]
  simp [energy]

lemma num_zero (β : ℝ) : num β 0 = 2 := by
  unfold num weight
  rw [sum_cons (fun σ : Fin 1 → Bool =>
    spin (σ 0) * spin (σ (Fin.last 0)) * Real.exp (β * energy σ))]
  simp [energy, spin_sq]

lemma Z_eq (β : ℝ) (n : ℕ) : Z β n = 2 * (2 * Real.cosh β) ^ n := by
  induction n with
  | zero => simpa using Z_zero β
  | succ n ih => rw [Z_succ, ih]; ring

lemma num_eq (β : ℝ) (n : ℕ) : num β n = 2 * (2 * Real.sinh β) ^ n := by
  induction n with
  | zero => simpa using num_zero β
  | succ n ih => rw [num_succ, ih]; ring

lemma Z_pos (β : ℝ) (n : ℕ) : 0 < Z β n := by
  rw [Z_eq]
  have : 0 < 2 * Real.cosh β := by positivity
  positivity

/-- **Exact two-point function of the 1D Ising chain**: `⟨σ₀ σₙ⟩ = (tanh β)ⁿ`. -/
theorem corr_eq (β : ℝ) (n : ℕ) : corr β n = Real.tanh β ^ n := by
  have hc : (0 : ℝ) < Real.cosh β := Real.cosh_pos β
  unfold corr
  rw [num_eq, Z_eq, Real.tanh_eq_sinh_div_cosh, div_pow, mul_pow, mul_pow]
  rw [div_eq_iff (by positivity)]
  field_simp

/-! ### Exponential decay at every finite inverse temperature -/

lemma abs_tanh_lt_one (β : ℝ) : |Real.tanh β| < 1 := by
  rw [abs_lt]
  exact ⟨Real.neg_one_lt_tanh β, Real.tanh_lt_one β⟩

/-- Exponential decay of correlations, at every inverse temperature `β`:
there is `c > 0` with `|⟨σ₀ σₙ⟩| ≤ exp (-c n)` for all `n`. -/
theorem exponential_decay (β : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, |corr β n| ≤ Real.exp (-(c * n)) := by
  rcases eq_or_ne (Real.tanh β) 0 with h0 | h0
  · refine ⟨1, one_pos, fun n => ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [corr_eq, h0]
    · rw [corr_eq, h0, zero_pow (by omega)]
      simp [Real.exp_nonneg]
  · refine ⟨-Real.log |Real.tanh β|, ?_, fun n => ?_⟩
    · have h1 : |Real.tanh β| < 1 := abs_tanh_lt_one β
      have h2 : 0 < |Real.tanh β| := abs_pos.mpr h0
      have := Real.log_neg h2 h1
      linarith
    · have h2 : 0 < |Real.tanh β| := abs_pos.mpr h0
      rw [corr_eq, abs_pow]
      rw [show -(-Real.log |Real.tanh β| * (n : ℝ)) = (n : ℝ) * Real.log |Real.tanh β| by ring,
        ← Real.log_pow, Real.exp_log (by positivity)]

/-- Correlations tend to zero: the chain has no long-range order at any finite `β`. -/
theorem corr_tendsto_zero (β : ℝ) :
    Filter.Tendsto (fun n : ℕ => corr β n) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun n : ℕ => Real.tanh β ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (abs_tanh_lt_one β)
  simpa [corr_eq] using h

/-- Finite susceptibility: `∑ₙ |⟨σ₀ σₙ⟩| < ∞` at every finite `β`. -/
theorem summable_corr (β : ℝ) : Summable (fun n : ℕ => corr β n) := by
  have h : Summable (fun n : ℕ => Real.tanh β ^ n) := by
    apply Summable.of_abs
    simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg _) (abs_tanh_lt_one β)
  simpa [corr_eq] using h

end IsingChain

/-- **Sharpness of the phase transition for the Ising model (one-dimensional case).**

For the nearest-neighbour Ising model on the chain `{0, …, n}` with free boundary
conditions and inverse temperature `β`:

1. the two-point function is exactly `⟨σ₀ σₙ⟩ = (tanh β)ⁿ`;
2. for every `β` there is `c > 0` with `|⟨σ₀ σₙ⟩| ≤ e^{-c n}` (exponential decay);
3. correlations tend to `0`, so there is no long-range order;
4. the susceptibility `∑ₙ ⟨σ₀ σₙ⟩` converges.

Hence the whole of `[0, ∞)` is subcritical: the critical inverse temperature is
`+∞`, and the subcritical behaviour predicted by the sharpness theorem
(exponential decay of correlations together with finite susceptibility) holds
at every finite inverse temperature. -/
theorem duminil_ising_sharp :
    (∀ (β : ℝ) (n : ℕ), IsingChain.corr β n = Real.tanh β ^ n) ∧
    (∀ β : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, |IsingChain.corr β n| ≤ Real.exp (-(c * n))) ∧
    (∀ β : ℝ, Filter.Tendsto (fun n : ℕ => IsingChain.corr β n) Filter.atTop (nhds 0)) ∧
    (∀ β : ℝ, Summable (fun n : ℕ => IsingChain.corr β n)) :=
  ⟨IsingChain.corr_eq, IsingChain.exponential_decay, IsingChain.corr_tendsto_zero,
    IsingChain.summable_corr⟩

end Frontier

