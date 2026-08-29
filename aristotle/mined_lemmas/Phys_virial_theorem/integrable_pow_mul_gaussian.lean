import RequestProject.Main

/-!
# A concrete instance of the virial theorem

The hypotheses of `Phys.virial_theorem` are satisfiable: we check them for the
ground state `ψ(x) = π^(-1/4) exp(-x²/2)` of the harmonic oscillator
`V(x) = x²/2`, with energy `E = 1/2`, and deduce the virial identity
`2⟨T⟩ = ⟨x ∂ₓV⟩ = 2⟨V⟩` for that state.
-/

namespace Phys

open MeasureTheory Filter Topology Real

/-- `exp (-x²/2)` squared is `exp (-x²)`. -/

theorem integrable_pow_mul_gaussian (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (-x ^ 2)) volume := by
  have hbase : Integrable (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) volume :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ n * Real.exp (-x ^ 2 / 2)) volume := by
    fun_prop
  have hbdd : Integrable
      (fun x : ℝ => (x ^ n * Real.exp (-x ^ 2 / 2)) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) volume := by
    refine hbase.bdd_mul (c := 1 + 2 ^ n * (Nat.factorial n : ℝ)) hmeas ?_
    filter_upwards with x
    have h := abs_pow_mul_exp_neg_half_sq_le n x
    have : ‖x ^ n * Real.exp (-x ^ 2 / 2)‖ = |x| ^ n * Real.exp (-x ^ 2 / 2) := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow,
        abs_of_pos (Real.exp_pos _)]
    rw [this]
    exact h
  refine hbdd.congr ?_
  filter_upwards with x
  have h : Real.exp (-x ^ 2 / 2) * Real.exp (-(1 / 2 : ℝ) * x ^ 2) = Real.exp (-x ^ 2) := by
    rw [← Real.exp_add]
    ring_nf
  calc x ^ n * Real.exp (-x ^ 2 / 2) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)
      = x ^ n * (Real.exp (-x ^ 2 / 2) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by ring
    _ = x ^ n * Real.exp (-x ^ 2) := by rw [h]

/-- `exp (-x²/2) → 0` at `+∞`. -/
