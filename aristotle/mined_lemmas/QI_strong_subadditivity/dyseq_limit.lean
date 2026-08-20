import RequestProject.SSA.PartialTrace

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header comment above has to follow the `import` line: Lean requires `import` commands to
come first in a file.)

The von Neumann entropy `S(A) = -Tr (A log A)` of a positive definite matrix on a threefold
tensor product `α ⊗ β ⊗ γ` satisfies the Lieb–Ruskai inequality

`S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`.

The proof goes through Lindblad's joint convexity of the Umegaki relative entropy
(itself deduced from Ando's joint concavity of the operator geometric mean) and the
resulting monotonicity of the relative entropy under partial traces.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Kronecker
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

/-! ### Relative entropy against `1 ⊗ Y` -/


lemma dyseq_limit {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun m : ℕ => 2 ^ m * (a - dyseq m a b)) atTop
      (𝓝 (a * (Real.log a - Real.log b))) := by
  set t : ℝ := Real.log b - Real.log a with ht
  have hexp : ∀ m : ℕ, dyseq m a b = a * Real.exp (t * ((2:ℝ)⁻¹ ^ m)) := by
    intro m
    set s : ℝ := (2:ℝ)⁻¹ ^ m with hs
    rw [dyseq_eq m ha hb, Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, ← Real.exp_add]
    rw [← Real.exp_log ha, ← Real.exp_add]
    congr 1
    rw [Real.log_exp]
    ring
  have hbase : Tendsto (fun m : ℕ => (Real.exp (t * ((2:ℝ)⁻¹ ^ m)) - 1) / ((2:ℝ)⁻¹ ^ m))
      atTop (𝓝 t) := by
    have hd : HasDerivAt (fun s : ℝ => Real.exp (t * s)) t 0 := by
      have h1 : HasDerivAt (fun s : ℝ => t * s) t 0 := by
        simpa using (hasDerivAt_id (0:ℝ)).const_mul t
      simpa using h1.exp
    rw [hasDerivAt_iff_tendsto_slope] at hd
    have hs : Tendsto (fun m : ℕ => ((2:ℝ)⁻¹ ^ m)) atTop (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num), ?_⟩
      filter_upwards with m
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      positivity
    have h2 := hd.comp hs
    refine h2.congr fun m => ?_
    simp [slope_def_field]
  have hlim := hbase.const_mul (-a)
  have heq : ∀ m : ℕ, (-a) * ((Real.exp (t * ((2:ℝ)⁻¹ ^ m)) - 1) / ((2:ℝ)⁻¹ ^ m))
      = 2 ^ m * (a - dyseq m a b) := by
    intro m
    have hpow : ((2:ℝ)⁻¹ ^ m) = ((2:ℝ) ^ m)⁻¹ := by rw [inv_pow]
    have hne : ((2:ℝ) ^ m) ≠ 0 := by positivity
    rw [hexp m, hpow]
    field_simp
    ring
  have hval : (-a) * t = a * (Real.log a - Real.log b) := by rw [ht]; ring
  rw [← hval]
  exact hlim.congr heq

/-- The relative entropy is the limit of the (rescaled) dyadic trace functionals. -/
