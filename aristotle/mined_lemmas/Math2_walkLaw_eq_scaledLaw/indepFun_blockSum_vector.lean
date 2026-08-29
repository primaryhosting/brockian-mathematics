import RequestProject.CLT

/-!
# Convergence of the rescaled walk against smooth test functions

`Math2.walkLaw μ n t` is the law of `S_{⌊n t⌋} / √n`, where `S` is a random walk with step
distribution `μ`.  Here we prove that, for a centered step distribution with unit variance and
finite third absolute moment, the integrals of smooth test functions against `walkLaw μ n t`
converge to the corresponding integrals against the centered Gaussian law of variance `t`, which
is the law of Brownian motion at time `t`.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- The law of `S_p / √n`, the sum of `p` i.i.d. steps with law `μ`, rescaled by `1/√n`. -/

theorem indepFun_blockSum_vector (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    {a : ℕ → ℕ} (ha : Monotone a) (k : ℕ) :
    IndepFun (fun ω => ∑ i ∈ Finset.Ico (a k) (a (k + 1)), X i ω)
      (fun ω (j : Fin k) => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω) P := by
  classical
  set S : Finset ℕ := Finset.Ico (a k) (a (k + 1)) with hS
  set T : Finset ℕ := Finset.range (a k) with hT
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    rw [hS, Finset.mem_Ico] at hiS
    rw [hT, Finset.mem_range] at hiT
    omega
  have hbase := hindep.indepFun_finset S T hST hmeas
  have hφ : Measurable (fun w : S → ℝ => ∑ i : S, w i) := by fun_prop
  have hψ : Measurable (fun (w : T → ℝ) (j : Fin k) =>
      ∑ i : T, if a j ≤ (i : ℕ) ∧ (i : ℕ) < a (j + 1) then w i else 0) := by
    refine measurable_pi_lambda _ fun j => ?_
    exact Finset.measurable_sum _ fun i _ => by split_ifs <;> fun_prop
  have hcomp := hbase.comp hφ hψ
  have h1 : ((fun w : S → ℝ => ∑ i : S, w i) ∘ fun (ω : Ω) (i : S) => X (i : ℕ) ω)
      = fun ω => ∑ i ∈ Finset.Ico (a k) (a (k + 1)), X i ω := by
    funext ω
    simp only [Function.comp_apply]
    exact Finset.sum_coe_sort (Finset.Ico (a k) (a (k + 1))) (fun i => X i ω)
  have h2 : ((fun (w : T → ℝ) (j : Fin k) =>
        ∑ i : T, if a j ≤ (i : ℕ) ∧ (i : ℕ) < a (j + 1) then w i else 0)
      ∘ fun (ω : Ω) (i : T) => X (i : ℕ) ω)
      = fun ω (j : Fin k) => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω := by
    funext ω j
    simp only [Function.comp_apply]
    have hsub : Finset.Ico (a j) (a (j + 1)) ⊆ T := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have hle : a ((j : ℕ) + 1) ≤ a k := ha (by omega)
      rw [hT, Finset.mem_range]
      omega
    have hcoe : (∑ i : T, if a j ≤ (i : ℕ) ∧ (i : ℕ) < a (j + 1) then X (i : ℕ) ω else 0)
        = ∑ i ∈ T, if a j ≤ i ∧ i < a (j + 1) then X i ω else 0 :=
      Finset.sum_coe_sort T (fun i => if a j ≤ i ∧ i < a (j + 1) then X i ω else 0)
    have hfilter : T.filter (fun i => a j ≤ i ∧ i < a (j + 1))
        = Finset.Ico (a j) (a (j + 1)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h
        exact ⟨hsub (Finset.mem_Ico.2 h), h⟩
    rw [hcoe, ← Finset.sum_filter, hfilter]
  rw [h1, h2] at hcomp
  exact hcomp

/-- **The joint law of the block sums of a random walk with i.i.d. steps.**  For an increasing
sequence of times `a`, the vector of increments `(∑_{a j ≤ i < a (j+1)} X i)_{j < k}` has as law
the product of the convolution powers `convPow μ (a (j+1) - a j)`; in particular the increments
are independent. -/
