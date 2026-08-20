import Mathlib
import RequestProject.Brun.Final

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede every other command, including module
-- doc comments, so the required header comment appears immediately after the imports.)

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The summand is `1/n` whenever `n` and `n + 2` are both prime, and `0` otherwise; the value of
its sum is Brun's constant.  Convergence is proved from scratch by a Brun pure sieve; see the
development in `RequestProject/Brun/`. -/

lemma sifted_le (Q : Finset ℕ) (N K : ℕ) (hK : Even K) :
    (#((range N).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n*(n+2))) : ℤ)
      ≤ ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K), (-1:ℤ)^T.card *
          #((range N).filter (fun n => ∀ p ∈ T, p ∣ n*(n+2))) := by
  set R : ℕ → Finset ℕ := fun n => Q.filter (fun p => p ∣ n*(n+2)) with hR
  have hcount : ∀ T : Finset ℕ, T ⊆ Q →
      ((#((range N).filter (fun n => ∀ p ∈ T, p ∣ n*(n+2))) : ℤ))
        = ∑ n ∈ range N, (if T ⊆ R n then (1:ℤ) else 0) := by
    intro T hT
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    apply propext
    constructor
    · intro h p hp
      exact Finset.mem_filter.2 ⟨hT hp, h p hp⟩
    · intro h p hp
      exact (Finset.mem_filter.1 (h hp)).2
  have step1 : (#((range N).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n*(n+2))) : ℤ)
      = ∑ n ∈ range N, (if R n = ∅ then (1:ℤ) else 0) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    apply propext
    rw [Finset.filter_eq_empty_iff]
  have step2 : ∑ n ∈ range N, (if R n = ∅ then (1:ℤ) else 0)
      ≤ ∑ n ∈ range N, ∑ T ∈ (R n).powerset.filter (fun T => T.card ≤ K), (-1:ℤ)^T.card :=
    Finset.sum_le_sum fun n _ => bonferroni_pointwise (R n) K hK
  have step3 : ∑ n ∈ range N, ∑ T ∈ (R n).powerset.filter (fun T => T.card ≤ K), (-1:ℤ)^T.card
      = ∑ n ∈ range N, ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K),
          (if T ⊆ R n then (-1:ℤ)^T.card else 0) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1.trans (Finset.filter_subset _ _), h2⟩, h1⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h3, h2⟩
  have step4 : ∑ n ∈ range N, ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K),
          (if T ⊆ R n then (-1:ℤ)^T.card else 0)
      = ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K), (-1:ℤ)^T.card *
          #((range N).filter (fun n => ∀ p ∈ T, p ∣ n*(n+2))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [hcount T (Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1), Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    split <;> simp
  rw [step1]
  exact (step2.trans_eq step3).trans_eq step4

/-- **Brun's pure sieve**, real form: the number of `n < N` with `n (n+2)` coprime to all
primes of `Q` is at most the truncated main term plus the truncated error term. -/
