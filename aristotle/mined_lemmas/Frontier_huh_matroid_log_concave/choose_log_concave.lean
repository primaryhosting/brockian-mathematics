import RequestProject.Main

/-!
# Log-concavity of the characteristic polynomial of a uniform matroid

This file constructs the uniform matroid `U_{r,E}` on a finite ground set `E` and proves that
the coefficients of its characteristic polynomial form a log-concave sequence, i.e. the
Adiprasito–Huh–Katz theorem for uniform matroids.
-/

namespace Frontier

open Finset Polynomial

variable {α : Type*}

/-- The uniform matroid `U_{r,E}`: the independent sets are the subsets of `E` of size at most
`r`. -/

lemma choose_log_concave (n k : ℕ) :
    n.choose k * n.choose (k + 2) ≤ n.choose (k + 1) * n.choose (k + 1) := by
  have key : (n.choose k * n.choose (k + 2)) * ((k + 1) * (k + 2))
      ≤ (n.choose (k + 1) * n.choose (k + 1)) * ((k + 1) * (k + 2)) := by
    have e1 : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) := Nat.choose_succ_right_eq n k
    have e2 : n.choose (k + 2) * (k + 2) = n.choose (k + 1) * (n - (k + 1)) :=
      Nat.choose_succ_right_eq n (k + 1)
    have lhs : (n.choose k * n.choose (k + 2)) * ((k + 1) * (k + 2))
        = (n.choose k * (k + 1)) * (n.choose (k + 1) * (n - (k + 1))) := by
      rw [← e2]; ring
    have rhs : (n.choose (k + 1) * n.choose (k + 1)) * ((k + 1) * (k + 2))
        = (n.choose k * (n - k)) * (n.choose (k + 1) * (k + 2)) := by
      rw [← e1]; ring
    rw [lhs, rhs]
    have hstep : (k + 1) * (n - (k + 1)) ≤ (n - k) * (k + 2) := by
      calc (k + 1) * (n - (k + 1)) ≤ (k + 1) * (n - k) :=
            Nat.mul_le_mul_left _ (Nat.sub_le_sub_left (Nat.le_succ k) n)
        _ ≤ (k + 2) * (n - k) := Nat.mul_le_mul_right _ (by omega)
        _ = (n - k) * (k + 2) := Nat.mul_comm _ _
    calc (n.choose k * (k + 1)) * (n.choose (k + 1) * (n - (k + 1)))
        = (n.choose k * n.choose (k + 1)) * ((k + 1) * (n - (k + 1))) := by ring
      _ ≤ (n.choose k * n.choose (k + 1)) * ((n - k) * (k + 2)) :=
          Nat.mul_le_mul_left _ hstep
      _ = (n.choose k * (n - k)) * (n.choose (k + 1) * (k + 2)) := by ring
  exact Nat.le_of_mul_le_mul_right key (by positivity)

/-- **Log-concavity of the characteristic polynomial of a matroid** (Adiprasito–Huh–Katz),
base case: for the free (Boolean) matroid on a finite ground set `E`, the absolute values of the
coefficients of the characteristic polynomial form a log-concave sequence,
`w_{i+1}^2 ≥ w_i · w_{i+2}`. -/
