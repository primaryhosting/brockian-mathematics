import RequestProject.Basic

/-!
# Unbounded fan-in Boolean circuits, the class `AC⁰`, and `PARITY`

A `Circuit n` is a Boolean circuit on `n` inputs built from constants, input
variables, negations, and *unbounded fan-in* `AND`/`OR` gates.

* `Circuit.depth` counts the maximal number of `AND`/`OR` gates on a root-to-leaf
  path (negations are free, as is standard for `AC⁰`).
* `Circuit.size` counts the number of `AND`/`OR` gates.

`InAC0 f` says that the family `f` is computed by circuits of some fixed depth and
polynomial size.  Making negations free and not counting them in the size only
makes the class larger, hence the lower bound proved later stronger.
-/

namespace CS

/-- Boolean circuits with unbounded fan-in `AND`/`OR` gates. -/
inductive Circuit (n : ℕ) where
  | const : Bool → Circuit n
  | var : Fin n → Circuit n
  | neg : Circuit n → Circuit n
  | or : (m : ℕ) → (Fin m → Circuit n) → Circuit n
  | and : (m : ℕ) → (Fin m → Circuit n) → Circuit n

namespace Circuit

/-- The Boolean function computed by a circuit. -/

lemma card_subsets_le (m D : ℕ) :
    2 * ((Finset.univ : Finset (Finset (Fin (2 * m)))).filter (fun T => T.card ≤ m + D)).card
      ≤ 4 ^ m + 2 * (D + 1) * Nat.centralBinom m := by
  classical
  rw [card_filter_card_le]
  have hsplit : ∑ k ∈ Finset.range (m + D + 1), (2 * m).choose k
      = (∑ k ∈ Finset.range m, (2 * m).choose k)
        + ∑ k ∈ Finset.Ico m (m + D + 1), (2 * m).choose k := by
    have h1 : Finset.range (m + D + 1) = Finset.range m ∪ Finset.Ico m (m + D + 1) := by
      ext k; simp [Finset.mem_range, Finset.mem_Ico]; omega
    have hd : Disjoint (Finset.range m) (Finset.Ico m (m + D + 1)) := by
      simp only [Finset.disjoint_left, Finset.mem_range, Finset.mem_Ico, not_and]
      intro a ha hb
      omega
    rw [h1, Finset.sum_union hd]
  have hupper : ∑ k ∈ Finset.Ico m (m + D + 1), (2 * m).choose k
      ≤ (D + 1) * Nat.centralBinom m := by
    calc ∑ k ∈ Finset.Ico m (m + D + 1), (2 * m).choose k
        ≤ ∑ _k ∈ Finset.Ico m (m + D + 1), Nat.centralBinom m := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          have := Nat.choose_le_middle k (2 * m)
          simpa [Nat.centralBinom, Nat.mul_div_cancel_left m (by norm_num : 0 < 2)] using this
      _ = (D + 1) * Nat.centralBinom m := by
          rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
          congr 1
          omega
  have hhalf := two_mul_sum_range_choose_lt m
  have hprod : 2 * (D + 1) * Nat.centralBinom m = 2 * ((D + 1) * Nat.centralBinom m) := by ring
  rw [hsplit, hprod]
  omega

/-- `k * (q+1) ≤ 2^q` once `q ≥ k^2 + k`. -/
