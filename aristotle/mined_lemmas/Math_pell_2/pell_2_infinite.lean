/-!
# Pell 2
Category: Pure Mathematics
Target: Math.pell_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² − 2·y² = 1` has a nontrivial integer solution,
i.e. one with `y ≠ 0` (equivalently, a solution other than `(±1, 0)`).
Witness: `3² − 2·2² = 9 − 8 = 1`. -/

theorem pell_2_infinite : {p : ℤ × ℤ | p.1 ^ 2 - 2 * p.2 ^ 2 = 1}.Infinite := by
  have hstrict : StrictMono fun n => (pellStep n).1 :=
    strictMono_nat_of_lt_succ fun n => (pellStep_bounds n).2.2
  have hinj : Function.Injective pellStep := fun a b hab =>
    hstrict.injective (by rw [hab])
  exact Set.infinite_of_injective_forall_mem hinj (fun n => pellStep_sol n)

end Math

