import Mathlib
import RequestProject.Simon.Basic
import RequestProject.Simon.Classical
import RequestProject.Simon.Quantum
import RequestProject.Simon.Solve

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

/-!
# Simon's problem: `O(n)` quantum queries, `Ω(2 ^ (n / 2))` classical queries

`QI.simon_algorithm` collects the two halves of the classical/quantum
separation for Simon's problem.  An instance is a function
`f : BV n → BV n` on `n`-bit strings satisfying Simon's promise
`IsSimon f s`: `s ≠ 0` and `f x = f y ↔ y = x ∨ y = x + s`.  The task is to
output the hidden shift `s`.

*Quantum upper bound.*  Each round of Simon's algorithm uses exactly **one**
query: it prepares `2 ^ (-n/2) ∑ₓ |x⟩|f x⟩`, applies the Hadamard transform to
the first register and measures.  The resulting distribution `prob f` is
uniform on the hyperplane `{y | ⟪y, s⟫ = 0}` orthogonal to `s`.  After
`2 * n` such rounds — i.e. `2 * n = O(n)` queries — the outcomes fail to pin
down `s` (as the unique nonzero solution of the linear system `⟪yᵢ, t⟫ = 0`)
only with probability at most `2 ^ (-n)`.

*Classical lower bound.*  A deterministic classical query algorithm that always
outputs the hidden shift after `q` queries must satisfy `2 ^ n ≤ (q + 2) ^ 2`,
i.e. `q ≥ 2 ^ (n / 2) - 2 = Ω(2 ^ (n / 2))`.
-/

namespace QI

/-- The classical lower bound in the form `2 ^ (n / 2) ≤ q + 2`. -/

theorem card_badTuples_le (s : BV n) (m : ℕ) :
    2 ^ m * (badTuples s m).card ≤ 2 ^ n * (orth s).card ^ m := by
  classical
  set T : Finset (BV n) := Finset.univ.filter (fun t : BV n => t ≠ 0 ∧ t ≠ s) with hT
  have hsub := badTuples_subset s m
  have hcard : (badTuples s m).card
      ≤ ∑ t ∈ T, ((orth s).filter (fun y => ip y t = 0)).card ^ m := by
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_biUnion_le) ?_
    refine Finset.sum_le_sum fun t _ => ?_
    rw [Fintype.card_piFinset_const]
  have hterm : ∀ t ∈ T, 2 ^ m * ((orth s).filter (fun y => ip y t = 0)).card ^ m
      = (orth s).card ^ m := by
    intro t htT
    have ht : t ≠ 0 ∧ t ≠ s := by
      have := Finset.mem_filter.1 htT
      exact this.2
    have h2 := card_orth_filter ht.1 ht.2
    calc 2 ^ m * ((orth s).filter (fun y => ip y t = 0)).card ^ m
        = (2 * ((orth s).filter (fun y => ip y t = 0)).card) ^ m := by
          rw [Nat.mul_pow]
      _ = (orth s).card ^ m := by rw [h2]
  calc 2 ^ m * (badTuples s m).card
      ≤ 2 ^ m * ∑ t ∈ T, ((orth s).filter (fun y => ip y t = 0)).card ^ m :=
        Nat.mul_le_mul_left _ hcard
    _ = ∑ t ∈ T, 2 ^ m * ((orth s).filter (fun y => ip y t = 0)).card ^ m := by
        rw [Finset.mul_sum]
    _ = ∑ _t ∈ T, (orth s).card ^ m := Finset.sum_congr rfl hterm
    _ = T.card * (orth s).card ^ m := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 ^ n * (orth s).card ^ m := by
        refine Nat.mul_le_mul_right _ ?_
        calc T.card ≤ (Finset.univ : Finset (BV n)).card := Finset.card_le_card (by simp [hT])
          _ = 2 ^ n := by rw [Finset.card_univ, card_bv]

/-! ### The failure probability of Simon's algorithm -/

/-- The probability that the outcomes of `m` independent runs of the quantum
subroutine fail to determine the hidden shift. -/
