/-
`m` independent runs of Simon's algorithm, and the analysis showing that `n + 2` quantum
queries determine the hidden shift with probability at least `3/4`.
-/
import RequestProject.SimonQuantum

open scoped BigOperators
open scoped Classical
open Finset

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace QI

/-- The state of `m` independent copies of the Simon circuit (a product state, using
`m` quantum queries in total). -/

lemma transcript_stable {n : ℕ} (A : ClassicalAlg n) (q : ℕ) (g : Bits n → Bits n)
    (hg : ∀ x ∈ queried A q, g x = x) :
    ∀ k, k ≤ q → transcript A g k = transcript A (fun x => x) k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hk' : k ≤ q := Nat.le_of_succ_le hk
    have hT := ih hk'
    have hmem : qpt A k ∈ queried A q := by
      rw [queried]
      exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 (Nat.lt_of_succ_le hk), rfl⟩
    rw [transcript, transcript, hT, ← qpt, hg _ hmem]

section Construction

variable {n : ℕ}

/-- The canonical representative of the pair `{x, x + s}`, where `s j = 1`. -/
