/-
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
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

set_option grind.warning false

namespace QI

/-!
## The Deutsch–Jozsa circuit

We model the `n`-qubit register by its (real) amplitude vector, a function
`(Fin n → Bool) → ℝ`, indexed by bit strings.  The circuit is

`|0…0⟩  --H^{⊗n}-->  --U_f (phase kickback)-->  --H^{⊗n}-->  measure`.

Everything below is stated for real amplitudes, which suffices because all gates
involved (Hadamard and the phase oracle) have real matrix entries.
-/

/-- The all-zeros bit string. -/

lemma sum_signIP {n : ℕ} (y : Fin n → Bool) :
    ∑ x : Fin n → Bool, signIP x y = if y = zeroStr n then (2 : ℝ) ^ n else 0 := by
  have hswap : ∑ x : Fin n → Bool, (∏ i, if x i && y i then (-1 : ℝ) else 1)
      = ∏ i, ∑ b : Bool, (if b && y i then (-1 : ℝ) else 1) :=
    (Finset.prod_univ_sum (fun _ => Finset.univ) fun i b => if b && y i then (-1 : ℝ) else 1).symm
  have hfac : ∀ i : Fin n, ∑ b : Bool, (if b && y i then (-1 : ℝ) else 1)
      = if y i then (0 : ℝ) else 2 := by
    intro i
    cases y i <;> simp
  simp only [signIP]
  rw [hswap, Finset.prod_congr rfl fun i _ => hfac i]
  by_cases hy : y = zeroStr n
  · subst hy
    simp [zeroStr]
  · rw [if_neg hy]
    obtain ⟨i, hi⟩ : ∃ i, y i = true := by
      by_contra hcon
      push_neg at hcon
      exact hy (funext fun i => by simpa [zeroStr] using hcon i)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- After the first Hadamard layer the register is in the uniform superposition. -/
