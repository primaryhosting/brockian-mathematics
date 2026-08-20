/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Complex Matrix

namespace QPhys

variable {n : ℕ}

/-- The expectation value `⟨v, M v⟩` of the (matrix) observable `M` in the state `v`. -/

private lemma hasDerivAt_finsum {f : Fin n → ℝ → ℂ} {f' : Fin n → ℂ} {t : ℝ}
    (h : ∀ i, HasDerivAt (f i) (f' i) t) : HasDerivAt (fun s => ∑ i, f i s) (∑ i, f' i) t := by
  have e : (fun s => ∑ i, f i s) = ∑ i, f i := by funext s; simp
  rw [e]
  exact HasDerivAt.sum (fun i _ => h i)

/-- The algebraic core of Ehrenfest's theorem: the three terms coming from the product rule
recombine into the commutator term plus the explicit time-derivative term. -/
