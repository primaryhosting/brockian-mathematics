import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Brockian.Weyl.WeylLawTarget

variable {α : Type u}

/-- `countingFunction lam L K` is the number of indices `n < K` whose eigenvalue `lam n`
lies at or below the threshold `L`.  For a discrete spectrum this stabilises as `K → ∞`
and its limiting value is the Weyl counting function `N(L) = #{n | lam n ≤ L}`. -/

theorem countingFunction_stable {K₀ : Nat} (hK₀ : ∀ n : Nat, K₀ ≤ n → ¬ (lam n ≤ L))
    (K K' : Nat) (hK : K₀ ≤ K) (hKK' : K ≤ K') :
    countingFunction lam L K' = countingFunction lam L K := by
  induction K' with
  | zero =>
    have : K = 0 := Nat.le_zero.mp hKK'
    simp [this]
  | succ n ih =>
    rcases Nat.lt_or_ge n K with hn | hn
    · have : K = n + 1 := Nat.le_antisymm hKK' hn
      subst this
      rfl
    · have hlam : ¬ (lam n ≤ L) := hK₀ n (Nat.le_trans hK hn)
      simp [countingFunction, hlam, ih hn]

end Basic

/-- **Divergence of the Weyl counting function.**

Let `lam : ℕ → α` enumerate the eigenvalues of an operator, with values in a type `α` carrying
a transitive order relation.  Assume:

* `hdisc` — the spectrum is *discrete*: below any threshold only finitely many eigenvalues occur;
* `hrvm` — the eigenvalues are enumerated in nondecreasing order, as delivered by the
  Rayleigh variational (min–max) characterisation.

Then, above every threshold, the counting function `N(L) = #{n | lam n ≤ L}` is well defined
(the truncated counts stabilise) and it diverges: for every `M` there is a threshold `L₀` such
that `N(L) ≥ M` for all `L ≥ L₀`. -/
