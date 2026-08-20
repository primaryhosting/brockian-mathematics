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

/-
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Statement: Set-disjointness has Ω(n) randomized communication complexity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

namespace CS

universe u v

/-- A deterministic two-party communication protocol tree over inputs `X` (Alice) and `Y` (Bob).
`alice m k` means Alice sends the bit `m x` and the protocol continues with `k (m x)`;
`bob m k` means Bob sends the bit `m y`. -/
inductive Protocol (X : Type u) (Y : Type v) : Type (max u v)
  | leaf : Bool → Protocol X Y
  | alice : (X → Bool) → (Bool → Protocol X Y) → Protocol X Y
  | bob : (Y → Bool) → (Bool → Protocol X Y) → Protocol X Y

namespace Protocol

variable {X : Type u} {Y : Type v}

/-- The output of the protocol on a given pair of inputs. -/

lemma rectangle (P : Protocol X Y) :
    ∀ (x x' : X) (y y' : Y), trans P x y = trans P x' y' →
      trans P x y' = trans P x y ∧ run P x y' = run P x y := by
  induction P with
  | leaf b => intro x x' y y' _; exact ⟨rfl, rfl⟩
  | alice m k ih =>
      intro x x' y y' h
      simp only [trans, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have h2' : trans (k (m x)) x y = trans (k (m x)) x' y' := by rw [h2, h1]
      obtain ⟨ha, hb⟩ := ih (m x) x x' y y' h2'
      refine ⟨?_, ?_⟩
      · simp only [trans]; rw [ha]
      · simp only [run]; exact hb
  | bob m k ih =>
      intro x x' y y' h
      simp only [trans, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have h2' : trans (k (m y)) x y = trans (k (m y)) x' y' := by rw [h2, h1]
      obtain ⟨ha, hb⟩ := ih (m y) x x' y y' h2'
      refine ⟨?_, ?_⟩
      · simp only [trans, ← h1]; rw [ha]
      · simp only [run, ← h1]; exact hb

end Protocol

open Protocol

/-!
## The lower bound

We work with the set-disjointness function on `Fin n`: Alice holds `a : Finset (Fin n)`,
Bob holds `b : Finset (Fin n)`, and the goal is to decide whether `a` and `b` are disjoint.

The protocol is allowed *private randomness*: Alice's input is a pair `(a, ra)` with
`ra : RA` her private random string, and likewise for Bob.  The hypotheses below say the
protocol has *one-sided error*: it never accepts an intersecting pair (`hsound`), and every
disjoint pair is accepted for at least one choice of the random strings (`hcomplete`).  This
is a very weak requirement (it is implied, in particular, by any one-sided-error randomized
protocol with error probability `< 1`, and by any correct deterministic protocol), so the
resulting `n`-bit lower bound is correspondingly strong.

Three consequences are recorded: the deterministic bound, the one-sided-error randomized
bound with any error probability `< 1`, and a two-sided-error bound for protocols whose
error probability is smaller than `4 ^ (-n)`.  The two-sided bound for *constant* error is
Razborov's theorem, whose proof (the corruption bound) is not carried out here.
-/

/-- **Fooling-set bound.**  Suppose `α` and `β` embed the subsets of `Fin n` into the two input
spaces of a protocol `P` in such a way that `P` rejects `(α S, β T)` whenever `S` and `T`
intersect, while accepting every "diagonal" pair `(α S, β Sᶜ)`.  Then `P` has depth at least
`n`.  This is the classical `2 ^ n` fooling set for set disjointness. -/
