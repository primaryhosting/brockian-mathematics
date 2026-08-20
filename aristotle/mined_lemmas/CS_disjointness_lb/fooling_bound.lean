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

theorem fooling_bound {n : ℕ} {X : Type u} {Y : Type v} (P : Protocol X Y)
    (α : Finset (Fin n) → X) (β : Finset (Fin n) → Y)
    (hsound : ∀ S T : Finset (Fin n), ¬ Disjoint S T → run P (α S) (β T) = false)
    (hacc : ∀ S : Finset (Fin n), run P (α S) (β Sᶜ) = true) :
    n ≤ depth P := by
  classical
  set F : Finset (Fin n) → List Bool := fun S => trans P (α S) (β Sᶜ)
  have hinj : Function.Injective F := by
    intro S T hST
    by_contra hne
    have hex : ∃ i : Fin n, (i ∈ S ∧ i ∉ T) ∨ (i ∈ T ∧ i ∉ S) := by
      by_contra hcon
      push_neg at hcon
      apply hne
      ext i
      exact ⟨fun hi => (hcon i).1 hi, fun hi => (hcon i).2 hi⟩
    obtain ⟨i, hi⟩ := hex
    rcases hi with ⟨hiS, hiT⟩ | ⟨hiT, hiS⟩
    · -- the crossed pair `(α S, β Tᶜ)` gets the same transcript, hence is accepted too
      obtain ⟨_, hrun⟩ := rectangle P (α S) (α T) (β Sᶜ) (β Tᶜ) hST
      have h1 : run P (α S) (β Tᶜ) = true := by rw [hrun]; exact hacc S
      have h2 : ¬ Disjoint S (Tᶜ : Finset (Fin n)) := by
        rw [Finset.not_disjoint_iff]
        exact ⟨i, hiS, Finset.mem_compl.mpr hiT⟩
      rw [hsound S Tᶜ h2] at h1
      exact Bool.false_ne_true h1
    · obtain ⟨_, hrun⟩ := rectangle P (α T) (α S) (β Tᶜ) (β Sᶜ) hST.symm
      have h1 : run P (α T) (β Sᶜ) = true := by rw [hrun]; exact hacc T
      have h2 : ¬ Disjoint T (Sᶜ : Finset (Fin n)) := by
        rw [Finset.not_disjoint_iff]
        exact ⟨i, hiT, Finset.mem_compl.mpr hiS⟩
      rw [hsound T Sᶜ h2] at h1
      exact Bool.false_ne_true h1
  have hcard : (2 : ℕ) ^ n ≤ (paths P).card := by
    have h1 : (Finset.univ : Finset (Finset (Fin n))).card ≤ (paths P).card :=
      Finset.card_le_card_of_injOn F (fun S _ => trans_mem_paths _ _ _)
        (fun S _ T _ h => hinj h)
    simpa [Finset.card_univ, Fintype.card_finset] using h1
  have h2 : (2 : ℕ) ^ n ≤ 2 ^ depth P := le_trans hcard (card_paths_le P)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

/-- **Set-disjointness requires `n` bits of communication.**

Any (private-coin, one-sided error) randomized communication protocol for set disjointness on
a universe of size `n` must exchange at least `n` bits in the worst case: the one-sided
randomized communication complexity of `DISJ_n` is `Ω(n)` (indeed `≥ n`). -/
