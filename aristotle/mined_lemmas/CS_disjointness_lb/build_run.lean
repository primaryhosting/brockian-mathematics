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
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

We set up two-party communication protocols as protocol trees, and prove the
`Ω(n)` lower bound for the randomized communication complexity of set
disjointness on `n`-element ground sets: any public-coin randomized protocol
which never wrongly claims that two intersecting sets are disjoint, and which
detects disjointness with probability at least `1/2`, must communicate at least
`n - 1` bits (`CS.disjointness_lb`).

The proof combines the classical fooling set `{(S, Sᶜ) : S ⊆ Fin n}` of size
`2 ^ n` for disjointness with an averaging argument over the public random
string.  We also record the matching upper bound `n + 1`
(`CS.disjointness_ub`), which shows in particular that the hypotheses of the
lower bound are satisfiable, and the deterministic lower bound `n`
(`CS.disjointness_deterministic_lb`).

The randomized bound proved here is for protocols with one-sided error (they
never certify disjointness wrongly); the two-sided bounded-error case is
Razborov's theorem and is not covered by this argument.
-/

open Finset

namespace CS

open scoped Classical

/-- A deterministic two-party communication protocol tree.  `alice g L R` means
"Alice sends the bit `g x` and the players continue with `L` (if the bit is
`true`) or `R` (if it is `false`)"; `bob` is the same with Bob speaking. -/
inductive Prot (X Y : Type*) : Type _
  | leaf : Bool → Prot X Y
  | alice : (X → Bool) → Prot X Y → Prot X Y → Prot X Y
  | bob : (Y → Bool) → Prot X Y → Prot X Y → Prot X Y

namespace Prot

variable {X Y : Type*}

/-- The output of the protocol on the input pair `(x, y)`. -/

theorem build_run {n : ℕ} (m : ℕ) : ∀ (h : (Fin n → Bool) → Bool) (x y : Fin n → Bool),
    ((build m h).run x y = true ↔
      (h y = true ∧ ∀ i : Fin n, (i : ℕ) < m → ¬ (x i = true ∧ y i = true))) := by
  induction m with
  | zero =>
    intro h x y
    constructor
    · intro hrun
      refine ⟨?_, by omega⟩
      by_contra hy
      simp [build, Prot.run, hy] at hrun
    · intro hy
      simp [build, Prot.run, hy.1]
  | succ m ih =>
    intro h x y
    by_cases hb : getBit m x = true
    · have hm : m < n := by
        by_contra hmn
        rw [getBit, dif_neg hmn] at hb
        exact absurd hb (by simp)
      have hx : x ⟨m, hm⟩ = true := by rwa [getBit, dif_pos hm] at hb
      have hrun : (build (m + 1) h).run x y =
          (build m (fun y => h y && !(getBit m y))).run x y := by
        simp [build, Prot.run, hb]
      rw [hrun, ih]
      constructor
      · rintro ⟨h1, h2⟩
        rw [Bool.and_eq_true] at h1
        refine ⟨h1.1, ?_⟩
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | hi'
        · exact h2 i hi'
        · have : i = ⟨m, hm⟩ := by
            apply Fin.ext; simpa using hi'
          subst this
          have : getBit m y = false := by simpa using h1.2
          rw [getBit, dif_pos hm] at this
          simp [this]
      · rintro ⟨h1, h2⟩
        refine ⟨?_, fun i hi => h2 i (by omega)⟩
        rw [Bool.and_eq_true]
        refine ⟨h1, ?_⟩
        have := h2 ⟨m, hm⟩ (by simp)
        rw [hx] at this
        have hy : y ⟨m, hm⟩ = false := by
          rcases Bool.eq_false_or_eq_true (y ⟨m, hm⟩) with h' | h'
          · exact absurd ⟨rfl, h'⟩ this
          · exact h'
        simp [getBit, dif_pos hm, hy]
    · have hb' : getBit m x = false := by simpa using hb
      have hrun : (build (m + 1) h).run x y = (build m h).run x y := by
        simp [build, Prot.run, hb']
      rw [hrun, ih]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | hi'
        · exact h2 i hi'
        · have hm : m < n := hi' ▸ i.isLt
          have hxi : x i = false := by
            rw [getBit, dif_pos hm] at hb'
            rwa [show (⟨m, hm⟩ : Fin n) = i from Fin.ext hi'.symm] at hb'
          simp [hxi]
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun i hi => h2 i (by omega)⟩

/-- **Upper bound**: there is a correct deterministic protocol for disjointness
on `Fin n` of cost `n + 1`, so the lower bound below is not vacuous and is
tight up to an additive constant. -/
