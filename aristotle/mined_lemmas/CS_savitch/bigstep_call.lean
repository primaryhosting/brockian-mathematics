import RequestProject.Savitch.Machine

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Savitch's theorem

We model a space-`s` machine by its configuration graph: it has at most `2 ^ s`
configurations (`s` bits of workspace), a start configuration, an acceptance
predicate, and a transition relation (a relation for nondeterministic machines, a
function for deterministic ones).  A nondeterministic machine accepts when some
accepting configuration is reachable from the start configuration; a deterministic
machine accepts when its (unique) run visits an accepting configuration.

The main theorem `CS.savitch` states `NSPACE f ⊆ DSPACE (9 * (f + 1) ^ 2)`, i.e.
nondeterministic space `f` is contained in deterministic space `O(f ^ 2)`, and
`CS.PSPACE_eq_NPSPACE` deduces `PSPACE = NPSPACE`.
-/

namespace CS

open Savitch

/-- A nondeterministic machine using space `s`: at most `2 ^ s` configurations. -/
structure NMachine (s : ℕ) where
  /-- Number of configurations. -/
  size : ℕ
  /-- The space bound: `s` bits of workspace. -/
  hsize : size ≤ 2 ^ s
  /-- The (nondeterministic) transition relation. -/
  step : Fin size → Fin size → Bool
  /-- The initial configuration. -/
  start : Fin size
  /-- The accepting configurations. -/
  acc : Fin size → Bool

/-- A nondeterministic machine accepts if some accepting configuration is reachable. -/

theorem bigstep_call (R : Fin n → Fin n → Bool) (K : ℕ) :
    ∀ (k : ℕ) (a b : Fin n) (st : List (Frame n)), st.length + k = K →
      Reaches R K (Sum.inl (a, b), st) (Sum.inr (cy R k a b), st) := by
  intro k
  induction k with
  | zero =>
    intro a b st hst
    apply Reaches.one
    show stepR R K (Sum.inl (a, b), st) = _
    simp only [stepR]
    rw [if_pos (by omega)]
    rfl
  | succ k ih =>
    have loop : ∀ (d : ℕ) (a b mid : Fin n) (st : List (Frame n)), n - (mid : ℕ) ≤ d →
        st.length + (k + 1) = K →
        Reaches R K (Sum.inl (a, mid), (a, b, mid, false) :: st)
          (Sum.inr (loopVal R k a b (mid : ℕ)), st) := by
      intro d
      induction d with
      | zero =>
        intro a b mid st hd _
        have := mid.isLt
        omega
      | succ d ihd =>
        intro a b mid st hd hst
        have hmid : (mid : ℕ) < n := mid.isLt
        have hstack : ((a, b, mid, false) :: st).length + k = K := by simp; omega
        have hstack' : ((a, b, mid, true) :: st).length + k = K := by simp; omega
        have hunfold : loopVal R k a b (mid : ℕ) =
            ((cy R k a mid && cy R k mid b) || loopVal R k a b ((mid : ℕ) + 1)) := by
          rw [loopVal_of_lt hmid]
        -- moving to the next midpoint
        have hadv : Reaches R K (advance a b mid st) (Sum.inr (loopVal R k a b ((mid : ℕ) + 1)), st) := by
          unfold advance
          by_cases h : (mid : ℕ) + 1 < n
          · rw [dif_pos h]
            exact ihd a b ⟨(mid : ℕ) + 1, h⟩ st (by simp; omega) hst
          · rw [dif_neg h, loopVal_of_ge h]
            exact Reaches.rfl'
        refine Reaches.trans (ih a mid _ hstack) ?_
        by_cases hv : cy R k a mid = true
        · rw [hv]
          refine Reaches.trans (Reaches.one (?_ : stepR R K (Sum.inr true, (a, b, mid, false) :: st)
              = (Sum.inl (mid, b), (a, b, mid, true) :: st))) ?_
          · simp [stepR]
          refine Reaches.trans (ih mid b _ hstack') ?_
          by_cases hw : cy R k mid b = true
          · rw [hw, hunfold, hv, hw]
            refine Reaches.one ?_
            simp [stepR]
          · simp only [Bool.not_eq_true] at hw
            rw [hw, hunfold, hv, hw]
            simp only [Bool.and_false, Bool.false_or]
            exact Reaches.trans (Reaches.one (by simp [stepR] : stepR R K
              (Sum.inr false, (a, b, mid, true) :: st) = advance a b mid st)) hadv
        · simp only [Bool.not_eq_true] at hv
          rw [hv, hunfold, hv]
          simp only [Bool.false_and, Bool.false_or]
          exact Reaches.trans (Reaches.one (by simp [stepR] : stepR R K
            (Sum.inr false, (a, b, mid, false) :: st) = advance a b mid st)) hadv
    intro a b st hst
    refine Reaches.trans (Reaches.one (?_ : stepR R K (Sum.inl (a, b), st)
        = (Sum.inl (a, mid0 a), (a, b, mid0 a, false) :: st))) ?_
    · simp only [stepR]
      rw [if_neg (by omega)]
    · have := loop n a b (mid0 a) st (by simp) hst
      rw [mid0_val] at this
      rw [cy_succ_eq_loopVal]
      exact this

/-! ### The bounded configuration type -/

/-- Configurations of the Savitch machine: stacks of depth at most `K`. -/
