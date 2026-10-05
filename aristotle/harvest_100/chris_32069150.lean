/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is self-contained (no imports): a Lean module doc comment has to precede any
`import` command, and the required header above is a module doc comment, so the
development below is built from Lean core only.

We fix a small but genuine machine model: a step-indexed interpreter `run` for programs
coded by natural numbers, define the time-bounded classes `TIME t`, and prove by
diagonalization that allowing one extra step strictly increases the family of decidable
languages.
-/

namespace CS

/-- Inputs are pairs of natural numbers: the first component is read as (the code of) a
program, the second one as a clock. -/
abbrev Input : Type := Nat × Nat

/-- A *language* is a decidable predicate on inputs. -/
abbrev Lang : Type := Input → Bool

/--
`run s e x` runs the program with code `e` on input `x` for at most `s` steps.
It returns `some b` if the program halts within `s` steps with output `b`, and `none` if
it has not halted yet.

A program code `e : Nat` is decoded as an opcode `e % 3` together with an argument `e / 3`:

* opcode `0`: the constant program, outputting `true` iff its argument is `1`;
* opcode `1`: negation — run the subprogram whose code is the argument and flip the
  answer, at the cost of one extra step;
* opcode `2`: the *clocked diagonalizer* — on input `x = (a, k)` simulate the program with
  code `a` on the very same input `x` for `k + 1` steps and flip its answer, answering
  `true` if the simulated program has not halted in time.  The simulation is step for
  step, with one extra step of overhead.
-/
def run : Nat → Nat → Input → Option Bool
  | 0, _, _ => none
  | s + 1, e, x =>
    match e % 3 with
    | 0 => some (decide (e / 3 = 1))
    | 1 => (run s (e / 3) x).map (fun b => !b)
    | _ =>
        match run (min s (x.2 + 1)) x.1 x with
        | some b => some (!b)
        | none => if x.2 + 1 ≤ s then some true else none
  termination_by s => s
  decreasing_by
  · omega
  · omega

/-! ### Basic equations for the interpreter -/

theorem run_zero (e : Nat) (x : Input) : run 0 e x = none := by rw [run]

theorem run_op0 (s e : Nat) (x : Input) (h : e % 3 = 0) :
    run (s + 1) e x = some (decide (e / 3 = 1)) := by rw [run, h]

theorem run_op1 (s e : Nat) (x : Input) (h : e % 3 = 1) :
    run (s + 1) e x = (run s (e / 3) x).map (fun b => !b) := by rw [run, h]

theorem run_op2_some (s e : Nat) (x : Input) (h : e % 3 = 2) (c : Bool)
    (hc : run (min s (x.2 + 1)) x.1 x = some c) : run (s + 1) e x = some (!c) := by
  rw [run, h, hc]

theorem run_op2_none (s e : Nat) (x : Input) (h : e % 3 = 2)
    (hc : run (min s (x.2 + 1)) x.1 x = none) :
    run (s + 1) e x = if x.2 + 1 ≤ s then some true else none := by
  rw [run, h, hc]

/-! ### Monotonicity in the step bound -/

/-- Giving a program one extra step cannot change an answer it has already produced. -/
theorem run_succ : ∀ (s e : Nat) (x : Input) (b : Bool), run s e x = some b →
    run (s + 1) e x = some b := by
  intro s
  induction s with
  | zero => intro e x b h; rw [run_zero] at h; exact absurd h (by simp)
  | succ m ih =>
    intro e x b h
    have hm : e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 := by omega
    rcases hm with hmod | hmod | hmod
    · rw [run_op0 _ _ _ hmod] at h ⊢; exact h
    · rw [run_op1 _ _ _ hmod] at h ⊢
      rcases hc : run m (e / 3) x with _ | c
      · rw [hc] at h; simp at h
      · rw [ih _ _ _ hc]; rw [hc] at h; exact h
    · rcases hc : run (min m (x.2 + 1)) x.1 x with _ | c
      · rw [run_op2_none _ _ _ hmod hc] at h
        by_cases hkm : x.2 + 1 ≤ m
        · simp only [hkm, if_true] at h
          have hmin : min (m + 1) (x.2 + 1) = min m (x.2 + 1) := by omega
          rw [run_op2_none _ _ _ hmod (by rw [hmin]; exact hc)]
          simp [show x.2 + 1 ≤ m + 1 by omega, ← h]
        · simp only [hkm, if_false] at h; exact absurd h (by simp)
      · rw [run_op2_some _ _ _ hmod _ hc] at h
        have hmin : run (min (m + 1) (x.2 + 1)) x.1 x = some c := by
          by_cases hkm : x.2 + 1 ≤ m
          · have hmm : min (m + 1) (x.2 + 1) = min m (x.2 + 1) := by omega
            rw [hmm]; exact hc
          · have h1 : min m (x.2 + 1) = m := by omega
            have h2 : min (m + 1) (x.2 + 1) = m + 1 := by omega
            rw [h2]; exact ih _ _ _ (h1 ▸ hc)
        rw [run_op2_some _ _ _ hmod _ hmin]; exact h

/-- The answer of a halted computation is stable under increasing the step bound. -/
theorem run_mono {s s' e : Nat} {x : Input} {b : Bool} (hss : s ≤ s')
    (h : run s e x = some b) : run s' e x = some b := by
  obtain ⟨d, rfl⟩ : ∃ d, s' = s + d := ⟨s' - s, by omega⟩
  clear hss
  induction d with
  | zero => exact h
  | succ n ih => exact run_succ _ _ _ _ ih

/-! ### Time-bounded classes -/

/-- `TIME t L` says that the language `L` is decided by some program within `t x` steps on
every input `x`. -/
def TIME (t : Input → Nat) (L : Lang) : Prop := ∃ e : Nat, ∀ x, run (t x) e x = some (L x)

/-- More time can only decide more languages. -/
theorem TIME_mono {t t' : Input → Nat} (h : ∀ x, t x ≤ t' x) {L : Lang} (hL : TIME t L) :
    TIME t' L := by
  obtain ⟨e, he⟩ := hL
  exact ⟨e, fun x => run_mono (h x) (he x)⟩

/-- The time bound read off the input: on input `x = (a, k)` it is `k + 1`. -/
def tclock : Input → Nat := fun x => x.2 + 1

/-! ### The diagonal language -/

/-- The diagonal language: `x = (a, k)` belongs to it iff the program with code `a` does
*not* accept `x` within `tclock x` steps. -/
def diagLang : Lang := fun x =>
  match run (tclock x) x.1 x with
  | some b => !b
  | none => true

/-- The clocked diagonalizer decides the diagonal language with exactly one extra step. -/
theorem diagLang_mem_TIME_succ : TIME (fun x => tclock x + 1) diagLang := by
  refine ⟨2, fun x => ?_⟩
  show run (tclock x + 1) 2 x = some (diagLang x)
  have hmin : min (x.2 + 1) (x.2 + 1) = x.2 + 1 := by omega
  have htc : tclock x = x.2 + 1 := rfl
  rcases hc : run (x.2 + 1) x.1 x with _ | c
  · have hnone : run (min (x.2 + 1) (x.2 + 1)) x.1 x = none := by rw [hmin]; exact hc
    rw [htc, run_op2_none _ _ _ (by decide) hnone]
    have : diagLang x = true := by rw [diagLang]; rw [htc, hc]
    rw [this]
    simp
  · have hsome : run (min (x.2 + 1) (x.2 + 1)) x.1 x = some c := by rw [hmin]; exact hc
    rw [htc, run_op2_some _ _ _ (by decide) _ hsome]
    have : diagLang x = !c := by rw [diagLang]; rw [htc, hc]
    rw [this]

/-- The heart of the hierarchy theorem: the diagonal language is not decidable within the
time bound that it diagonalizes against. -/
theorem diagLang_not_mem_TIME : ¬ TIME tclock diagLang := by
  rintro ⟨e, he⟩
  have h := he (e, 0)
  have hd : diagLang (e, 0) = !(diagLang (e, 0)) := by
    conv => lhs; rw [diagLang]
    rw [show ((e, 0) : Input).1 = e from rfl, h]
  rcases hb : diagLang (e, 0) with _ | _ <;> rw [hb] at hd <;> simp at hd

/-! ### The time hierarchy theorem -/

/-- **Time hierarchy theorem.**  A time bound allowing just one step more than `tclock`
decides all the languages that `tclock` decides, and strictly more: the diagonal language
is decidable within the larger bound but by no program running within `tclock` steps. -/
theorem time_hierarchy {t' : Input → Nat} (h : ∀ x, tclock x + 1 ≤ t' x) :
    (∀ L, TIME tclock L → TIME t' L) ∧ ∃ L, TIME t' L ∧ ¬ TIME tclock L := by
  refine ⟨fun L hL => TIME_mono (fun x => by have := h x; omega) hL, ?_⟩
  exact ⟨diagLang, TIME_mono h diagLang_mem_TIME_succ, diagLang_not_mem_TIME⟩

/-- Non-vacuity: the constant languages are already decidable within `tclock`. -/
theorem const_mem_TIME_tclock (b : Bool) : TIME tclock (fun _ => b) := by
  refine ⟨if b then 3 else 0, fun x => ?_⟩
  have htc : tclock x = x.2 + 1 := rfl
  cases b <;> · rw [htc, run_op0 _ _ _ (by decide)]; rfl

end CS

