/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Cert

/-! ## Arithmetic: an injective pairing function on `Nat` -/

/-- Szudzik-style pairing function. -/
def pairNat (a b : Nat) : Nat := if a < b then b * b + a else a * a + a + b

private theorem sq_succ (n : Nat) : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by
  simp [Nat.mul_add, Nat.add_mul]
  omega

/-- The "root" of a pair: the unique `r` with `r*r ≤ pairNat a b < (r+1)*(r+1)`. -/
def rootNat (a b : Nat) : Nat := if a < b then b else a

private theorem root_bounds (a b : Nat) :
    rootNat a b * rootNat a b ≤ pairNat a b ∧
      pairNat a b < (rootNat a b + 1) * (rootNat a b + 1) := by
  unfold rootNat pairNat
  by_cases h : a < b
  · simp only [h, if_pos]
    rw [sq_succ]
    omega
  · simp only [h, if_neg, if_false]
    rw [sq_succ]
    omega

private theorem root_unique {v r s : Nat} (hr1 : r * r ≤ v) (hr2 : v < (r + 1) * (r + 1))
    (hs1 : s * s ≤ v) (hs2 : v < (s + 1) * (s + 1)) : r = s := by
  rcases Nat.lt_trichotomy r s with h | h | h
  · exact absurd (Nat.lt_of_lt_of_le hr2 (Nat.mul_le_mul h h)) (Nat.not_lt.2 hs1)
  · exact h
  · exact absurd (Nat.lt_of_lt_of_le hs2 (Nat.mul_le_mul h h)) (Nat.not_lt.2 hr1)

theorem pairNat_inj {a b c d : Nat} (h : pairNat a b = pairNat c d) : a = c ∧ b = d := by
  have hab := root_bounds a b
  have hcd := root_bounds c d
  have hroot : rootNat a b = rootNat c d :=
    root_unique hab.1 hab.2 (h ▸ hcd.1) (h ▸ hcd.2)
  by_cases h1 : a < b <;> by_cases h2 : c < d
  · simp only [rootNat, if_pos h1, if_pos h2] at hroot
    subst hroot
    simp only [pairNat, if_pos h1, if_pos h2] at h
    omega
  · simp only [rootNat, if_pos h1, if_neg h2] at hroot
    subst hroot
    simp only [pairNat, if_pos h1, if_neg h2] at h
    omega
  · simp only [rootNat, if_neg h1, if_pos h2] at hroot
    subst hroot
    simp only [pairNat, if_neg h1, if_pos h2] at h
    omega
  · simp only [rootNat, if_neg h1, if_neg h2] at hroot
    subst hroot
    simp only [pairNat, if_neg h1, if_neg h2] at h
    omega

/-! ## Injective encoding of lists of naturals -/

/-- Injective encoding of a list of naturals as a single natural number. -/
def encList : List Nat → Nat
  | [] => 0
  | x :: xs => pairNat x (encList xs) + 1

theorem encList_inj : ∀ {l l' : List Nat}, encList l = encList l' → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [encList] at h
  | _ :: _, [], h => by simp [encList] at h
  | x :: xs, y :: ys, h => by
      simp only [encList, Nat.add_right_cancel_iff] at h
      obtain ⟨hx, hxs⟩ := pairNat_inj h
      rw [hx, encList_inj hxs]

theorem encList_injective : Function.Injective encList := fun _ _ h => encList_inj h

/-! ## The isolation engine's machine model -/

/-- Instructions of an isolated app. -/
inductive Instr
  | nop
  | read (addr : Nat)
  | write (addr val : Nat)
  | call (cap : Nat)
  deriving DecidableEq, Repr

/-- An isolation policy: the app may only touch memory below `maxAddr`,
and may only invoke capabilities listed in `caps`. -/
structure Policy where
  maxAddr : Nat
  caps : List Nat
  deriving DecidableEq, Repr

/-- A deployable artifact: the app's code together with the policy it ships with. -/
structure Artifact where
  code : List Instr
  policy : Policy
  deriving DecidableEq, Repr

/-- Machine state of the isolation engine: memory, the trace of capability
invocations performed so far, and a trap flag. -/
structure Machine where
  mem : Nat → Nat
  trace : List Nat
  fault : Bool

/-- Pointwise memory update. -/
def setMem (mem : Nat → Nat) (a v : Nat) : Nat → Nat := fun x => if x = a then v else mem x

/-- One step of the isolation engine.  Any policy violation traps (sets `fault`)
and has no effect on memory or on the capability trace. -/
def step (p : Policy) (m : Machine) : Instr → Machine
  | .nop => m
  | .read a => if a < p.maxAddr then m else { m with fault := true }
  | .write a v =>
      if a < p.maxAddr then { m with mem := setMem m.mem a v }
      else { m with fault := true }
  | .call c => if c ∈ p.caps then { m with trace := c :: m.trace } else { m with fault := true }

/-- Running a whole artifact under the isolation engine. -/
def run (a : Artifact) (m : Machine) : Machine := a.code.foldl (step a.policy) m

/-! ## The static isolation checker -/

/-- Static check that a single instruction respects the policy. -/
def Instr.allowed (p : Policy) : Instr → Bool
  | .nop => true
  | .read a => decide (a < p.maxAddr)
  | .write a _ => decide (a < p.maxAddr)
  | .call c => decide (c ∈ p.caps)

/-- Static check that the whole artifact respects its policy. -/
def isolated (a : Artifact) : Bool := a.code.all (Instr.allowed a.policy)

/-! ## Digests -/

/-- Injective encoding of an instruction. -/
def Instr.enc : Instr → Nat
  | .nop => 0
  | .read a => 4 * a + 1
  | .write a v => 4 * pairNat a v + 2
  | .call c => 4 * c + 3

theorem Instr.enc_injective : Function.Injective Instr.enc := by
  intro i j h
  cases i with
  | nop =>
      cases j with
      | nop => rfl
      | read a => simp only [Instr.enc] at h; omega
      | write a v => simp only [Instr.enc] at h; omega
      | call c => simp only [Instr.enc] at h; omega
  | read x =>
      cases j with
      | nop => simp only [Instr.enc] at h; omega
      | read a => simp only [Instr.enc] at h; rw [show x = a by omega]
      | write a v => simp only [Instr.enc] at h; omega
      | call c => simp only [Instr.enc] at h; omega
  | write x y =>
      cases j with
      | nop => simp only [Instr.enc] at h; omega
      | read a => simp only [Instr.enc] at h; omega
      | write a v =>
          simp only [Instr.enc] at h
          obtain ⟨h1, h2⟩ := pairNat_inj (show pairNat x y = pairNat a v by omega)
          rw [h1, h2]
      | call c => simp only [Instr.enc] at h; omega
  | call z =>
      cases j with
      | nop => simp only [Instr.enc] at h; omega
      | read a => simp only [Instr.enc] at h; omega
      | write a v => simp only [Instr.enc] at h; omega
      | call c => simp only [Instr.enc] at h; rw [show z = c by omega]

/-- Injective encoding of a policy. -/
def Policy.enc (p : Policy) : Nat := pairNat p.maxAddr (encList p.caps)

theorem Policy.enc_injective : Function.Injective Policy.enc := by
  intro p q h
  obtain ⟨h1, h2⟩ := pairNat_inj h
  cases p; cases q
  simp only [Policy.mk.injEq]
  exact ⟨h1, encList_inj h2⟩

/-- The digest of an artifact.  It is collision-free (injective), so the model
captures the ideal-hash assumption used by proof-carrying deployments. -/
def digest (a : Artifact) : Nat :=
  pairNat (encList (a.code.map Instr.enc)) (Policy.enc a.policy)

theorem map_enc_injective : ∀ {l l' : List Instr},
    l.map Instr.enc = l'.map Instr.enc → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      rw [Instr.enc_injective h.1, map_enc_injective h.2]

theorem digest_injective : Function.Injective digest := by
  intro a b h
  obtain ⟨h1, h2⟩ := pairNat_inj h
  cases a; cases b
  simp only [Artifact.mk.injEq]
  exact ⟨map_enc_injective (encList_inj h1), Policy.enc_injective h2⟩

/-! ## Certificates -/

/-- A proof-carrying certificate: the digest of the artifact it was issued for,
the policy that was checked, and the verdict of the isolation checker. -/
structure Certificate where
  digest : Nat
  policy : Policy
  verdict : Bool
  deriving DecidableEq, Repr

/-- Re-running the certifier on a delivered artifact. -/
def reprove (a : Artifact) : Certificate :=
  { digest := digest a, policy := a.policy, verdict := isolated a }

/-! ## Main theorem -/

/-- **Reprove matches iff untampered.**  Re-running the certifier on a delivered
artifact `a'` reproduces the certificate issued for the original artifact `a`
if and only if the delivered artifact is exactly the original one. -/
theorem reprove_matches_iff_untampered (a a' : Artifact) :
    reprove a' = reprove a ↔ a' = a := by
  constructor
  · intro h
    have : digest a' = digest a := congrArg Certificate.digest h
    exact digest_injective this
  · intro h
    rw [h]

/-! ## Consequences -/

/-- Completeness: an untampered artifact always re-proves to its certificate. -/
theorem reprove_of_untampered (a a' : Artifact) (h : a' = a) : reprove a' = reprove a :=
  (reprove_matches_iff_untampered a a').2 h

/-- Soundness / tamper detection: any modification of the artifact is detected. -/
theorem reprove_ne_of_tampered (a a' : Artifact) (h : a' ≠ a) : reprove a' ≠ reprove a :=
  fun hc => h ((reprove_matches_iff_untampered a a').1 hc)

/-- The certificate check performed by the deployment target. -/
def checks (c : Certificate) (a : Artifact) : Bool := decide (reprove a = c)

/-- The deployment check accepts a delivered artifact against the certificate
issued for `a` exactly when the delivered artifact is untampered. -/
theorem checks_reprove_iff (a a' : Artifact) :
    checks (reprove a) a' = true ↔ a' = a := by
  simp [checks, reprove_matches_iff_untampered]

/-! ## The certified verdict really does guarantee isolation -/

theorem step_mem_outside (p : Policy) (m : Machine) (i : Instr) (x : Nat)
    (hx : p.maxAddr ≤ x) : (step p m i).mem x = m.mem x := by
  cases i with
  | nop => rfl
  | read a => by_cases h : a < p.maxAddr <;> simp [step, h]
  | write a v =>
      by_cases h : a < p.maxAddr <;> simp [step, h, setMem] <;> omega
  | call c => by_cases h : c ∈ p.caps <;> simp [step, h]

/-- Memory outside the policy window is never modified, whatever the app does. -/
theorem run_mem_outside (a : Artifact) (m : Machine) (x : Nat)
    (hx : a.policy.maxAddr ≤ x) : (run a m).mem x = m.mem x := by
  unfold run
  generalize a.code = l
  induction l generalizing m with
  | nil => rfl
  | cons i is ih => simpa [List.foldl_cons] using (ih (step a.policy m i)).trans
      (step_mem_outside a.policy m i x hx)

/-- The capability trace only ever grows by capabilities allowed by the policy. -/
theorem run_trace_allowed (a : Artifact) (m : Machine) (c : Nat)
    (hc : c ∈ (run a m).trace) : c ∈ a.policy.caps ∨ c ∈ m.trace := by
  unfold run at hc
  generalize a.code = l at hc
  induction l generalizing m with
  | nil => exact Or.inr hc
  | cons i is ih =>
      rw [List.foldl_cons] at hc
      rcases ih (step a.policy m i) hc with h | h
      · exact Or.inl h
      · cases i with
        | nop => exact Or.inr h
        | read x => by_cases hx : x < a.policy.maxAddr <;> simp [step, hx] at h <;> exact Or.inr h
        | write x v =>
            by_cases hx : x < a.policy.maxAddr <;> simp [step, hx] at h <;> exact Or.inr h
        | call x =>
            by_cases hx : x ∈ a.policy.caps
            · simp only [step, hx, if_pos, if_true, List.mem_cons] at h
              rcases h with h | h
              · exact Or.inl (h ▸ hx)
              · exact Or.inr h
            · simp [step, hx] at h
              exact Or.inr h

theorem step_no_fault (p : Policy) (m : Machine) (i : Instr)
    (hi : Instr.allowed p i = true) (hm : m.fault = false) : (step p m i).fault = false := by
  cases i with
  | nop => exact hm
  | read a => simp only [Instr.allowed, decide_eq_true_eq] at hi; simp [step, hi, hm]
  | write a v => simp only [Instr.allowed, decide_eq_true_eq] at hi; simp [step, hi, hm]
  | call c => simp only [Instr.allowed, decide_eq_true_eq] at hi; simp [step, hi, hm]

/-- A certified artifact never traps: a positive verdict on the certificate is a
genuine guarantee about every execution of the app. -/
theorem run_no_fault_of_verdict (a : Artifact) (m : Machine)
    (hv : (reprove a).verdict = true) (hm : m.fault = false) : (run a m).fault = false := by
  have hall : ∀ i ∈ a.code, Instr.allowed a.policy i = true := by
    have := hv
    simp only [reprove, isolated, List.all_eq_true] at this
    exact this
  unfold run
  revert hall
  generalize a.code = l
  intro hall
  induction l generalizing m with
  | nil => exact hm
  | cons i is ih =>
      rw [List.foldl_cons]
      exact ih (step a.policy m i) (fun j hj => hall j (List.mem_cons_of_mem _ hj))
        (step_no_fault a.policy m i (hall i (List.mem_cons_self ..)) hm)

end PCA.Cert

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

