/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Isolation

/-- A resource path in the isolation engine's name space: a sequence of name
components (components are interned names, represented by natural numbers). -/
abbrev Path := List Nat

/-- A sandbox of the isolation engine: a `root` (the mount point the sandboxed
app is confined to) together with a deny predicate `denied` that can additionally
block individual absolute paths inside the sandbox. -/
structure Sandbox where
  /-- The mount point the sandboxed application is confined to. -/
  root : Path
  /-- Absolute paths explicitly blocked by the isolation policy. -/
  denied : Path → Bool

/-- A path `p` is *in scope* for sandbox `s` when it lies under the sandbox root,
say `p = s.root ++ c`, and no non-trivial ancestor of `p` below the root is denied. -/
def InScope (s : Sandbox) (p : Path) : Prop :=
  ∃ c : Path, p = s.root ++ c ∧
    ∀ c' : Path, c' <+: c → c' ≠ [] → ¬ s.denied (s.root ++ c')

/-- Strip a prefix from a path; fails (`none`) if the path does not start with it. -/
def strip : Path → Path → Option Path
  | [], p => some p
  | _ :: _, [] => none
  | a :: r, b :: p => if a = b then strip r p else none

/-- Walk down the components of a sandbox-relative path, starting from the absolute
path `acc`, failing as soon as one of the traversed absolute paths is denied. -/
def scan (s : Sandbox) (acc : Path) : Path → Option Path
  | [] => some []
  | a :: rest =>
      if s.denied (acc ++ [a]) then none
      else (scan s (acc ++ [a]) rest).map (fun t => a :: t)

/-- The isolation engine's encoder: turn an absolute path into the sandbox-relative
capability code the sandboxed app is allowed to hold, or fail. -/
def encode (s : Sandbox) (p : Path) : Option Path :=
  (strip s.root p).bind (scan s s.root)

/-- The decoder used by the isolation engine to resolve a capability code back to an
absolute path. -/
def decode (s : Sandbox) (c : Path) : Path :=
  s.root ++ c

/-- Stripping a prefix that really is a prefix succeeds and returns the remainder. -/
theorem strip_append (r c : Path) : strip r (r ++ c) = some c := by
  induction r with
  | nil => simp [strip]
  | cons a r ih => simpa [strip] using ih

/-- If stripping succeeds, the stripped prefix really was a prefix. -/
theorem eq_append_of_strip_eq_some :
    ∀ (r p q : Path), strip r p = some q → p = r ++ q := by
  intro r
  induction r with
  | nil => intro p q h; simpa [strip] using h
  | cons a r ih =>
      intro p q h
      match p with
      | [] => simp [strip] at h
      | b :: p' =>
          by_cases hab : a = b
          · subst hab
            rw [strip, if_pos rfl] at h
            simpa using ih p' q h
          · rw [strip, if_neg hab] at h
            exact absurd h (by simp)

/-- The scan of a path all of whose non-empty ancestors are allowed succeeds and is
the identity. -/
theorem scan_eq_self (s : Sandbox) (acc c : Path)
    (h : ∀ c' : Path, c' <+: c → c' ≠ [] → ¬ s.denied (acc ++ c')) :
    scan s acc c = some c := by
  induction c generalizing acc with
  | nil => simp [scan]
  | cons a rest ih =>
      have ha : ¬ s.denied (acc ++ [a]) :=
        h [a] (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩) (by simp)
      have hrest : scan s (acc ++ [a]) rest = some rest := by
        refine ih (acc ++ [a]) ?_
        intro c' hc' hne
        have h2 := h (a :: c') (List.cons_prefix_cons.mpr ⟨rfl, hc'⟩) (by simp)
        simpa [List.append_assoc] using h2
      simp [scan, ha, hrest]

/-- A successful scan is the identity and certifies that every non-empty ancestor of
the scanned path is allowed. -/
theorem scan_eq_some (s : Sandbox) :
    ∀ (acc q t : Path), scan s acc q = some t →
      t = q ∧ ∀ q' : Path, q' <+: q → q' ≠ [] → ¬ s.denied (acc ++ q') := by
  intro acc q
  induction q generalizing acc with
  | nil =>
      intro t ht
      refine ⟨by simpa [scan] using ht.symm, ?_⟩
      intro q' hq' hne
      exact absurd (List.prefix_nil.mp hq') hne
  | cons a rest ih =>
      intro t ht
      by_cases ha : s.denied (acc ++ [a])
      · simp [scan, ha] at ht
      · rw [scan, if_neg ha, Option.map_eq_some_iff] at ht
        obtain ⟨t', ht', rfl⟩ := ht
        obtain ⟨rfl, hall⟩ := ih (acc ++ [a]) t' ht'
        refine ⟨rfl, ?_⟩
        intro q' hq' hne
        match q' with
        | [] => exact absurd rfl hne
        | b :: q'' =>
            obtain ⟨rfl, hq''⟩ := List.cons_prefix_cons.mp hq'
            match q'' with
            | [] => simpa using ha
            | d :: q''' =>
                have := hall (d :: q''') hq'' (by simp)
                simpa [List.append_assoc] using this

/-- **In-scope encoding completeness.**  The isolation engine's encoder never rejects a
path that the policy puts in scope: every in-scope absolute path has a capability code,
and decoding that code recovers exactly the original path. -/
theorem in_scope_encoding_complete (s : Sandbox) (p : Path) (hp : InScope s p) :
    ∃ c : Path, encode s p = some c ∧ decode s c = p := by
  obtain ⟨c, rfl, hc⟩ := hp
  exact ⟨c, by simp [encode, strip_append, scan_eq_self s s.root c hc], rfl⟩

/-- Contrapositive form: if the encoder rejects a path, that path was out of scope. -/
theorem not_in_scope_of_encode_eq_none (s : Sandbox) (p : Path)
    (h : encode s p = none) : ¬ InScope s p := by
  intro hp
  obtain ⟨c, hc, -⟩ := in_scope_encoding_complete s p hp
  rw [h] at hc
  exact absurd hc (by simp)

/-- Soundness counterpart: anything the encoder accepts is in scope, and its code
decodes back to the path it came from. -/
theorem encode_sound (s : Sandbox) (p c : Path) (h : encode s p = some c) :
    decode s c = p ∧ InScope s p := by
  match hq : strip s.root p with
  | none => rw [encode, hq] at h; exact absurd h (by simp)
  | some q =>
      have hp : p = s.root ++ q := eq_append_of_strip_eq_some s.root p q hq
      rw [encode, hq] at h
      simp only [Option.bind_some] at h
      obtain ⟨rfl, hall⟩ := scan_eq_some s s.root q c h
      exact ⟨by rw [decode, ← hp], ⟨c, hp, hall⟩⟩

end PCA.Isolation

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

