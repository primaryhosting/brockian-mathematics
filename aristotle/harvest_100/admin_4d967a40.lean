import Mathlib
import RequestProject.Main

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

/-- Re-export check: the target theorem is available in the Mathlib environment. -/
example (check : PCA.Artifact → Bool) (a₀ a : PCA.Artifact) (cert : PCA.Cert)
    (hcert : cert = PCA.prove check a₀) :
    PCA.prove check a = cert ↔ PCA.Untampered a₀ a :=
  PCA.Cert.reprove_matches_iff_untampered check a₀ a cert hcert

/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` commands to precede every other syntactic item,
-- so this module (whose first item must be the header doc-comment above) carries
-- no imports.  The development below needs none: it uses only core Lean.
-- The original Mathlib preamble is preserved verbatim in `RequestProject.Preamble`,
-- which imports this module.

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

namespace PCA

/-! ## The isolation engine's model

An *artifact* is a finite byte string (the code and data an app ships).  A
*certificate* records the digest of the artifact it was issued for, together
with the verdict of the isolation checker on that artifact.

The prover is deterministic: `prove check a` is a pure function of the
artifact.  An artifact is *untampered* (with respect to the original `a₀`) when
it is byte-for-byte the artifact the certificate was issued for.

The statement `PCA.Cert.reprove_matches_iff_untampered` says that re-running the
prover on an artifact reproduces the stored certificate **exactly when** the
artifact is untampered.  The `←` direction is completeness (determinism of the
prover: an honest artifact always re-certifies); the `→` direction is soundness
(collision-freeness of the digest: no tampered artifact can reproduce the
certificate).  Collision-freeness is not assumed — it is proved below for the
concrete base-`257` digest of byte strings.
-/

/-- A shipped artifact: a finite string of bytes. -/
structure Artifact where
  bytes : List (Fin 256)
deriving DecidableEq

/-- The concrete digest of a byte string: a base-`257` positional encoding, with
each byte offset by one so that the empty string is the only string of digest
`0`. -/
def hashList : List (Fin 256) → Nat
  | [] => 0
  | x :: xs => 257 * hashList xs + (x.val + 1)

@[simp] theorem hashList_nil : hashList [] = 0 := rfl

@[simp] theorem hashList_cons (x : Fin 256) (xs : List (Fin 256)) :
    hashList (x :: xs) = 257 * hashList xs + (x.val + 1) := rfl

/-- Only the empty byte string has digest `0`. -/
@[simp] theorem hashList_eq_zero_iff (l : List (Fin 256)) : hashList l = 0 ↔ l = [] := by
  cases l with
  | nil => simp
  | cons x xs => simp

/-- The digest is collision-free: distinct byte strings have distinct digests. -/
theorem hashList_injective : Function.Injective hashList := by
  intro l
  induction l with
  | nil =>
    intro m h
    exact ((hashList_eq_zero_iff m).mp h.symm).symm
  | cons x xs ih =>
    intro m h
    cases m with
    | nil =>
      simp only [hashList_nil, hashList_cons] at h
      omega
    | cons y ys =>
      simp only [hashList_cons] at h
      have hx : x.val < 256 := x.isLt
      have hy : y.val < 256 := y.isLt
      have hxy : x = y := Fin.ext (by omega)
      have hrest : hashList xs = hashList ys := by omega
      rw [hxy, ih hrest]

/-- The digest of an artifact. -/
def Artifact.digest (a : Artifact) : Nat := hashList a.bytes

/-- Artifacts with equal digests are equal. -/
theorem Artifact.digest_injective : Function.Injective Artifact.digest := by
  intro a b h
  cases a
  cases b
  simpa using hashList_injective h

/-- A certificate: the digest of the artifact it was issued for, together with
the verdict of the isolation checker on that artifact. -/
structure Cert where
  digest : Nat
  verdict : Bool
deriving DecidableEq

/-- The deterministic prover: it digests the artifact and runs the isolation
checker `check` on it. -/
def prove (check : Artifact → Bool) (a : Artifact) : Cert :=
  { digest := a.digest, verdict := check a }

/-- The artifact `a` is untampered with respect to the original `a₀` when it is
byte-for-byte the same artifact. -/
def Untampered (a₀ a : Artifact) : Prop := a = a₀

namespace Cert

/-- **Soundness and completeness of the isolation engine's certificate check.**

Let `cert` be the certificate issued for the original artifact `a₀` by the
deterministic prover `prove check`.  Re-running the prover on an artifact `a`
reproduces `cert` exactly when `a` is untampered, i.e. `a = a₀`. -/
theorem reprove_matches_iff_untampered
    (check : Artifact → Bool) (a₀ a : Artifact) (cert : Cert)
    (hcert : cert = prove check a₀) :
    prove check a = cert ↔ Untampered a₀ a := by
  subst hcert
  constructor
  · intro h
    exact Artifact.digest_injective (congrArg Cert.digest h)
  · intro h
    rw [show a = a₀ from h]

end Cert

/-- A convenient corollary: tampering is detected.  If the artifact differs from
the one the certificate was issued for, re-proving yields a different
certificate. -/
theorem tampering_detected
    (check : Artifact → Bool) (a₀ a : Artifact) (cert : Cert)
    (hcert : cert = prove check a₀) (h : a ≠ a₀) :
    prove check a ≠ cert := fun hc =>
  h ((Cert.reprove_matches_iff_untampered check a₀ a cert hcert).mp hc)

end PCA

