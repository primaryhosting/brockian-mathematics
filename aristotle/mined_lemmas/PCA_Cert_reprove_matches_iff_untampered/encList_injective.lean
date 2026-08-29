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
