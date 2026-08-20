/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace PCA.Isolation

/-! ## The model

We model the isolation engine of a proof-carrying app as follows.

* A *capability* (`Cap`) is one of a fixed set of permissions.
* A *resource* (`Resource`) is a path, i.e. a list of interned symbol identifiers.
* A *scope* (`Scope`) grants a list of capabilities on every resource lying under
  a given root path.
* A request `(c, r)` is *in scope* when `c` is granted and `r` lies under the root.

Requests crossing the isolation boundary are serialised to a bitstring by
`encodeReq` (a self-delimiting unary encoding) and the engine's runtime check is
the boolean function `checkToken`, which decodes the bitstring and re-checks the
scope condition.

The two main results are:

* `PCA.Isolation.in_scope_encoding_complete` — *completeness*: every in-scope
  request has its encoding accepted by the runtime check;
* `PCA.Isolation.in_scope_encoding_sound` — *soundness*: the runtime check only
  accepts encodings of in-scope requests.
-/

/-- The capabilities the isolation engine can grant. -/
inductive Cap
  | read
  | write
  | net
  deriving DecidableEq, Repr

/-- Numeric code of a capability, used by the wire format. -/
def Cap.code : Cap → Nat
  | .read => 0
  | .write => 1
  | .net => 2

/-- Partial inverse of `Cap.code`. -/
def Cap.ofCode : Nat → Option Cap
  | 0 => some .read
  | 1 => some .write
  | 2 => some .net
  | _ => none

@[simp] theorem Cap.ofCode_code (c : Cap) : Cap.ofCode c.code = some c := by
  cases c <;> rfl

theorem Cap.code_of_ofCode {n : Nat} {c : Cap} (h : Cap.ofCode n = some c) : n = c.code := by
  match n, h with
  | 0, h => simp [Cap.ofCode] at h; subst h; rfl
  | 1, h => simp [Cap.ofCode] at h; subst h; rfl
  | 2, h => simp [Cap.ofCode] at h; subst h; rfl
  | (n + 3), h => simp [Cap.ofCode] at h

/-- A resource is a path of interned symbol identifiers. -/
abbrev Resource := List Nat

/-- A scope grants the capabilities in `caps` on all resources under `root`. -/
structure Scope where
  root : Resource
  caps : List Cap

/-- A request `(c, r)` is in scope when the capability is granted and the
resource lies under the scope's root. -/
def inScope (s : Scope) (c : Cap) (r : Resource) : Prop :=
  c ∈ s.caps ∧ s.root <+: r

instance (s : Scope) (c : Cap) (r : Resource) : Decidable (inScope s c r) := by
  unfold inScope; infer_instance

/-! ## The wire format -/

/-- Self-delimiting unary encoding of a natural number. -/
def encodeNat (n : Nat) : List Bool := List.replicate n true ++ [false]

/-- Encoding of a list of natural numbers: concatenation of the unary codes. -/
def encodeNats : List Nat → List Bool
  | [] => []
  | n :: ns => encodeNat n ++ encodeNats ns

/-- Decoder for `encodeNats`; `k` is the number of `true`s read so far. -/
def decodeAux : List Bool → Nat → Option (List Nat)
  | [], 0 => some []
  | [], _ + 1 => none
  | true :: bs, k => decodeAux bs (k + 1)
  | false :: bs, k => (decodeAux bs 0).map (fun l => k :: l)

/-- Decoder for `encodeNats`. -/
def decodeNats (bs : List Bool) : Option (List Nat) := decodeAux bs 0

/-- Serialisation of a request as a bitstring. -/
def encodeReq (c : Cap) (r : Resource) : List Bool := encodeNats (c.code :: r)

/-- The runtime check performed by the isolation engine on an incoming token. -/
def checkToken (s : Scope) (t : List Bool) : Bool :=
  match decodeNats t with
  | some (n :: r) =>
      match Cap.ofCode n with
      | some c => decide (c ∈ s.caps) && decide (s.root <+: r)
      | none => false
  | _ => false

/-! ## Round-trip of the wire format -/

theorem decodeAux_encodeNat_append (n k : Nat) (rest : List Bool) :
    decodeAux (encodeNat n ++ rest) k
      = (decodeAux rest 0).map (fun l => (k + n) :: l) := by
  induction n generalizing k with
  | zero => simp [encodeNat, decodeAux]
  | succ n ih =>
      have : encodeNat (n + 1) = true :: encodeNat n := by
        simp [encodeNat, List.replicate_succ]
      rw [this]
      have hk : k + 1 + n = k + (n + 1) := by omega
      simp only [List.cons_append, decodeAux, ih (k + 1), hk]

@[simp] theorem decodeNats_encodeNats (l : List Nat) : decodeNats (encodeNats l) = some l := by
  induction l with
  | nil => rfl
  | cons n ns ih =>
      unfold decodeNats at *
      simp [encodeNats, decodeAux_encodeNat_append n 0 (encodeNats ns), ih]

/-! ## Soundness and completeness of the isolation check -/

/-- **Completeness**: every in-scope request is accepted by the runtime check on
its encoding. -/
theorem in_scope_encoding_complete (s : Scope) (c : Cap) (r : Resource)
    (h : inScope s c r) : checkToken s (encodeReq c r) = true := by
  obtain ⟨hc, hr⟩ := h
  simp [checkToken, encodeReq, hc, hr]

/-- **Soundness**: the runtime check accepts the encoding of a request only if
that request is in scope. -/
theorem in_scope_encoding_sound (s : Scope) (c : Cap) (r : Resource)
    (h : checkToken s (encodeReq c r) = true) : inScope s c r := by
  simp only [checkToken, encodeReq, decodeNats_encodeNats, Cap.ofCode_code,
    Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, h.2⟩

/-- The runtime check is exactly the scope predicate. -/
theorem checkToken_encodeReq_iff (s : Scope) (c : Cap) (r : Resource) :
    checkToken s (encodeReq c r) = true ↔ inScope s c r :=
  ⟨in_scope_encoding_sound s c r, in_scope_encoding_complete s c r⟩

end PCA.Isolation

