# Galois Briefing Package — Index & Talking Track

*Built overnight, 2026-08-21. Everything here is machine-checked and independently gated; nothing is a mock-up.*

## The one-sentence version

We built the **verified security core of a capability microkernel** — the seL4 crown-jewel property classes (integrity, confidentiality, separation, capability confinement, refinement) plus a crypto-verification layer — generated with AI, **independently re-verified** by a second prover, axiom-audited, and honesty-gated; the pitch is a pipeline that attacks seL4's ~20:1 proof-cost with a trust discipline built for AI-in-the-loop.

## What's in this package

| Document | What it is |
|---|---|
| `CAPABILITY_BRIEF.md` | The main brief. Every verified theorem cited by name, the pipeline, the trust story, honest limits, a tiered engagement proposal. |
| `UNDERSTANDING_SEL4.md` | Honest map of seL4's refinement + security proof stack, and a per-activity contribution table (where AI + gate helps, where it does not). |
| Proof-Carrying Systems lab | `torus/labs/proof-carrying-systems.manifest.json` — every theorem rendered as an independent certificate on the honesty firewall (green PROVED; conditional/open never green). |
| This file | Index + suggested talking track. |

## The verified inventory (all AXLE-verified `lean-4.32.2`, axiom-clean)

**Kernel security core** — `Brockian.HighAssurance.*`
- `CapabilityIntegrity.integrity_confinement` — authority confinement, inductive, guard load-bearing.
- `TakeGrant.authority_confined` — take-grant closure bound (general form of integrity), honest sound-but-strict over-approx.
- `LatticeNoninterference.noninterference` — confidentiality over an arbitrary security lattice (Rushby unwinding).
- `Noninterference.noninterference` — the 2-domain confidentiality base case.
- `MemorySeparation.{frame, cross_subject_isolation, memory_separation}` — separation-kernel memory integrity.
- `IPCConfinement.ipc_confinement` — capability-gated endpoints; no unmediated channel.
- `Refinement.{forward_simulation, safety_transported}` — the seL4 refinement methodology, mechanized.
<!-- WAVE3-INVENTORY -->

**Crypto layer** — `Brockian.HighAssurance.*`
- `MAC.{verify_sound, mac_determines_tag, no_forgery}` — structural guarantees unconditional; unforgeability from a named premise.
- `AEAD.{aead_roundtrip, auth_required, tamper_rejected, replay_rejected}` — encrypt-then-MAC composition.
- `Merkle.{inclusion_complete, tamper_detected, root_binding, inclusion_sound}` — tamper-evidence; assumptions stated openly.
- `ConstantTime.{ct_trace_noninterference, leaky_program_leaks}` — side-channel noninterference with a counterexample for teeth.

**Software-security layer (Proof-Carrying Apps)** — `PCA.*` (7 modules): default-deny access control, tenant isolation, cross-tenant write prevention, ed25519 soundness, RLS invariants.

Corpus at time of writing: **11,450 PROVED**, 33 CONDITIONAL, gate 4/4 (registry-consistency + overclaim-firewall + no-theater-lint + attestation-integrity).

## Suggested talking track (≈15 min)

1. **Frame (2 min).** The scarce resource inverted: generating proofs is cheap; *verification and trust* are the moat. We're not here to re-prove seL4 (it's done, in Isabelle, ~20 person-years) — we're here to show a pipeline that verifies seL4-*class* properties with an independent gate and a trust discipline for AI-generated proof.
2. **The demonstrator (5 min).** Walk the Proof-Carrying Systems lab: integrity → noninterference (2-domain then full lattice) → memory separation → IPC confinement → refinement → crypto. Emphasize: each is *inductive and non-vacuous* (the guard is load-bearing; counterexamples prove the restriction has teeth), not a `decide` toy.
3. **The trust story (4 min).** The audit: 114 AI "proofs" of open problems → **zero unsound, but 9 empty stubs scored as passing** and pervasive conditional/circular mislabeling. This is the failure taxonomy a high-assurance org needs before putting AI in the loop — and the gate that enforces it. *This is the part nobody else is showing.*
4. **The seL4 contribution map (2 min).** The ~20:1 ratio is mostly mechanical invariant/refinement bookkeeping and per-port re-verification — exactly the bounded-but-enormous regime AI is strong at. Independent gate = the acceptance criterion for AI-contributed proofs.
5. **The ask (2 min).** Phase 1: bridge the gate to an SMT (Z3/CVC5) and Isabelle/HOL backend so "verified" isn't Lean-only — the step that targets seL4's binary translation-validation leg and makes the capability *complete*. Phase 2: SAW+Cryptol / Verus code-level.

## The honesty line to hold (do not oversell)

- We **did not** re-prove seL4 and are not claiming to.
- We **did not** write a kernel implementation; we verified the *mathematics* of a secure kernel.
- Every computational crypto assumption is a **named, visible hypothesis**, and Brockian number theory is the *wrong tool for the implementation* but the *right training* for the security proofs (the no-go/confinement invariants are the same mathematical shape).
- What we uniquely bring: **AI at scale + an independent verification gate + a compounding verified corpus** — the layer above the provers, not another prover.
