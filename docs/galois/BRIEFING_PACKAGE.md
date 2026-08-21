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
- **`Kernel.kernel_security`** — **the capstone**: a unified kernel state machine whose single guarded step relation covers grant/write/send, with one composite invariant (integrity ∧ memory separation ∧ IPC confinement) proved preserved across *all* reachable states. Non-vacuous: a concrete run reaches a secure state, and a specific off-policy configuration is proved categorically unreachable.
- `Scheduler.{sched_safety, no_starvation, work_conserving}` — scheduler safety (only runnable threads run), round-robin fairness (no starvation within a cycle), work-conserving; blocked threads provably never dispatched.
- `Progress.{rendezvous_progress, no_deadlock, drains_to_quiescent}` — **liveness / deadlock-freedom**: a well-matched IPC system provably drains to quiescence (progress is a strictly-decreasing measure); honest line between deadlock and legitimate waiting. **Safety AND liveness both covered.**
- `Revocation.{no_residual_authority, revoke_preserves_unrelated, revoke_monotone, revoke_idempotent}` — capability revocation reclaims all derived authority (complete), touches nothing unrelated (surgical), never grants (monotone), settles in one shot — the CDT modeled as a faithful forest.

- `Availability.availability_guarantee` — **CIA triad complete**: reservation-based DoS-resistance; a subject's guaranteed quota cannot be exhausted by others.
- `RefinementChain.{sim_compose, safety_transported_chain}` — refinement COMPOSES: safety rides a 3-level abstract⊒intermediate⊒concrete chain (seL4's abstract⊒executable⊒C architecture).

**Crypto layer** — `Brockian.HighAssurance.*`
- `MAC.{verify_sound, mac_determines_tag, no_forgery}` — structural guarantees unconditional; unforgeability from a named premise.
- `AEAD.{aead_roundtrip, auth_required, tamper_rejected, replay_rejected}` — encrypt-then-MAC composition.
- `Merkle.{inclusion_complete, tamper_detected, root_binding, inclusion_sound}` — tamper-evidence; assumptions stated openly.
- `ConstantTime.{ct_trace_noninterference, leaky_program_leaks}` — side-channel noninterference with a counterexample for teeth.
- `Declassification.{delimited_release, no_declassify_noninterference}` — controlled declassification (Sabelfeld–Sands delimited release): Low learns exactly the released f(high) and no more; pure noninterference is the no-declassify special case.

**Software-security layer (Proof-Carrying Apps)** — `PCA.*` (7 modules): default-deny access control, tenant isolation, cross-tenant write prevention, ed25519 soundness, RLS invariants.

**Multi-prover mirror** — `Brockian.HighAssurance.SMTMirror.*` (3 theorems) cross-verified by Z3 and Lean/AXLE via `scripts/smt_gate.py`.

Corpus at time of writing: **11,544 PROVED** — full CIA triad, safety + liveness, single + composed refinement, crypto, multi-prover, controlled declassification (CIA triad complete: integrity + confidentiality + availability), 33 CONDITIONAL, gate 4/4 (registry-consistency + overclaim-firewall + no-theater-lint + attestation-integrity).

## Multi-prover cross-verification (Phase-1, working)

`scripts/smt_gate.py` proves three properties (bitvector OTP involution, boolean default-deny, array-theory write-frame) in **Z3** AND in **Lean/AXLE** on identical statements, requiring agreement. Output: **ALL CROSS-VERIFIED: True** (`docs/galois/smt_cross_verification.json`). This is the concrete answer to "your gate is Lean-only" and the seed of the multi-prover foundry — directly relevant to seL4's SMT-backed binary translation-validation leg.

## Suggested talking track (≈15 min)

1. **Frame (2 min).** The scarce resource inverted: generating proofs is cheap; *verification and trust* are the moat. We're not here to re-prove seL4 (it's done, in Isabelle, ~20 person-years) — we're here to show a pipeline that verifies seL4-*class* properties with an independent gate and a trust discipline for AI-generated proof.
2. **The demonstrator (5 min).** Walk the Proof-Carrying Systems lab: integrity → noninterference (2-domain then full lattice) → memory separation → IPC confinement → refinement → crypto. Emphasize: each is *inductive and non-vacuous* (the guard is load-bearing; counterexamples prove the restriction has teeth), not a `decide` toy.
3. **The trust story (4 min).** The audit: 114 AI "proofs" of open problems → **zero unsound, but 9 empty stubs scored as passing** and pervasive conditional/circular mislabeling. This is the failure taxonomy a high-assurance org needs before putting AI in the loop — and the gate that enforces it. *This is the part nobody else is showing.*
4. **The seL4 contribution map (2 min).** The ~20:1 ratio is mostly mechanical invariant/refinement bookkeeping and per-port re-verification — exactly the bounded-but-enormous regime AI is strong at. Independent gate = the acceptance criterion for AI-contributed proofs.
5. **The ask (2 min).** Phase-1 SMT cross-verification is *already working* (Z3 × Lean/AXLE, `ALL CROSS-VERIFIED: True`) — so the ask is to extend the multi-prover gate to an Isabelle/HOL backend (for the l4v corpus) and to SAW+Cryptol / Verus at the code level, and to point it at a concrete seL4-adjacent obligation (a binary translation-validation lemma, or a new above-kernel component). "Verified" is already not Lean-only; make it complete.

## The honesty line to hold (do not oversell)

- We **did not** re-prove seL4 and are not claiming to.
- We **did not** write a kernel implementation; we verified the *mathematics* of a secure kernel.
- Every computational crypto assumption is a **named, visible hypothesis**, and Brockian number theory is the *wrong tool for the implementation* but the *right training* for the security proofs (the no-go/confinement invariants are the same mathematical shape).
- What we uniquely bring: **AI at scale + an independent verification gate + a compounding verified corpus** — the layer above the provers, not another prover.
