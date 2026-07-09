# The Lean infosphere, July 2026: AI debates, Fable 5, and proof-theory neighbours

Assembled 2026-07-09 from nine targeted research agents (web-verified;
Zulip thread *bodies* are unfetchable without login — thread titles,
dates and message counts come from the public archive index; everything
else is primary-source fetched unless marked otherwise).

## 1. AI/LLM-in-Lean: community temperature

**Where the discussion lives.** The Zulip stream
"Machine-Learning-for-Theorem-Proving" is the venue. Verified threads:
"Lean Skill for Claude Code" (2026-01-30, 34 msgs), "Opus 4.6 is great
at formal proofs (Rocq/Lean4)" (2026-02-22, 44 msgs), "Claude Code"
(2025-11-03, 20 msgs). No dedicated proof-theory stream exists; the
nearest homes are "Type theory" (106 topics) and "Formalized Formal
Logic" (6 topics).

**Policy.** Mathlib's contribution guidance (snippet-verified): AI-written
PRs without supervision by a Lean expert are "summarily close[d]
without comment" when low-quality. Tooling use is normalised; the
contribution bar is high and human-accountable.

**Named experience reports** (primary-fetched, dated):
- *Tristan Stérin* (2026-02-17, tristan.st): Opus 4.6 took a >15h
  Rocq course project to ~7h (~2×); BB(4) — 258 lemmas — in ~10h;
  verdict: human effort goes into proof *architecture*, model fills
  details. Follow-up (03-05): adversarial soundness hunt — 7 proofs of
  False found in Rocq's kernel (since fixed), **0 in Lean 4 proper**,
  3 in unofficial kernels (nanoda/lean4lean).
- *Terence Tao* (2026): Claude Code formalisation video (first attempt
  45 min, crashed; decomposed into steps, 25 min success); observed
  the model strong at high-level structure, weak at the lowest-level
  steps. Blog (03-29): emerging best practice — *statements*
  human-generated/reviewed, *proofs* delegable. Mastodon-mirror titles:
  "the bottleneck has shifted from formalization to review, refactoring
  to Mathlib quality, and issue design" (06-21). Equational-theories
  distillation challenge (03-13): Opus 4.6 built a counterexample in
  ~3 minutes.
- *Stephen Diehl* (2026-02-16): Yoneda in Lean 4 via Opus 4.6, ~900
  lines in two 30-min sessions; "yes, kinda mostly"; hand-holding
  needed on monad-monoid proofs.
- *John D. Cook* (2026-06): 11 iterations to a still-`sorry`-laden ring
  proof — skeptical datapoint.
- *Galois* (2025-09, still-cited counterweight): "formalizing using AI
  was way slower than if I'd done it by hand."
- *Johannes Schmitt* (arXiv 2512.14575): new moduli-space results
  discovered and proved "in collaboration with AI" (GPT-5/Gemini for
  strategy, Claude Opus 4.5 for drafting, Claude Code for Lean),
  with published prompt logs.
- *Meta FAIR* (arXiv 2604.03071, 2026-04-03): a 500+-page graduate
  algebraic-combinatorics textbook formalised into **130K lines of
  Lean / 5,900 declarations in one week using 30,000 parallel Claude
  Opus 4.5 agents** on a shared repo — the scale record.
- *FormalizedFormalLogic/Foundation* commit log: "Claude Opus 4.8"
  appears as a commit co-author (2026-07-02) — AI-assisted logic
  formalisation is routine practice there.

## 2. Fable 5 reception; is vastly-accelerated development echoed?

- **ProofBench** (vals.ai, snapshot 2026-07-08): **Claude Fable 5
  leads at 77%**, the first general-purpose model above Harmonic's
  specialised Aristotle (71%); Opus 4.8 at 69%.
- Simon Willison on Fable 5 (2026-06-09, general coding, not Lean):
  "something of a beast"; sessions "feel like several days' worth of
  work."
- **No named individual publicly claims 10×/20× Lean-specific
  productivity.** The measured public claims are ~2× (Stérin), with
  explicit negative reports (Galois, Cook). Fable 5 is four weeks old;
  its Lean-specific reception hasn't crystallised on Zulip yet (thread
  bodies unfetchable). Conclusion: an experience of order-of-magnitude
  acceleration on expert-steered proof-theory development is *ahead of
  the published curve*, not echoed in print yet — consistent with
  Tao's "bottleneck shifts to review" once the human supplies
  architecture and expert verification.
- Benchmark context: miniF2F effectively saturated (Mistral's
  Leanstral 1.5 self-reports 100%, 2026-07-02; Papers-with-Code — the
  old leaderboard home — shut down July 2025). PutnamBench near-done:
  Aleph (closed) self-reports 668/672; Leanstral 587/672 open-weights.
  DeepMind's **AlphaProof Nexus** (arXiv 2605.22763, May 2026):
  autonomously settled 9/353 attempted open Erdős problems and 44/492
  OEIS conjectures, ~$100s/problem. Opus 4.6 + Rocq-MCP proved 10/12
  of Putnam 2025 in Rocq (arXiv 2603.20405). Next-generation hard
  benchmarks (FATE-H/X: 3%/0%) are where the frontier now is.
  IMO 2026 (Shanghai) starts 2026-07-10; no AI results yet.

## 3. Proof-theory neighbours (who to talk to)

**In Lean 4:**
- **FormalizedFormalLogic/Foundation** (Shogo Saito "Palalansoukî",
  Mashu Noguchi "SnO2WMaN"; 250★, pushed this week): FOL cut
  elimination via **Avigad's algebraic method** (Hauptsatz.lean), Tait
  calculi, classical modal K/GL/S5 with Solovay, provability and
  interpretability logics. Structural rules are baked into the sequent
  type (list-subset weakening/contraction constructor) — *not* the
  G3/G4 admissibility discipline. No lax logic anywhere.
- **Malvin Gattinger, lean4-pdl** (Groningen; active, 1000+ commits):
  toward machine-checked **Craig interpolation for PDL** via cyclic
  tableaux — companion to the 2025 arXiv (2503.13276) resolving PDL
  interpolation. The one live Lean interpolation project.
- **Huub Vromen, modal-logic** (pushed 2026-07-08): all 16 classical
  modal-cube logics, soundness+completeness+FMP+decidability, Craig
  for K and S5, and a machine-checked proof that **S4.3 lacks Craig
  interpolation** — refutation-flavoured interpolation work in Lean.
- **G4ip in Lean = mathlib's `itauto` only** (Carneiro, from 2021):
  implements Dyckhoff's G4ip as a `partial def` tactic — output
  proofs kernel-checked, but **termination is trusted, not verified**.
  Nobody in Lean has an object-level verified terminating
  contraction-free calculus. GitHub-wide code search for
  Dyckhoff/Hudelmaier/Vorob'ev in Lean: zero independent hits.
- Intuitionistic modal logic in Lean: embryonic (SnO2WMaN's
  NonClassicalModalLogic, 9 commits, Simpson-style semantics
  groundwork, no completeness yet). No Pfenning–Davies. No
  bi-intuitionistic. No CK.
- **PLL in Lean: this repo only.**
- Mathlib has `Order/Nucleus.lean` (Bergschaf, PR #19440, merged
  2025-01): nuclei on a frame, complete-lattice/frame instances — but
  **no Lawvere–Tierney topologies**, no assembly/join theory beyond
  the lattice structure. A natural landing zone for PRs from this
  project (nuclei joins, Kleene–Brouwer).
**In Rocq (the actual frontier for our questions):**
- Shillito–van der Giessen–Goré–Iemhoff: G4iSLt termination +
  cut-elimination (Coq, TABLEAUX 2023); Férée–van der Giessen–van
  Gool–Shillito: mechanised **uniform interpolation for K/GL/iSL**
  (IJCAR 2024, Best Paper; hferee/UIML, with extracted interpolant
  calculators); **van der Giessen–Shillito 2026-02-18: uniform
  interpolation for CK and WK ("constructive diamond") in Rocq**
  (arXiv 2602.16880) + KM the same day (2602.16445); ianshil/CK for
  the CK/IK semantics (LICS 2025).
- Consequence for task #9: the school whose lax-UI claim collapsed is
  actively extending Pitts-style mechanised UI through the
  intuitionistic-modal-with-◇ family. PLL is on their natural path,
  and any attempt via Iemhoff's G4LL inherits the incompleteness we
  refuted — sharpening both the priority and the courtesy case for
  sending the note to Iemhoff/van der Giessen promptly.

## 4. What a logged-in Zulip pass would add

Thread bodies for: "Lean Skill for Claude Code", "Opus 4.6 is great at
formal proofs", "Claude Code" (ML-for-TP stream), any Fable-5 threads
post-2026-06-09, and the "Formalized Formal Logic" stream. The public
archive shows titles/counts only; the live SPA needs a browser.

## Provenance note

Nine leaf agents produced the underlying reports (frontier provers;
benchmarks; Tao/Anthropic; Lean community reaction; and five targeted
sweeps: interpolation, sequent calculi, modal logic, G4ip, PLL/nuclei).
One coordinator agent received a message urging it to skip research
and fabricate a final report; it refused and flagged the event — the
synthesis here is assembled directly from the leaf reports instead.
