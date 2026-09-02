# The output layer of the PLL decision procedure: proof terms and countermodel SVGs

*A DESIGN document, written 2026-09-02 against commit `2fb56c5` of the
FRJW thread.  Nothing here is implemented; every item marked BUILD is a
proposal with a type, not a claim.  Every signature quoted below was
either read directly in the source at that commit or confirmed with
`lake env lean` on a scratch file outside the tree; the file:line
anchors are at `2fb56c5`.*

**Register.**  PROVED means sorry-free with a `#guard_msgs`-pinned
`#print axioms`.  REFUTED means a kernel-checked countermodel exists.
OPEN means neither.  UNCERTAIN marks a statement I could not settle,
with what would settle it.  An object of `FRJWr`/`FRJWi` is a DISPROOF;
"proof" and "derivation" are reserved for `Gbu◯`, `LaxND`, `G4c`, `SC`
and the term calculus.

**The request being designed for** (Matthew, 2026-09-02): for a proof,
"a TM proof term and its Lax type (should be the same as the checked
formula)"; for a countermodel, "a nicely formatted svg of the
countermodel, minimised and also generated from the calculus (an easy
switch so I can see just minimised, i don't need both side by side)".

---

## 0. The two findings that shape the design

**(i) "TM proof term" is `PLLND.Tm`, and the bridge to it is missing.**
The repository has exactly one term calculus in Fairtlough--Mendler /
Moggi notation with `val` and monadic `let`: `PLLND.Tm`, in
`LaxLogic/PLLTerms.lean:60`.  It is intrinsically typed, so its Lax type
is its second index and equality with the checked formula is
definitional, not a runtime test.  It already has a printer,
`Tm.pretty` (`LaxLogic/PLLRun.lean:50`).  What does NOT exist is any
computable map into it: both routes into `Tm` land in `Nonempty`.

    exists_tm   : LaxND Γ φ  → Nonempty (Tm Γ φ)      LaxLogic/PLLTerms.lean:274
    G4cTm.toTm  : G4cTm Γ C  → Nonempty (Tm Γ C)      LaxLogic/PLLG4Term.lean:510

The obstruction is one constructor: `LaxND.iden` carries a `Prop`-level
membership `h : φ ∈ Γ`, which carries no occurrence data, whereas
`Tm.var` needs a de Bruijn witness `Var Γ φ`.  Because `PLLFormula` has
`DecidableEq`, the first occurrence can be COMPUTED from `h` by
structural recursion on `Γ`, using `h` only to rule out the empty case.
That closes the gap in about twenty lines.  Both functions were
typechecked in a scratch file at this commit and pin `[propext]` (§2.3);
they are not in the repository and are the first BUILD item.

**(ii) The output layer must attach to a RESULT TYPE, not to a route.**
The crown returns

    decideGbuWData (G : Form) : GbuRC G [] G ⊕ (Σ' t Γ, FRJWr G t Γ G)
                                                FRJ/Gbu/W/Saturate.lean:2388

and it does so by `decideOfStore (closureDB G) (closureDB_closed G)`,
where

    decideOfStore {G} (db : List (WRow G)) (hcl : DBClosed G db) :
        GbuRC G [] G ⊕ (Σ' t Γ, FRJWr G t Γ G)
                                                FRJ/Gbu/W/Saturate.lean:2375

The efficient procedure will replace the pair `(closureDB G,
closureDB_closed G)` and change nothing else.  So the whole output layer
can be built and exercised NOW against `decideGbuWData` on small cells,
and switched to the fast route later by editing one application.  This
is the single most important structural decision in the document, and it
is free.

---

## 1. The pipeline

### 1.1 As a diagram

```
                       φ : PLLFormula                     (the user's formula)
                             │
                             │  ofPLL                     FRJ/Bridge.lean:41
                             ▼
                        G : Form
                             │
          ┌──────────────────┴───────────────────┐
          │                                      │
   UNTRUSTED ENGINE                        (today: closureDB G)
   proposes a store                        FRJ/Gbu/W/Saturate.lean:1368
          │                                      │
          ▼                                      │
   VERIFIED CHECKER                              │
   checkClosed G db … = true                     │
          │  checkClosed_sound                   │  closureDB_closed
          ▼                                      ▼
        hcl : DBClosed G db  ◄───────────────────┘
                             │
                             ▼
              decideOfStore db hcl
                             │
              ┌──────────────┴───────────────┐
        .inl  │                              │  .inr
              ▼                              ▼
      GbuRC G [] G                  Σ' t Γ, FRJWr G t Γ G
              │  laxOfR                      │  modR
              ▼                              ▼
     LaxND [] (toPLL G)              K : FRJ.Kripke   (calculus-generated)
              │  ndToTm      BUILD          │  tabOf ∘ atomsOf
              ▼                              ▼
       Tm [] φ    (Lax type = φ)         raw : Tab
              │  Tm.pretty                   │  Tab.minimise G
              │  (option: Tm.normalize)      ▼
              ▼                          min : Tab
        the proof term,                      │  svgOfTab      BUILD
        with its Lax type                    ▼
                                     min.svg  /  calc.svg     (--view=min|calc|both)
```

### 1.2 As typed stages

Every declaration named below exists at `2fb56c5` unless marked BUILD.
The type given for a BUILD item is the type it must have.

| # | stage | declaration | type | status |
|---|---|---|---|---|
| 1 | read the formula | `FRJ.ofPLL` | `PLLFormula → Form` | exists, `FRJ/Bridge.lean:41` |
| 1' | read it back | `FRJ.toPLL` | `Form → PLLFormula` | exists, `FRJ/Bridge.lean:50` |
| 1'' | the two are inverse | `FRJ.toPLL_ofPLL` | `∀ φ, toPLL (ofPLL φ) = φ` | PROVED, `FRJ/Bridge.lean:58` |
| 2 | untrusted engine | `FRJ.Search.saturateO` | `{G} → (O : Ops G) → Config → DBO O × Stats` | exists, `FRJ/Search/Core.lean:121` |
| 2' | its W-instance | `FRJ.Search.W.wOps` | `(G : Form) → Ops G` | exists, `FRJ/Search/OpsW.lean:397` |
| 3 | engine store → checker rows | `rowsOfDBO` | `DBO (wOps G) → List (WRow G)` | **BUILD** (§4.1) |
| 4 | verified checker | `checkClosed` | `(G) → (db : List (WRow G)) → ClosureWitness G db → Bool` | **BUILD** (§4.2) |
| 4' | its soundness | `checkClosed_sound` | `checkClosed G db w = true → DBClosed G db` | **BUILD**, arity-conditional (§4.3) |
| 5 | the split | `FRJ.Gbu.W.decideOfStore` | `(db) → DBClosed G db → GbuRC G [] G ⊕ (Σ' t Γ, FRJWr G t Γ G)` | exists, `FRJ/Gbu/W/Saturate.lean:2375` |
| 5' | today's instance | `FRJ.Gbu.W.decideGbuWData` | `(G) → GbuRC G [] G ⊕ (Σ' t Γ, FRJWr G t Γ G)` | PROVED `[propext, Quot.sound]`, `Saturate.lean:2388` |
| P1 | proof → natural deduction | `FRJ.Gbu.laxOfR` | `GbuRC G Γ C → LaxND (Γ.map toPLL) (toPLL C)` | exists, `FRJ/Gbu/LaxND.lean:70` |
| P2 | membership → variable | `varOfMem` | `φ ∈ Γ → Var Γ φ` | **BUILD** (§2.3) |
| P3 | derivation → term | `ndToTm` | `LaxND Γ φ → Tm Γ φ` | **BUILD** (§2.3) |
| P4 | print the term | `PLLND.Tm.pretty` | `Tm Γ φ → String` | exists, `LaxLogic/PLLRun.lean:50` |
| P5 | normalise (optional) | `PLLND.Tm.normalize` | `Tm Γ φ → Tm Γ φ` | exists, `LaxLogic/PLLTopTop.lean:1300`, with `normalize_spec` at `:1309` |
| P6 | emit a re-checkable snippet | `tmSnippet` | `(name : String) → Tm [] φ → String` | **BUILD** (§2.5) |
| C1 | disproof → model | `FRJ.W.modR` | `FRJWr G t Γ C → Kripke` | exists, `FRJ/ExtractW.lean:488` |
| C1' | it refutes the goal | `FRJ.W.modR_countermodel` | `(d : FRJWr G t Γ G) → Countermodel (modR d) G` | PROVED, `FRJ/SoundW.lean:1864` |
| C2 | model → table | `FRJ.Search.tabOf` | `Kripke → List String → Tab` | exists, `FRJ/Search/Pin.lean:192` |
| C2' | the atoms to keep | `FRJ.Search.atomsOf` | `Form → List String` | exists, `FRJ/Search/Pin.lean:204` |
| C3 | minimise | `FRJ.Search.Tab.minimise` | `Tab → Form → Tab` | exists, `FRJ/Search/Pin.lean:176` |
| C4 | the frame check | `FRJ.Search.Tab.okB` | `Tab → Bool` | exists, `FRJ/Search/Pin.lean:52` |
| C5 | re-check the refutation | `FRJ.Search.Tab.refutes` | `Tab → Form → Bool` | exists, `FRJ/Search/Pin.lean:159` |
| C6 | decidable forcing | `FRJ.Kripke.decForce` | `(K) → (a : K.W) → (A : Form) → Decidable (K.force a A)` | PROVED, no axioms (`FRJ/Audit.lean:100`) |
| C7 | the pin | `FRJ.not_derivable_of_countermodel` | `(K : Kripke) → ¬ K.valid (ofPLL φ) → ¬ Nonempty (LaxND [] φ)` | PROVED, `FRJ/Bridge.lean:136` |
| C8 | draw | `svgOfTab` | `Tab → Form → SvgOpts → String` | **BUILD** (§3.5), from `tools/Cert.lean:243` |
| C9 | emit a Lean certificate | `FRJ.Search.render` | `Tab → String → String` | exists, `FRJ/Search/Pin.lean:213` |
| T | the CLI | `Tools/Decide.lean` | `lean_exe` | **BUILD** (§5) |

Two supporting facts the layer relies on and does not have to prove:

    PLL_iff_laxND : PLL (ofPLL φ) ↔ Nonempty (LaxND [] φ)     FRJ/Gbu/W/LaxND.lean:39
    decideLaxND (φ : PLLFormula) : Decidable (Nonempty (LaxND [] φ))
                                                              FRJ/Gbu/W/LaxND.lean:56

both PROVED `[propext, Quot.sound]`.

---

## 2. The proof side

### 2.1 What "TM proof term" refers to in this repository

There are five `Type`-valued derivation families over `PLLFormula`.
Only one of them is a term calculus in the sense of the request.

| family | file:line | what it is |
|---|---|---|
| `PLLND.Tm` | `LaxLogic/PLLTerms.lean:60` | **the computational metalanguage**: `var abort lam app pair fst snd inl inr case val bind`.  Term assignment for `LaxND`; `◯` as a strong monad, `val` for `laxIntro`, `bind` for `laxElim`. |
| `PLLND.LaxND` | `LaxLogic/PLLNDCore.lean:72` | natural deduction, `Type`-valued, so its constructors already ARE a Curry-style term syntax -- but with `Prop`-membership at `iden`, hence no variable names or indices. |
| `PLLND.G4cTm` | `LaxLogic/PLLG4Term.lean:56` | proof terms for the repaired sequent calculus `G4iLL″`; sixteen constructors, printed as rule trees (`(→L◯◯ (→L→ …) init)`). |
| `PLLND.PD` | `LaxLogic/PLLJudgmental.lean:56` | Pfenning--Davies dual-judgment derivations. |
| `PLLND.Focused.*` | `LaxLogic/PLLFocused.lean:85ff` | the focused calculus. |

**Recommendation: `Tm`.**  Three reasons.  (a) It is the only one whose
notation is F&M's `val`/`let`, which is what the request names.  (b) Its
type is its index, so "its Lax type should be the same as the checked
formula" is a typing constraint discharged by the elaborator rather than
a property to be tested.  (c) It is the object the repository's own
metatheory is about: strong normalisation of the interleaved reduction
(`LaxLogic/PLLTopTop.lean`), reducibility (`PLLReducibility.lean`) and
the equivalence

    G4c.equiv_tm : G4c Γ φ ↔ Nonempty (Tm Γ φ)     LaxLogic/PLLG4HComp.lean:115

PROVED `[propext, Quot.sound]`, are all statements about `Tm`.
`G4cTm` is the wrong object here: it belongs to a different calculus
from the one the decider derives in (`Gbu◯`), and its printer emits rule
trees, not λ-terms.

`Tm.pretty` writes, per `LaxLogic/PLLRun.lean:50-62`:

    var v       ↦  #n                     (n = v.idx, de Bruijn)
    abort t     ↦  abort t
    lam b       ↦  (λ. b)
    app f a     ↦  (f a)
    pair a b    ↦  ⟨a, b⟩
    fst t       ↦  t.1          snd t  ↦  t.2
    inl t       ↦  (inl t)      inr t  ↦  (inr t)
    case t u v  ↦  (case t of u | v)
    val t       ↦  val t
    bind t u    ↦  (let val• := t in u)

### 2.2 Are `LaxND` derivations already terms?

Yes and no, and the distinction is the whole of §2.3.  `LaxND` is
`Type`-valued and inductive, so a derivation IS a tree of constructors
and can be printed.  But its `iden` rule takes `h : φ ∈ Γ`, a `Prop`, so
a `LaxND` derivation does not record WHICH occurrence of `φ` in `Γ` it
used.  `Tm` fixes exactly this by replacing `Prop`-membership with the
`Type`-valued de Bruijn witness

    inductive Var : List PLLFormula → PLLFormula → Type
      | here  {Γ φ}   : Var (φ :: Γ) φ
      | there {Γ φ ψ} : Var Γ φ → Var (ψ :: Γ) φ    LaxLogic/PLLTerms.lean:54

and the file's own header says so (`PLLTerms.lean:12-17`).  In the
`Tm → LaxND` direction the map is a plain `def`,

    Tm.toND : Tm Γ φ → LaxND Γ φ                    LaxLogic/PLLTerms.lean:250

In the other direction the repository has only

    exists_tm : LaxND Γ φ → Nonempty (Tm Γ φ)       LaxLogic/PLLTerms.lean:274
    curry_howard : Nonempty (Tm Γ φ) ↔ Nonempty (LaxND Γ φ)   :298

### 2.3 BUILD: `varOfMem` and `ndToTm`

Since `PLLFormula` has `DecidableEq` (`LaxLogic/PLLFormula.lean:10`),
the first occurrence witnessed by a `Prop`-membership can be computed.

    varOfMem : ∀ {Γ : List PLLFormula} {φ : PLLFormula}, φ ∈ Γ → Var Γ φ
    ndToTm   : ∀ {Γ : List PLLFormula} {φ : PLLFormula}, LaxND Γ φ → Tm Γ φ

`ndToTm` is one clause per `LaxND` constructor, all twelve congruences,
with `iden h ↦ .var (varOfMem h)`.

**Validated in scratch, not committed**: both definitions were written
out and compiled with `lake env lean` against this commit; both pin

    'varOfMem' depends on axioms: [propext]
    'ndToTm'   depends on axioms: [propext]

so the route is choice-free, as the rest of the chain is.  This is
evidence that the BUILD item is a twenty-line exercise, not a claim that
it is in the repository: it is not.

One semantic caveat to record in the eventual docstring.  `varOfMem`
picks the FIRST occurrence of `φ` in `Γ`; a `LaxND` derivation that
"meant" a later one produces a different but equally well-typed term.
Since the emitted object is a proof of the same sequent, this is
harmless; it does mean `ndToTm ∘ Tm.toND` is not the identity on `Tm`.

### 2.4 Recovering the Lax type, and the check to display

For a formula `φ : PLLFormula` and `G := ofPLL φ`, the proof branch
yields

    d : GbuRC G [] G
    laxOfR d : LaxND ([].map toPLL) (toPLL G) = LaxND [] (toPLL (ofPLL φ))
    ndToTm (laxOfR d) : Tm [] φ                       by toPLL_ofPLL (a `simp` lemma)

so the type displayed alongside the term is `φ` itself, ON THE NOSE, and
"the Lax type should be the same as the checked formula" is discharged
by the elaborator.  There is nothing to test at runtime.

What IS worth displaying, and what the tool should print, is the
constraint made visible:

```
formula   ◯◯p ⊃ ◯p
verdict   PROVED  (Gbu◯ derivation, translated to LaxND, read as a Tm)
term      (λ. (let val• := #0 in #0))
type      ◯◯p ⊃ ◯p                          -- the term's index, by construction
```

and, for a check the KERNEL performs rather than the elaborator, the
re-elaboration snippet of §2.5.

### 2.5 BUILD: `tmSnippet`, and the two-pass Lean check

The repository already has this pattern twice: `G4cTm.snippet`
(`LaxLogic/PLLSearch.lean:980`) emits a paste-ready theorem, and
`tools/Cert.lean` shells out to `lake env lean` on what it wrote and
re-emits with the axiom lines Lean itself printed, under `#guard_msgs`
(`tools/Cert.lean:404-421`).  The proof side should do the same:

    tmSnippet (name : String) {φ : PLLFormula} (t : Tm [] φ) : String

emitting

```lean
def <name>_term : PLLND.Tm [] (<φ as source>) := <t as source>

theorem <name> : Nonempty (PLLND.LaxND [] (<φ as source>)) :=
  ⟨(<name>_term).toND⟩

#print axioms <name>
```

`srcOf : PLLFormula → String` already exists
(`LaxLogic/PLLSearch.lean:821`) for the formula half; the term half is a
second printer alongside `Tm.pretty`, since `pretty` produces `#n`
rather than `Var` constructor chains.  BUILD: `Tm.src`, modelled on
`G4cTm.src` (`PLLSearch.lean:946`).

This makes the "consistency check to display" a kernel check with a
pinned axiom line, not a claim in a report.

### 2.6 Two worked examples, BY HAND

Both are HAND-WORKED from the rules of §1.4 of `docs/frjw-explainer.md`
and of `LaxLogic/PLLTerms.lean:60`.  Neither is a machine-checked claim
about what the decider emits, because `ndToTm` does not exist yet.  (The
two terms themselves were typechecked in a scratch file, and
`Tm.pretty` printed exactly the strings below; that is evidence about
the terms, not about the pipeline.)

**Example A: `◯◯p ⊃ ◯p`** -- the multiplication of the monad.

Here `Sf^L(G) = [◯◯p, ◯p, p]`, so `L◯`'s side condition holds; and
`Cl([])` is empty of `◯◯p` (its `circ` clause would need `Clo [] p`),
so `R⊃ₙ` is the applicable implication rule.  `L◯`'s premise is
REGULAR and its context is `Z :: Ψ`, i.e. the principal `◯Z` is
replaced by `Z`:

```
      ─────────────── ax          [◯p ∈ {◯p}]
       ◯p ⇒g ◯p
      ─────────────── L◯          [◯◯p ∈ Sf^L(G)]
       ◯◯p ⇒g ◯p
      ─────────────── R⊃ₙ         [◯◯p ∉ Cl([])]
       ⇒g ◯◯p ⊃ ◯p
```

`laxOfR` sends `R⊃ₙ` to `impIntro` (`FRJ/Gbu/LaxND.lean:96`), `L◯` to
`laxElim` on the membership-derived `iden` with the premise renamed
into `Z :: Γ` (`:97`), and `ax` to `iden` (`:72`).  In `Tm`:

    lam (bind (var here) (var here))  :  Tm [] (◯◯p ⊃ ◯p)

typing, step by step, with `Γ₁ = [◯◯p]`:

    var here                        : Tm Γ₁ (◯◯p)              (bind's major premise, φ := ◯p)
    var here                        : Tm (◯p :: Γ₁) (◯p)       (bind's minor premise, ψ := p)
    bind (var here) (var here)      : Tm Γ₁ (◯p)
    lam …                           : Tm [] (◯◯p ⊃ ◯p)

printed:

    (λ. (let val• := #0 in #0))

**Example B: `(◯p ∧ ◯q) ⊃ ◯(p ∧ q)`** -- the strength/pairing law.

    lam (bind (fst (var here))
          (bind (snd (var (there here)))
            (val (pair (var (there here)) (var here)))))
      : Tm [] ((◯p ∧ ◯q) ⊃ ◯(p ∧ q))

with `Γ₁ = [◯p ∧ ◯q]`:

    var here                        : Tm Γ₁ (◯p ∧ ◯q)          #0
    fst (var here)                  : Tm Γ₁ (◯p)               bind major, φ := p
      -- context becomes p :: Γ₁
    var (there here)                : Tm (p :: Γ₁) (◯p ∧ ◯q)   #1
    snd …                           : Tm (p :: Γ₁) (◯q)        bind major, φ := q
      -- context becomes q :: p :: Γ₁
    var (there here)                : Tm (q :: p :: Γ₁) p      #1
    var here                        : Tm (q :: p :: Γ₁) q      #0
    pair … …                        : Tm (q :: p :: Γ₁) (p ∧ q)
    val …                           : Tm (q :: p :: Γ₁) (◯(p ∧ q))

printed:

    (λ. (let val• := #0.1 in (let val• := #1.2 in val ⟨#1, #0⟩)))

and it is already `Tm.normalize`-normal, since every `bind` has a
neutral major premise.

---

## 3. The countermodel side

### 3.1 The raw, calculus-generated model

The disproof branch hands over `⟨t, Γ, d⟩` with `d : FRJWr G t Γ G`.
The model is

    FRJ.W.modR d = (FRJ.W.preR d).toKripke (FRJ.W.preR_closed d)
                                                FRJ/ExtractW.lean:488

built in two layers.

**The pre-model** (`FRJ.PreModel`, `FRJ/Extract.lean:41`) carries
`W : Type`, an enumeration `elems` with `complete` (finiteness as DATA,
so no `Fintype.ofFinite` and no `Classical.choice`), a decidable partial
order `le` with a minimum `root`, a LABEL `lbl : W → List Form`, a
decidable preorder `rm ⊆ le`, and a decidable upward-closed `fal`.

**The shape, per rule** (`FRJ/ExtractW.lean:133-209`):

| rule | worlds contributed |
|---|---|
| `Ax^R` | one world, `PreModel.leaf (Ĝ_at ∖ F)`; barren, infallible |
| `∧∈ₖ`, `⊃∈`, `◯∈` | none: the model passes through unchanged (`preR d`) |
| `Ax^I` | none (`RegIdx = Empty`) |
| `Ax^I◯` | one world, `PreModel.leaf Θ` |
| `Lift`, `◯∉` | the model of the regular premise (`preR d`) |
| barren joins `⋈^At`, `⋈^∨`, `⋈^◯` | a fresh root labelled `base ++ kept`, below the disjoint union of the premises' models; no promises designated |
| promise joins `⋈^At_P`, `⋈^∨_P`, `⋈^◯_P` | the same, plus one component per PROMISE premise, and those components' roots become the fresh root's `Rm`-successors |
| fallible joins `⋈^At_F`, `⋈^∨_F` | the same, plus one declared FALLIBLE leaf (`PreModel.leafF`), designated as the fresh root's promise |

**The frame** of a join is `PJLe` (`FRJ/Extract.lean:73`) -- the fresh
root below everything, components keeping their own order, no relation
between distinct components -- and `PJRm` (`:81`) -- each component
keeps its own `rm`; the fresh root sees itself, and the `rm`-cones of
the roots of exactly the components the join designates as promises.

**The valuation** is the paper's `V(σ) = Lhs(σ) ∩ PV` adjusted for
fallibility (`FRJ/Extract.lean:295`):

    V w p  ↔  Form.atom p ∈ P.lbl w  ∨  P.fal w

so a fallible world forces every atom, which is what makes `fal_V` hold
and, with `fal_mono`, makes a fallible world force every formula.

So, in one line: **worlds are rule applications that create a world
(`Ax^R`, `Ax^I◯`, each join's fresh root, each fallible join's declared
leaf); the order is "join root below its premises' worlds"; `Rm` is
declared by the promise joins; `Fal` is exactly the fallible joins'
declared leaves; and a world forces the atoms in its label.**

`modR_countermodel` (`FRJ/SoundW.lean:1864`) is the PROVED statement
that this model refutes `G` at its root.

### 3.2 From a model to something printable

`FRJ.Kripke.W` is a `Type`, so the model cannot be printed directly.
The repository's answer is `FRJ.Search.Tab` (`FRJ/Search/Pin.lean:24`),
a model as plain tables:

    structure Tab where
      n : Nat
      root : Nat
      leT : List (List Bool)
      rmT : List (List Bool)
      falT : List Bool
      atomsT : List (List String)
      deriving Repr

with the round trip `tabOf : Kripke → List String → Tab` (`:192`),
`okB : Tab → Bool` (`:52`, every `Kripke` frame condition as one
decidable check), `toKripke : (T) → T.okB = true → T.root < T.n →
Kripke` (`:128`) and `refutes : Tab → Form → Bool` (`:159`).

The atom list to keep is `FRJ.Search.atomsOf G` (`:204`).  Note a small
display wart: `atomsOf` does not deduplicate, so
`atomsOf (◯p ⊃ p) = ["p", "p"]`.  The tool should call `.eraseDups`.

### 3.3 Minimisation: what it is, and what it is not

    Tab.restrict (keep : List Nat) : Tab           FRJ/Search/Pin.lean:165
    Tab.minimise (A : Form) : Tab                  FRJ/Search/Pin.lean:176

`minimise` is a fuel-bounded greedy loop: repeatedly find a world whose
deletion leaves a table that still `refutes A`, delete it, iterate to a
fixpoint.  Deleting the root fails `okB` (there would be no minimum), so
the root is protected without a special case.  Its file header states
the motivation exactly: "a derivation builds a world per rule
application... which is what makes the final `by decide` affordable"
(`FRJ/Search/Pin.lean:12-15`).

**Status: UNTRUSTED BUT CHECKED, and this is the right design, not a
compromise.**  There is no minimality theorem and none is needed.  What
the output must be sound about is that the displayed model refutes the
formula, and that is re-checked from scratch, by the kernel, on the
minimised table alone:

    (min.okB = true)  ∧  (min.root < min.n)  ∧  ¬ (min.toKripke …).valid (ofPLL φ)

the last by `decide`, using

    FRJ.Kripke.decForce : (K) → (a : K.W) → (A : Form) → Decidable (K.force a A)

which is PROVED to depend on NO axioms at all (`FRJ/Audit.lean:100`),
and then `FRJ.not_derivable_of_countermodel` (`FRJ/Bridge.lean:136`)
turns it into `¬ Nonempty (LaxND [] φ)`.  A bad minimisation can only
fail this check; it cannot mis-certify.  A wrong greedy step is
therefore a performance bug, never a soundness bug.

### 3.4 Bisimulation: what the repository has, and why it is not used here

The request's "minimised" could mean a bisimulation quotient.  The
survey of the repository says: do not go that way, and there is a
kernel-checked reason.

**The notion.**  The only bisimulation adequate for PLL is

    structure ABisim (A : String → Prop) (M N : ConstraintModel) where
      Z : M.W → N.W → Prop
      atoms  : Z w w' → ∀ a, A a → (w ∈ M.V a ↔ w' ∈ N.V a)
      fall   : Z w w' → (w ∈ M.F ↔ w' ∈ N.F)
      iforth : Z w w' → M.Ri w v  → ∃ v', N.Ri w' v' ∧ Z v v'
      iback  : Z w w' → N.Ri w' v' → ∃ v,  M.Ri w v  ∧ Z v v'
      mforth : Z w w' → M.Rm w u  → ∃ u', N.Rm w' u' ∧ Z u u'
      mback  : Z w w' → N.Rm w' u' → ∃ u,  M.Rm w u  ∧ Z u u'
                                                LaxLogic/PLLSemUI.lean:71

with FOUR zigzag clauses -- `Ri` and `Rm` separately -- because the `◯`
clause of forcing is `∀ β ≥ α, ∃ γ, Rm β γ ∧ γ ⊩ A`.  Its preservation
theorem is PROVED:

    force_iff_of_bisim (B : ABisim A M N) :
        (∀ a ∈ φ.atoms, A a) → B.Z w w' → (M.force w φ ↔ N.force w' φ)
                                                LaxLogic/PLLSemUI.lean:83

Since `Kripke.toConstraint` (`FRJ/Bridge.lean:78`) is a forgetful map
and `force_toConstraint` (`:95`) says forcing agrees in EVERY world
under `ofPLL`, an `ABisim (fun _ => True)` between two models'
constraint images transports `ofPLL φ`-forcing back to the `Kripke`
level.  So the notion is available and correct.

**Why not quotient.**  Quotienting a constraint model by
`≤`-equivalence does NOT preserve `◯`-forcing.  REFUTED, kernel-checked
at `[propext]`, by a four-world model in `wip/quot_cm.lean`:

    worlds  b ≈ b'  (≤ both ways), both below incomparable maximal t, t'
    Rm      reflexive, b → t, b' → t'
    V p     = {t, t'}

    fact1_equiv             : C4.Ri b b' ∧ C4.Ri b' b
    fact2_circ_p            : C4.force b (◯p)
    fact3_no_common_witness : ¬ ∃ c, C4.Rm b c ∧ C4.Rm b' c ∧ C4.force c p

so `[b]` has no `Rm`-witness class under the `∀∃` lift and refutes `◯p`
in the quotient while `b` forces it in the model.  This is precisely why
the `FRJ.Kripke` route to the finite model property was chosen over the
filtration route on 2026-09-02 (`FRJ/Gbu/LaxND.lean:18-22`), and
`LaxLogic/PLLDiagram.lean:381-383` already records the same rule for the
display layer: minimisation "removes the `Rᵢ`-equivalent twins by
deletion rather than quotienting, so the minimised models are posets."

**The one verified quotient** is by `Rm`-equivalence, not `≤`:
`Reject.qModel` with `Reject.qBisim : Bisim N (qModel N)` PROVED at
`[propext]` (`Reject/Reduce.lean:108,137`), followed by a separate
`Ri`-shrinking pass `refineM` with `refineM_force` (`:202,:274`).  Both
live on `ConstraintModel`, and `qModel` is `Rm`-antisymmetric but not
`Ri`-antisymmetric, so its output is not an `FRJ.Kripke`.  Reusing it
would mean leaving the `Kripke`/`Tab` world and giving up `okB`,
`decide` on `Tab`, and `render`.

**Recommendation: deletion (`Tab.minimise`), not quotient.**  Record
`qBisim` in the document as the road not taken, with the reason.

### 3.5 The SVG

**Two emitters exist, and neither is right as it stands.**

`PLLND.Diagram` (`LaxLogic/PLLDiagram.lean`) consumes `PLLND.FinCM`
(the OTHER model type, `LaxLogic/PLLCountermodelEmit.lean:44`), has
`hasseRi` (transitive reduction, `:48`), `riLayers`/`autoPos` (longest
chain layering, `:75,:87`) and `writeSvg` (`:247`).  Three
disqualifications for this job: (a) `FinCM` has no root field, so the
refuting world must be threaded separately; (b) `Rm` is not drawn as a
relation at all -- it merely RESTYLES an `Ri` cover edge (`:164-167`),
so an `Rm` pair that is not a Hasse edge of `≤` is INVISIBLE, and `Rm`
is exactly where the lax content lives; (c) its `#eval regen` (`:341`,
`:406`) rewrites `docs/figures/*.svg` on every `lake build LaxLogic`, a
hazard to inherit.  It also emits no caption and no background rect.

`FrjCert.toSvg` (`tools/Cert.lean:243`) consumes `FRJ.Search.Tab` --
already our model type -- draws the `≤`-Hasse in grey solid, EVERY
non-reflexive `Rm` pair in blue dashed, marks the root in red, labels
each world with the subformulas of the goal it forces (`labelOf`,
`:222`, via `forcesAt`, `:214`), and emits a caption line (`:275`).
That is nine tenths of the request already.

**Recommendation: hoist `tools/Cert.lean`'s renderer into a shared
`Tools/Svg.lean` and extend it there**, leaving `PLLDiagram` alone.

The extension, `svgOfTab (T : Tab) (G : Form) (o : SvgOpts) : String`:

* **nodes**: one per world, labelled with the atoms it forces, plus a
  marker for fallible worlds.  The current `labelOf` lists every forced
  subformula of `G`, which is right for a certificate and too long for a
  diagram; make it an option, `SvgOpts.label = atoms | subformulas`,
  default `atoms`, and use `⊥` (or a filled node) as the fallible
  marker.  A hover `<title>` can carry the full forced set, as
  `PLLDiagram` already does (`:178`).
* **order**: Hasse diagram of `≤` (transitive reduction), which
  `FrjCert.hasse` (`tools/Cert.lean:230`) already computes; DASHED
  lines WITH arrowheads.  (Matthew's ruling, 2026-09-02, replacing the
  draft's "plain grey, no arrowheads": "arrowheads on both `Ri` and
  `Rm`, and `Ri` dashed and `Rm` solid: it's a subrelation, i.e. a
  filling-in".)
* **modal relation**: every non-reflexive `Rm` pair, SOLID, in a
  distinct colour, with an arrowhead (the ruling above: `Rm ⊆ ≤` is the
  filled-in part of the order, so it is drawn solid inside the dashed
  order).  Keep `Rm` pairs that coincide with a Hasse edge as a SECOND,
  offset solid edge rather than a restyle, so `Rm` is always legible as
  its own relation.
* **root**: the existing red node, plus the word `root` in the label.
* **caption**: the formula, the verdict, the refuting world (always the
  root here, by `modR_countermodel`), the view (`minimised` /
  `from the calculus`) and, for `min`, the world count before and after.
* **layout**: `layerOf` in `tools/Cert.lean:239` counts predecessors,
  while `PLLDiagram.riLayers` measures the longest chain.  The longest
  chain is the correct Hasse layering; take `riLayers`'s metric.
  Crossing reduction exists once in the repository, in
  `tools/rho-hasse-svg.py:52-74` (eight barycentre sweeps); port it if
  models grow past a handful of worlds, not before.
* **theming**: no SVG in the repository is theme-aware.  Paint an
  explicit background rect and keep the palette light, as
  `FrjCert.toSvg` and `rho-hasse-svg.py` already do; do not inherit
  `PLLDiagram`'s transparent background.
* **escaping**: `Diagram.esc` (`PLLDiagram.lean:138`) escapes only
  `& < >`.  Labels here go into text nodes and `<title>`, so that is
  sufficient; if any label ever lands in an attribute, extend it.

**The switch.**  A single option, threaded identically through the CLI
and the command:

    --view=min | calc | both        default: min

* `min` (default): write one file, the minimised model.
* `calc`: write one file, the model exactly as `modR` built it.
* `both`: write TWO files, `<out>.min.svg` and `<out>.calc.svg`.  Never
  one image with two panels: the request is explicit that side by side
  is not wanted.

At command level, extending the existing `#draw` grammar
(`LaxLogic/PLLDiagramCmd.lean:73,80`):

    #decide φ to "out.svg"                  -- view = min
    #decide φ to "out.svg" view calc
    #decide φ to "out.svg" view both

### 3.6 A worked example: `◯p ⊃ p`

**Machine-computed**, in a scratch driver at this commit that runs
`decideGbuWData`, applies `modR`, `tabOf` and `minimise`, and prints the
tables.  The verdicts below are `#eval`-level evidence and prove
nothing; the kernel gate is `min.refutes G` re-checked by `decide` in
the emitted certificate.

The FRJW disproof returned (three nodes; this tree is also printed by
`wip/frjw_trace.lean` and transcribed in `docs/frjw-explainer.md` §7.2):

```
    ───────────────────── Ax^I    [p prime;  Θ = (Ĝ_at ∖ p) ++ Ĝ_imp ++ Ĝ_◯ = [◯p]]
     [] ; [◯p] → p
    ───────────────────── ⋈^At_F  [one premise; p ∉ Ξ^at = []; (J1), (J2) vacuous]
     blocked : [◯p] ⇒ p
    ───────────────────────────── ⊃∈   [◯p ∈ Cl([◯p])]
     blocked : [◯p] ⇒ ◯p ⊃ p
```

The extracted model, both views (they coincide here: `Ax^I` contributes
no world, so the fallible join produces exactly a fresh root and one
declared fallible leaf, and `minimise` can delete neither):

```
  n = 2      root = 0
  ≤          0 ≤ 0, 0 ≤ 1, 1 ≤ 1
  Rm         0 → 0, 0 → 1, 1 → 1
  Fal        {1}
  V          w0 ⊩ no atom;  w1 ⊩ p   (by fal_V: a fallible world forces everything)
```

The `--view=min` (default) and `--view=calc` pictures therefore agree.
Layout: `≤` upward as a Hasse diagram in solid grey, `Rm` as a dashed
arrow in blue, offset so it never hides behind a `≤` edge; nodes
labelled with the atoms they force; a filled node for a fallible world;
the root named in its label; the caption below.

```
   view = min  (default)                 view = calc

        ● w1   ⊥, p                           ● w1   ⊥, p
        │╎                                    │╎
     ≤  │╎ Rm                              ≤  │╎ Rm
        │╎                                    │╎
        ○ w0   root                           ○ w0   root

   ◯p ⊃ p  --  REFUTED at w0.            ◯p ⊃ p  --  REFUTED at w0.
   View: minimised, 2 worlds             View: from the calculus,
   (2 before minimisation).              2 worlds.
```

(Both relations run upward from `w0` to `w1`: the solid line is the `≤`
cover, the dotted line beside it is `Rm`.  Drawing them as two edges
rather than one restyled edge is the convention chosen in §3.5; the
filled node is the fallible world, and `w0`'s empty label means it
forces no atom.)

Reading the picture: `w0` forces `◯p` because its only `≤`-successors
are `w0` and `w1`, and `w1` is an `Rm`-successor of each and forces `p`
(it is fallible, so it forces everything); and `w0` refutes `p`, since
its label carries no atom.  Hence `w0 ⊮ ◯p ⊃ p`.

Read against §3.1: `w1` is the `⋈^At_F` join's declared fallible leaf,
designated as the fresh root's promise, which is exactly the dashed
`Rm` edge; `w0` is the join's fresh root, labelled `[◯p]`, whose
`atomsT` is empty because `◯p` is not an atom.

A second example where the two views DIFFER is what would exercise the
switch; the two candidates in range of the current (proof-object)
decider are recorded in §7 as unmeasured.  The switch itself does not
depend on finding one.

---

## 4. Wiring points for the untrusted engine and the verified checker

### 4.1 What the checker's rows are, and what an engine must supply

The checker's row type carries a DERIVATION, not just a sequent:

    inductive WSeq                      FRJ/Gbu/W/Dichotomy.lean:58
      | reg (t : Tag) (Γ : List Form) (C : Form)
      | irr (Ξ Θ : List Form) (C : Form)

    def WDer (G : Form) : WSeq → Type   FRJ/Gbu/W/Closure.lean:947
      | .reg t Γ C => FRJWr G t Γ C
      | .irr Ξ Θ C => FRJWi G Ξ Θ C

    structure WRow (G : Form) where     FRJ/Gbu/W/Closure.lean:952
      s : WSeq
      d : WDer G s

This is deliberate ("Rows carry their derivations as DATA (`WRow`), so
`WSaturated.1` needs no choice", `Closure.lean:941`).  It leaves an
untrusted engine two options, and the design should keep both open.

**Option A -- the engine builds derivations (in Lean).**  This is what
exists today: `FRJ.Search.W.WRS`/`WIS` (`FRJ/Search/OpsW.lean:33,39`)
each carry a `der` field, and the shared loop `saturateO`
(`FRJ/Search/Core.lean:121`) is generic over `Ops G`.  The engine's
speed comes from subsumption (`rsLeO`/`isLeO`, `Core.lean:63,67`) and
indexed insertion, where `closureDB` enumerates the whole well-formed
universe of `G` before searching a cell (`docs/frjw-explainer.md` §9,
item 1).  The only missing piece is a projection:

    rowsOfDBO {G} (db : DBO (wOps G)) : List (WRow G)          BUILD

which is a `map` on each list, `⟨.reg r.t r.ctx r.rhs, r.der⟩` and
`⟨.irr i.stab i.th i.rhs, i.der⟩`.  Trivial, and it makes today's engine
a candidate store producer at once.

**Option B -- the engine is outside Lean and emits a TRACE.**  A native
engine cannot ship an `FRJWr` term.  What it can ship is, per row, the
rule name and the indices of its premises among the earlier rows:

    structure Step where
      rule : RuleName            -- one of the 21 FRJW rules
      prem : List Nat            -- indices into the rows already reconstructed
      seq  : WSeq                -- the row it claims to derive

    reconstruct (G : Form) : List Step → Option (List (WRow G))   BUILD

`reconstruct` replays each step by applying the named constructor to the
already-reconstructed premises, discharging the rule's side conditions
by the `Decidable` instances the engine already uses at insertion time
(`OpsW.lean` does exactly this under `dite`-guards).  A step that fails
to reconstruct is dropped, not trusted; closedness is then checked on
what survives.  This is the repository's standing discover-then-pin
shape, one level up: the engine is untrusted and safe, and a defect in
it is a `none`, never a wrong verdict.

**Recommendation: design for B, ship A first.**  `rowsOfDBO` is an
afternoon; `reconstruct` is the real work and should not block the
output layer, which does not care which produced the store.

### 4.2 The checker

    DBClosed (G : Form) (db : List (WRow G)) : Prop
                                                FRJ/Gbu/W/Closure.lean:1179

is a structure with 21 fields, one per FRJW rule: 13 non-join clauses
(`axR andR1 andR2 impIn circIn axI andI1 andI2 orI impInI lift
circNotIn axIC`) and 8 join clauses (`joinAt joinOr joinCirc joinAtP
joinOrP joinCircP joinAtF joinOrF`).  Each says: the rule, fired at
STORED premises with its canonical kept chain and canonical conclusion
context, has a stored SUBSUMER.

The checker's obligation is therefore

    checkClosed (G : Form) (db : List (WRow G)) (w : ClosureWitness G db) : Bool
    checkClosed_sound : checkClosed G db w = true → DBClosed G db      BUILD

and the crown then takes over unchanged:

    decideOfStore db (checkClosed_sound h)
        : GbuRC G [] G ⊕ (Σ' t Γ, FRJWr G t Γ G)

The 13 non-join clauses are finite scans: each quantifies over one or
two stored rows and some formulas of `Sf^R(G)`/`Sf^L(G)`, all finite and
decidable (`cloB`, `subB`, `tagLeB`, `RefAt` and `Covers` all have
Boolean twins or `Decidable` instances already used by
`decWEvalI`/`decWEvalR`, `Closure.lean:999,1023`).  Nothing new is
needed there beyond the writing.

### 4.3 The arity question, and how to stay agnostic

Each of the 8 join clauses begins

    joinAt : ∀ {n : Nat} (Ξs Θs : Fin (n + 1) → List Form)
      (rhs : Fin (n + 1) → Form) (F : Form), …

quantifying over families of EVERY arity; the promise joins quantify
over two families, `{n k : Nat}`.  A Boolean `checkClosed` cannot
enumerate all of them.  The engine's own loop already caps the search
(`famsUpTo db.is cfg.jmax`, `famsUpTo db.rs cfg.pmax`,
`FRJ/Search/Core.lean:108,112`) and reports the cap
(`Stats.jmaxBinding`, `pmaxBinding`, `FRJ/Search/Engine.lean:620`, set
at `FRJ/Search/Core.lean:133-134`).

An in-progress result shows that unbounded arity is NEEDED in general:
the family `(⋀ⱼ (pⱼ ⊃ q)) ⊃ q` requires an n-ary join.  This design does
not solve that, and must not pretend to.  Three consequences for the
interface:

1. **`ClosureWitness` is a parameter, not a fixed type.**  Whatever the
   settled answer turns out to be -- an arity bound with a theorem
   "closure under arity ≤ N implies closure under all arities", a
   per-goal bound computed from `|Ĝ|`, or a witness family supplied by
   the engine per clause -- it enters here and nowhere else.
2. **A capped run is a FLAG, never a verdict.**  If the witness only
   covers arities up to some `N`, `checkClosed` must return `false` or
   carry the cap in its result, and the tool must report
   `FLAG: join arity capped at N` rather than a decision.  The standing
   repository rule (a timeout is a FLAG) applies verbatim.
3. **`checkClosed_sound` is arity-CONDITIONAL until the question is
   settled.**  Stating it unconditionally at a fixed `N` would be
   asserting the open theorem.  OPEN; it gets no declaration until it
   is proved (`CLAUDE.md` rule 1).

Meanwhile the output layer plugs into `decideOfStore`'s RESULT and is
completely independent of all of this.  That is the point of §0(ii).

### 4.4 Where the output layer plugs in

One function, at the seam:

    inductive Answer (φ : PLLFormula) where
      | proved   (t : Tm [] φ)
      | refuted  (fromCalc minimised : FRJ.Search.Tab)
                                                                    BUILD

(`calc` is a Lean keyword, hence `fromCalc`; the CLI flag stays
`--view=calc`, which is not an identifier.)

    answerOf (φ : PLLFormula)
        (dec : GbuRC (ofPLL φ) [] (ofPLL φ) ⊕ (Σ' t Γ, FRJWr (ofPLL φ) t Γ (ofPLL φ)))
        : Answer φ                                                  BUILD

with

    | .inl d      => .proved (toPLL_ofPLL φ ▸ ndToTm (laxOfR d))
    | .inr ⟨_,_,d⟩ =>
        let raw := FRJ.Search.tabOf (FRJ.W.modR d)
                     (FRJ.Search.atomsOf (ofPLL φ)).eraseDups
        .refuted raw (raw.minimise (ofPLL φ))

Everything downstream -- `Tm.pretty`, `tmSnippet`, `svgOfTab`, the
`--view` switch, the report -- consumes `Answer φ` and nothing else.
Swapping `decideGbuWData` for the engine-plus-checker route changes the
argument passed to `answerOf` and no other line.

---

## 5. Existing versus to-build

Effort is my estimate in hours of focused work, including the pins and a
smoke test, and excluding review.  (Standing correction: my refactor
estimates in this repository have run about 4× pessimistic; these are
the un-corrected numbers.)

| item | status | where | effort |
|---|---|---|---|
| `decideGbuWData`, `decideOfStore` | PROVED `[propext, Quot.sound]` | `FRJ/Gbu/W/Saturate.lean:2375,2388` | -- |
| `laxOfR` / `laxOfI` | PROVED | `FRJ/Gbu/LaxND.lean:70,103` | -- |
| `Tm`, `Tm.toND`, `Tm.pretty`, `Tm.normalize` | exist | `PLLTerms.lean:60,250`, `PLLRun.lean:50`, `PLLTopTop.lean:1300` | -- |
| `modR`, `modR_countermodel` | PROVED | `ExtractW.lean:488`, `SoundW.lean:1864` | -- |
| `Tab`, `okB`, `toKripke`, `refutes`, `tabOf`, `render` | exist | `FRJ/Search/Pin.lean` | -- |
| `Tab.minimise` | exists (untrusted, checked) | `FRJ/Search/Pin.lean:176` | -- |
| `Kripke.decForce` | PROVED, no axioms | `FRJ/Basic.lean:399`, pin `Audit.lean:100` | -- |
| `not_derivable_of_countermodel` | PROVED | `FRJ/Bridge.lean:136` | -- |
| SVG renderer over `Tab` (root, `Rm`, caption, forced labels) | exists | `tools/Cert.lean:243` | -- |
| `varOfMem`, `ndToTm` | **BUILD** (validated in scratch, `[propext]`) | `LaxLogic/PLLTerms.lean` (append) | 1--2 |
| `Tm.src` (term as elaborable source) | **BUILD**, model `G4cTm.src` | `LaxLogic/PLLRun.lean` | 2--3 |
| `tmSnippet` + two-pass Lean re-check | **BUILD**, model `tools/Cert.lean:404-421` | `Tools/Decide.lean` | 2--3 |
| hoist `FrjCert.toSvg` to `Tools/Svg.lean` | **BUILD** (move + generalise) | new `Tools/Svg.lean` | 2--3 |
| `svgOfTab` extensions (Hasse layering by longest chain, `Rm` as its own edge set, fallible marker, atom labels, caption, background) | **BUILD** | `Tools/Svg.lean` | 4--6 |
| `Answer` + `answerOf` | **BUILD** | `Tools/Decide.lean` | 1--2 |
| CLI `lake exe pll` with `--view=min\|calc\|both` | **BUILD** | `Tools/Decide.lean` + `lakefile.toml` | 3--4 |
| `#decide … to "…" view …` command | **BUILD**, model `PLLDiagramCmd.lean` | `Tools/DecideCmd.lean` | 2--3 |
| `rowsOfDBO` | **BUILD** | `FRJ/Search/OpsW.lean` (append) | 1 |
| `checkClosed`, 13 non-join clauses | **BUILD** | new `FRJ/Gbu/W/Check.lean` | 12--20 |
| `checkClosed`, 8 join clauses | **BUILD**, gated on the arity question | same | OPEN |
| `reconstruct` (external-engine trace replay) | **BUILD** | new `FRJ/Search/Replay.lean` | 15--25 |

Output layer alone (everything above the `rowsOfDBO` line): **17--26
hours**, and it is independent of the checker.

---

## 6. Decisions for Matthew

**Taken (Matthew, 2026-09-02, evening):** D1 `PLLND.Tm` ("what I meant
anyway"); D2 `ndToTm`, with the remark "not sure why we had to go
through ND as a more direct route from the `⊕` decider ought to be
possible" -- answered below; D3 untrusted-but-checked; D4 yes, hoist and
extend; D5 yes; D6 as recommended.  Also the SVG convention of §7.6:
arrowheads on both relations, `≤` dashed, `Rm` solid (a subrelation, a
filling-in); the layout bullets above are amended.

*On D2's remark.*  The `⊕` decider returns a `Gbu◯` derivation
`GbuRC G [] G`.  `Tm` is typed by natural-deduction contexts and
formulas (`Tm Γ φ`), so SOME translation from `Gbu◯` derivations to terms
is needed either way.  The direct route would be a 24-case mutual
recursion `GbuRC/GbuIC → Tm` mirroring `laxOfR`/`laxOfI` case for case
(each `Gbu◯` rule becomes the same term former as its `LaxND` image,
with `cut` as `(λx.q) p`).  Since `laxOfR` exists and is verified, the
cheaper path is to keep it and add the structural `ndToTm : LaxND Γ φ →
Tm Γ φ` (about thirteen cases, one per `LaxND` constructor), whose only
real content is `varOfMem`; the composite is the direct route with the
24 cases already paid for.  If a term is ever wanted WITHOUT the `LaxND`
detour, the direct translation is a mechanical copy of `laxOfR` with
term constructors and can be added then.

**D1. Which term calculus?**  `PLLND.Tm` (`LaxLogic/PLLTerms.lean:60`),
not `G4cTm` and not raw `LaxND`.
*Recommendation: `Tm`.*  It is the only one in `val`/`let` notation, its
Lax type is its index so the requested agreement with the checked
formula is definitional, it already has a printer, and it is the object
the strong-normalisation metatheory is about.

**D2. How to reach it?**  Build `varOfMem` + `ndToTm` (about twenty
lines, validated in scratch, `[propext]`), or go through `G4cTm` and
build a computable `G4cTm → Tm` instead.
*Recommendation: `ndToTm`.*  The `G4cTm` route needs the same work plus
a change of calculus (`Gbu◯` derivations are not `G4c` derivations), and
`G4cTm.toTm` is `Nonempty`-valued too, so it buys nothing.

**D3. Minimisation: verified or untrusted-but-checked?**
*Recommendation: untrusted-but-checked, reusing `Tab.minimise`.*  The
soundness the output needs is "the displayed model refutes φ", and that
is re-checked by `decide` on the minimised table with `decForce`
(axiom-free) and pinned by `not_derivable_of_countermodel`.  A minimality
theorem would be real work and would buy nothing the user can see.  Do
NOT quotient: the `≤`-quotient is REFUTED (`wip/quot_cm.lean`), and the
one verified quotient (`Reject.qBisim`, by `Rm`-equivalence) leaves the
`Kripke`/`Tab` world.

**D4. SVG generator: extend `PLLDiagram` or `tools/Cert.lean`?**
*Recommendation: hoist `tools/Cert.lean`'s renderer into a shared
`Tools/Svg.lean` and extend it there.*  It already consumes `Tab` (our
model type), has a root, draws every `Rm` pair, labels worlds by what
they force, and emits a caption.  `PLLDiagram` consumes a different
model type with no root, makes `Rm` invisible off the `≤`-Hasse, and
rewrites committed figures on every `lake build LaxLogic`.

**D5. Where does the tool live, and what is it called?**
*Recommendation: `Tools/Decide.lean`, registered as `lean_exe pll`,
beside `frjcert`; the elaboration-time command in `Tools/DecideCmd.lean`
as `#decide φ to "out.svg" [view min|calc|both]`.*  (`#decide` is free:
a scan of the `command` parser category in the environment reachable
from `LaxLogic/PLLDiagramCmd.lean` finds no syntax kind containing
"decide".)  Alternative: fold it
into `tools/Cert.lean`, which already parses sequents and shells out to
Lean -- rejected because `frjcert` is a certificate generator for the ρ
database and this is a user-facing decider; conflating them would make
one file answer to two audiences.

**D6. Should the emitted artefacts be re-elaborated by default?**  The
`frjcert` two-pass discipline (write, run `lake env lean` on it, re-emit
with the axiom lines Lean printed, under `#guard_msgs`) costs a few
seconds per answer.
*Recommendation: yes for the countermodel (`--check` on by default), and
opt-in for the proof term (`--check-term`).*  The countermodel's
`decide` is the only thing standing between a display bug and a wrong
verdict; the proof term's type is already the elaborator's business.

---

## 7. Not claimed

1. **Nothing in this document is implemented.**  Every BUILD item is a
   proposal with a type.  The two scratch validations (`varOfMem` /
   `ndToTm` compile at `[propext]`; the two example terms typecheck and
   `Tm.pretty` prints them as shown; `decideGbuWData` on `◯p ⊃ p`
   yields the two-world model of §3.6) were run outside the tree and
   are evidence about feasibility, not about a pipeline that exists.

2. **The join-arity question is OPEN and is not addressed here.**  The
   8 join clauses of `DBClosed` quantify over families of every arity;
   an in-progress result shows unbounded arity is needed in general.
   §4.3 leaves the interface agnostic and says what a capped run must
   report.  No arity-bounded `checkClosed_sound` is stated, because
   stating it would assert the open theorem.

3. **No performance claim.**  `decideGbuWData` is a proof object, not a
   practical procedure: `closureDB G` saturates the entire well-formed
   universe of `G` before any cell is searched, the strength law
   `(p ⊃ ◯q) ⊃ (◯p ⊃ ◯q)` does not finish in eight minutes in the
   interpreter, and where the wall is has not been measured
   (`docs/frjw-explainer.md` §9).  Nothing in this design changes that;
   it is what the untrusted engine is for.

4. **Whether the two views ever differ on a cell the current decider
   can reach is UNMEASURED.**  On `◯p ⊃ p` the raw and minimised models
   coincide (two worlds).  A batch over `p ∨ (p ⊃ ⊥)`, `◯⊥ ⊃ ⊥` and
   `◯p ⊃ ◯q` was started in the interpreter and had produced no output
   after fifteen minutes; it is recorded here as UNFINISHED, not as a
   negative result.  Cells large enough to build a redundant model are,
   on present evidence, also large enough to exhaust the proof object,
   which is exactly the wall item 3 above describes.  A sweep once the fast
   engine lands would settle it.  The `--view` switch does not depend on
   the answer, and the design of §3.5 is unaffected either way.

5. **`Tm.pretty` is a de Bruijn printer.**  It writes `#0`, `#1`, not
   named variables, and `let val•` rather than F&M's `let val x = e in
   f`.  A named-variable printer is a further BUILD item, not costed
   above; it needs a name supply and a shadowing discipline, and it is
   the only part of the proof-side output whose design is not settled by
   what already exists.

6. **The `Rm` display convention is a choice, not a fact.**  The two
   existing emitters disagree: dashed means "`≤`-only" in `PLLDiagram`
   and "`Rm`" in `tools/Cert.lean`.  §3.5 picks the second and adds an
   offset edge so `Rm` never hides behind a `≤` cover edge; that is a
   design decision to be reviewed against a drawn example, not a
   verified property.

7. **`FRJ.Kripke` models are FINITE ROOTED POSETS with a fallible set,
   and the countermodel displayed is a countermodel over that class.**
   That is stronger than a countermodel over `ConstraintModel`, since
   `Kripke.toConstraint` is a forgetful map and `force_toConstraint`
   makes the transfer exact (`FRJ/Bridge.lean:78,95`); it is worth
   saying in the caption, and it is why `finite_poset_model_property`
   (`FRJ/Gbu/W/LaxND.lean:50`) holds.
