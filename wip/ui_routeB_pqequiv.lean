/-
Route (B), node **N4**, WP10: the redundancy obligation `PQEquiv`
(`wip/ui_routeB_n4q_thm.lean`) — its two EASY halves, proved, and the form
in which the HARD halves are kept.

`interpQ` (`wip/ui_routeB_n4q.lean`) is `interpP` with the loop check: the
∀p attack row of a parked compound implication `Q′ ⊃ N` becomes `⊥` when
`Q′ ∈ seen`, and the ∃p row's guarded conjunct becomes `⊤` on the same
test.  Dropping a disjunct of an `nOrAll` makes it STRONGER; dropping a
conjunct of an `nAndAll` makes it WEAKER.  So

    E^P  ⊢  E^Q          (∃p: the loop check only weakens)
    A^Q  ⊢  A^P          (∀p: the loop check only strengthens)

and the two halves are ONE simultaneous statement, because each aggregate's
rows carry the other mode in NEGATIVE position (`docs/n4-loopcheck.md` §3).
Both hold at EVERY `seen` and under EVERY reset policy `rst`: the level
below is consulted at every `seen`, so `seen` is universally quantified in
the induction hypothesis and the policy is never inspected.  That is why
the statement is over `interpG rst` and not only over `interpQ`.

The two HARD halves — `E^Q ⊢ E^P` and `A^P ⊢ A^Q` — are the redundancy
claim of `docs/n4-circfree-cases.md` §3.3.  They are NOT proved here; they
are named as a typed obligation (`PQHard`), and `PQEquiv` is reconstructed
from the pair.

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_n4q_thm
import wip.ui_routeB_wp4
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 1 · Pointwise transfer between aggregates

`nOrAll` and `nAndAll` are monotone along a POINTWISE entailment between
two lists.  `PW` carries that entailment as data, so both lemmas are
structural recursions and spend no cut. -/

/-- Pointwise entailment of two lists of interpolant rows, as data. -/
inductive PW : List Neg → List Neg → Type
  | nil : PW [] []
  | cons {x y : Neg} {l m : List Neg} :
      Inv [x] [] .tru y → PW l m → PW (x :: l) (y :: m)

/-- Concatenation. -/
def PW.append : ∀ {l m l' m' : List Neg}, PW l m → PW l' m' → PW (l ++ l') (m ++ m')
  | _, _, _, _, .nil, q => q
  | _, _, _, _, .cons d r, q => .cons d (r.append q)

/-- Every list entails itself pointwise. -/
def PW.refl : ∀ (l : List Neg), PW l l
  | [] => .nil
  | x :: l => .cons (idNeg x [x] (List.mem_cons_self ..)) (PW.refl l)

/-- Pointwise entailment of two maps over a common list. -/
def PW.mapBoth {β : Type} {gP gQ : β → Neg} :
    ∀ {L : List β}, (∀ b ∈ L, Inv [gP b] [] .tru (gQ b)) → PW (L.map gP) (L.map gQ)
  | [], _ => .nil
  | b :: L, h =>
      .cons (h b (List.mem_cons_self ..))
        (PW.mapBoth (fun c hc => h c (List.mem_cons_of_mem _ hc)))

/-- **`nOrAll` is monotone**, disjunct by disjunct. -/
def nOrAllPW : ∀ {l m : List Neg}, PW l m → Inv [nOrAll l] [] .tru (nOrAll m)
  | _, _, .nil => idNeg nBot [nBot] (List.mem_cons_self ..)
  | x :: l, y :: m, .cons d r =>
      upMerge (nOrAll (y :: m)) (R := .or (.down x) (.down (nOrAll l)))
        (List.mem_cons_self ..)
        (fun b hb => by
          have hb' : b = [x] ∨ b = [nOrAll l] := by
            simpa [invertPos] using hb
          -- `Or` cannot be eliminated into `Type`: decide the first disjunct
          -- (decidable equality on `List Neg`), and transport along the
          -- resulting equation.
          refine if h1 : b = [x] then ?_ else ?_
          · subst h1
            exact nOrAllIntro (List.mem_cons_self ..)
              (d.wk (fun Z hZ => by
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact absurd hZ List.not_mem_nil))
          · have h2 : b = [nOrAll l] := hb'.resolve_left h1
            subst h2
            exact Inv.stable (.rfoc (.or2 (.rel
              ((nOrAllPW r).wk (fun Z hZ => by
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact absurd hZ List.not_mem_nil))))))

/-- **`nAndAll` is monotone**, conjunct by conjunct. -/
def nAndAllPW : ∀ {l m : List Neg}, PW l m → Inv [nAndAll l] [] .tru (nAndAll m)
  | _, _, .nil => nTopIntro
  | x :: l, y :: m, .cons d r =>
      .andR
        (simHyp (H := x) (Γ := []) (Δ₀ := [nAnd x (nAndAll l)])
          (fun hs lf => .lfoc (hs _ (List.mem_cons_self ..)) (.and1 lf))
          (fun _ hc => absurd hc List.not_mem_nil) d)
        (simHyp (H := nAndAll l) (Γ := []) (Δ₀ := [nAnd x (nAndAll l)])
          (fun hs lf => .lfoc (hs _ (List.mem_cons_self ..)) (.and2 lf))
          (fun _ hc => absurd hc List.not_mem_nil) (nAndAllPW r))

/-- `attach.map` of a function that ignores its proof is a plain `map`. -/
theorem attachMapEq {α β : Type} (l : List α) (g : α → β) :
    l.attach.map (fun x => g x.1) = l.map g :=
  List.attach_map_val

/-- Pointwise entailment from an `attach.map` (the `interpP` side) to a plain
`map` (the `interpQ` side). -/
def PW.attachMap {α : Type} (l : List α) (fP : {x // x ∈ l} → Neg) (gQ : α → Neg)
    (h : ∀ x : {y // y ∈ l}, Inv [fP x] [] .tru (gQ x.1)) :
    PW (l.attach.map fP) (l.map gQ) := by
  have e : l.map gQ = l.attach.map (fun x : {y // y ∈ l} => gQ x.1) :=
    (attachMapEq l gQ).symm
  rw [e]
  exact PW.mapBoth (fun b _ => h b)

/-- The same, the other way round. -/
def PW.mapAttach {α : Type} (l : List α) (fP : {x // x ∈ l} → Neg) (gQ : α → Neg)
    (h : ∀ x : {y // y ∈ l}, Inv [gQ x.1] [] .tru (fP x)) :
    PW (l.map gQ) (l.attach.map fP) := by
  have e : l.map gQ = l.attach.map (fun x : {y // y ∈ l} => gQ x.1) :=
    (attachMapEq l gQ).symm
  rw [e]
  exact PW.mapBoth (fun b _ => h b)

/-! # Part 2 · Connective monotonicity

`∧` and `◯↓` are covariant and spend no cut; `↓· ⊃ ·` is contravariant in
its antecedent and spends two (`cutInv`, hence `Classical.choice` through
its `Type`-valued packaging). -/

/-- `∧` is monotone in both arguments. -/
def andMono {x x' y y' : Neg} (d₁ : Inv [x] [] .tru x') (d₂ : Inv [y] [] .tru y') :
    Inv [nAnd x y] [] .tru (nAnd x' y') :=
  .andR
    (simHyp (H := x) (Γ := []) (Δ₀ := [nAnd x y])
      (fun hs lf => .lfoc (hs _ (List.mem_cons_self ..)) (.and1 lf))
      (fun _ hc => absurd hc List.not_mem_nil) d₁)
    (simHyp (H := y) (Γ := []) (Δ₀ := [nAnd x y])
      (fun hs lf => .lfoc (hs _ (List.mem_cons_self ..)) (.and2 lf))
      (fun _ hc => absurd hc List.not_mem_nil) d₂)

/-- `◯↓·` is monotone. -/
def circMono {x y : Neg} (d : Inv [x] [] .tru y) :
    Inv [Neg.circ (.down x)] [] .tru (Neg.circ (.down y)) :=
  .circR (.stable (.lfoc (List.mem_cons_self ..)
    (.circL (.downL (.stable (.laxOf (.rfoc (.rel
      (d.wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact absurd hZ List.not_mem_nil))))))))))

/-- Using a shifted implication: `[E, ↓E ⊃ A] ⊢ A`. -/
def impUse {E A : Neg} : Inv [E, Neg.imp (.down E) A] [] .tru A :=
  simHyp (H := A) (Γ := []) (Δ₀ := [E, Neg.imp (.down E) A])
    (fun hs lf =>
      .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        (.impL (.rfoc (.rel (idNeg E _ (hs _ (List.mem_cons_self ..))))) lf))
    (fun _ hc => absurd hc List.not_mem_nil)
    (idNeg A [A] (List.mem_cons_self ..))

/-- Using an atom-guarded implication: `[↑a, a ⊃ A] ⊢ A`. -/
def impUseAtom {a : String} {A : Neg} :
    Inv [Neg.up (.atom a), Neg.imp (.atom a) A] [] .tru A :=
  simHyp (H := A) (Γ := []) (Δ₀ := [Neg.up (.atom a), Neg.imp (.atom a) A])
    (fun hs lf =>
      .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        (.impL (.rfoc (.init (hs _ (List.mem_cons_self ..)))) lf))
    (fun _ hc => absurd hc List.not_mem_nil)
    (idNeg A [A] (List.mem_cons_self ..))

/-- `↓· ⊃ ·` is antitone in its antecedent and monotone in its consequent. -/
noncomputable def impMono {a a' b b' : Neg}
    (d₁ : Inv [a'] [] .tru a) (d₂ : Inv [b] [] .tru b') :
    Inv [Neg.imp (.down a) b] [] .tru (Neg.imp (.down a') b') := by
  refine .impR (.downL ?_)
  exact cut2N' (cut2N d₁ impUse)
    (d₂.wk (fun Z hZ => by
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_self ..
      · exact absurd hZ List.not_mem_nil))

/-- `a ⊃ ·` is monotone (an atomic antecedent, so no contravariance). -/
noncomputable def impMonoAtom {a : String} {b b' : Neg} (d : Inv [b] [] .tru b') :
    Inv [Neg.imp (.atom a) b] [] .tru (Neg.imp (.atom a) b') := by
  refine .impR (.atomL ?_)
  exact cut2N' impUseAtom
    (d.wk (fun Z hZ => by
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_self ..
      · exact absurd hZ List.not_mem_nil))

/-! # Part 3 · The loop-checked recursion's own equations

`interpP`'s are already named (`LJF/OFuelPMin.lean`).  The step form makes
`interpG`'s processing clauses definitional; only the aggregate needs the
saturation hypothesis. -/

section QEq
variable {rst : List Pos → List Pos} {p : String} {f : Nat}

theorem qAtom (a : String) (todo done : List Neg) (g : Option Neg) (seen : List Pos) :
    interpG rst p (f + 1) (.up (.atom a) :: todo) done g seen
      = interpG rst p f todo (.up (.atom a) :: done) g (rst seen) := rfl

theorem qFlsE (todo done : List Neg) (seen : List Pos) :
    interpG rst p (f + 1) (.up .fls :: todo) done none seen = nBot := rfl

theorem qFlsA (todo done : List Neg) (G : Neg) (seen : List Pos) :
    interpG rst p (f + 1) (.up .fls :: todo) done (some G) seen = nTop := rfl

theorem qOrE (P₁ P₂ : Pos) (todo done : List Neg) (seen : List Pos) :
    interpG rst p (f + 1) (.up (.or P₁ P₂) :: todo) done none seen
      = nOrAll ((invertPos (Pos.or P₁ P₂)).map
          (fun b => interpG rst p f (b ++ todo) done none (rst seen))) := rfl

theorem qOrA (P₁ P₂ : Pos) (todo done : List Neg) (G : Neg) (seen : List Pos) :
    interpG rst p (f + 1) (.up (.or P₁ P₂) :: todo) done (some G) seen
      = nAndAll ((invertPos (Pos.or P₁ P₂)).map
          (fun b => .imp (.down (interpG rst p f (b ++ todo) done none (rst seen)))
                         (interpG rst p f (b ++ todo) done (some G) (rst seen)))) := rfl

theorem qDown (M : Neg) (todo done : List Neg) (g : Option Neg) (seen : List Pos) :
    interpG rst p (f + 1) (.up (.down M) :: todo) done g seen
      = interpG rst p f (M :: todo) done g (rst seen) := rfl

theorem qAnd (M N : Neg) (todo done : List Neg) (g : Option Neg) (seen : List Pos) :
    interpG rst p (f + 1) (.and M N :: todo) done g seen
      = interpG rst p f (M :: N :: todo) done g (rst seen) := rfl

theorem qImpFls (N : Neg) (todo done : List Neg) (g : Option Neg) (seen : List Pos) :
    interpG rst p (f + 1) (.imp .fls N :: todo) done g seen
      = interpG rst p f todo done g (rst seen) := rfl

theorem qParkAtom (a : String) (N : Neg) (todo done : List Neg) (g : Option Neg)
    (seen : List Pos) :
    interpG rst p (f + 1) (.imp (.atom a) N :: todo) done g seen
      = interpG rst p f todo (.imp (.atom a) N :: done) g (rst seen) := rfl

theorem qParkOr (Q₁ Q₂ : Pos) (N : Neg) (todo done : List Neg) (g : Option Neg)
    (seen : List Pos) :
    interpG rst p (f + 1) (.imp (.or Q₁ Q₂) N :: todo) done g seen
      = interpG rst p f todo (.imp (.or Q₁ Q₂) N :: done) g (rst seen) := rfl

theorem qParkShift (P' : Pos) (N : Neg) (todo done : List Neg) (g : Option Neg)
    (seen : List Pos) :
    interpG rst p (f + 1) (.imp (.down (.up P')) N :: todo) done g seen
      = interpG rst p f todo (.imp (.down (.up P')) N :: done) g (rst seen) := rfl

theorem qParkAnd (M₁ M₂ N : Neg) (todo done : List Neg) (g : Option Neg)
    (seen : List Pos) :
    interpG rst p (f + 1) (.imp (.down (.and M₁ M₂)) N :: todo) done g seen
      = interpG rst p f todo (.imp (.down (.and M₁ M₂)) N :: done) g (rst seen) := rfl

theorem qParkDyk (Q' : Pos) (N' N : Neg) (todo done : List Neg) (g : Option Neg)
    (seen : List Pos) :
    interpG rst p (f + 1) (.imp (.down (.imp Q' N')) N :: todo) done g seen
      = interpG rst p f todo (.imp (.down (.imp Q' N')) N :: done) g (rst seen) := rfl

theorem qParkBox (Q : Pos) (todo done : List Neg) (g : Option Neg) (seen : List Pos) :
    interpG rst p (f + 1) (.circ Q :: todo) done g seen
      = interpG rst p f todo (.circ Q :: done) g (rst seen) := rfl

theorem qParkCimp (Q' : Pos) (N : Neg) (todo done : List Neg) (g : Option Neg)
    (seen : List Pos) :
    interpG rst p (f + 1) (.imp (.down (.circ Q')) N :: todo) done g seen
      = interpG rst p f todo (.imp (.down (.circ Q')) N :: done) g (rst seen) := rfl

/-- The fire equation for the loop-checked recursion. -/
theorem qFire {done : List Neg} {a : String} {N : Neg} {rest : List Neg}
    (hf : findFire done (splits done) = some (a, N, rest))
    (g : Option Neg) (seen : List Pos) :
    interpG rst p (f + 1) [] done g seen = interpG rst p f [N] rest g (rst seen) := by
  show stepQ rst p (interpG rst p f) [] done g seen = _
  rw [stepQ, hf]

/-- The aggregate equation for the loop-checked recursion. -/
theorem qAgg {done : List Neg} (hsat : Saturated done) (g : Option Neg)
    (seen : List Pos) :
    interpG rst p (f + 1) [] done g seen
      = aggQ rst p (interpG rst p f) done g seen := by
  show stepQ rst p (interpG rst p f) [] done g seen = _
  rw [stepQ, hsat]

/-! The aggregate, clause by clause. -/

theorem aggQ_none (prev : ApproxQ) (done : List Neg) (seen : List Pos) :
    aggQ rst p prev done none seen = nAndAll (eRowsQ rst p prev done seen) := rfl

theorem aggQ_imp (prev : ApproxQ) (done : List Neg) (Q : Pos) (N : Neg)
    (seen : List Pos) :
    aggQ rst p prev done (some (.imp Q N)) seen
      = nAndAll ((invertPos Q).map (fun b =>
          .imp (.down (prev b done none seen)) (prev b done (some N) seen))) := rfl

theorem aggQ_and (prev : ApproxQ) (done : List Neg) (M N : Neg) (seen : List Pos) :
    aggQ rst p prev done (some (.and M N)) seen
      = nAnd (prev [] done (some M) seen) (prev [] done (some N) seen) := rfl

theorem aggQ_atomIf (prev : ApproxQ) (done : List Neg) (q : String)
    (seen : List Pos) :
    aggQ rst p prev done (some (.up (.atom q))) seen
      = if atomMem q done then nTop
        else nOrAll (atomHead p q ++
              aRowsQ rst p prev done (.up (.atom q)) false seen) := rfl

theorem aggQ_atomT (prev : ApproxQ) {done : List Neg} {q : String}
    (hq : atomMem q done = true) (seen : List Pos) :
    aggQ rst p prev done (some (.up (.atom q))) seen = nTop := by
  rw [aggQ_atomIf, if_pos hq]

theorem aggQ_atomF (prev : ApproxQ) {done : List Neg} {q : String}
    (hq : ¬ atomMem q done = true) (seen : List Pos) :
    aggQ rst p prev done (some (.up (.atom q))) seen
      = nOrAll (atomHead p q ++ aRowsQ rst p prev done (.up (.atom q)) false seen) := by
  rw [aggQ_atomIf, if_neg hq]

theorem aggQ_fls (prev : ApproxQ) (done : List Neg) (seen : List Pos) :
    aggQ rst p prev done (some (.up .fls)) seen
      = nOrAll (aRowsQ rst p prev done (.up .fls) false seen) := rfl

theorem aggQ_or (prev : ApproxQ) (done : List Neg) (P₁ P₂ : Pos) (seen : List Pos) :
    aggQ rst p prev done (some (.up (.or P₁ P₂))) seen
      = nOrAll ([prev [] done (some (.up P₁)) seen,
                 prev [] done (some (.up P₂)) seen] ++
          aRowsQ rst p prev done (.up (.or P₁ P₂)) false seen) := rfl

theorem aggQ_down (prev : ApproxQ) (done : List Neg) (M : Neg) (seen : List Pos) :
    aggQ rst p prev done (some (.up (.down M))) seen
      = nOrAll ([prev [] done (some M) seen] ++
          aRowsQ rst p prev done (.up (.down M)) false seen) := rfl

theorem aggQ_circ (prev : ApproxQ) (done : List Neg) (Q : Pos) (seen : List Pos) :
    aggQ rst p prev done (some (.circ Q)) seen
      = .circ (.down (nOrAll (laxPrefixQ prev done seen Q ++
          aRowsQ rst p prev done (.circ Q) true seen))) := rfl

end QEq

/-! # Part 4 · The two easy halves -/

/-- The two easy halves at one fuel level, at EVERY station, goal and
`seen`. -/
structure EasyLvl (rst : List Pos → List Pos) (p : String) (f : Nat) : Type where
  /-- `∃p`: `interpP` entails the loop-checked interpolant. -/
  E : ∀ (todo done : List Neg) (seen : List Pos),
        Inv [interpP p f todo done none] [] .tru (interpG rst p f todo done none seen)
  /-- `∀p`: the loop-checked interpolant entails `interpP`. -/
  A : ∀ (todo done : List Neg) (G : Neg) (seen : List Pos),
        Inv [interpG rst p f todo done (some G) seen] [] .tru
            (interpP p f todo done (some G))

/-- Fuel 0: both sides are the same default. -/
def easyLvl_zero (rst : List Pos → List Pos) (p : String) : EasyLvl rst p 0 where
  E := fun _ _ _ => nTopIntro
  A := fun _ _ _ _ => nBotElim _ (List.mem_cons_self ..)

section Step
variable {rst : List Pos → List Pos} {p : String} {f : Nat}

/-- The `∀p` row of a parked compound implication transfers: the cut row is
`⊥`, and the retained row is conjunct-wise. -/
noncomputable def aParkRow (ih : EasyLvl rst p f) (done : List Neg) (Qa : Pos)
    (N : Neg) (rest : List Neg) (goal : Neg) (seen : List Pos) :
    Inv [parkRowA rst (interpG rst p f) done Qa N rest goal seen] [] .tru
        (nAnd (interpP p f [] done (some (.up Qa)))
              (interpP p f [N] rest (some goal))) := by
  unfold parkRowA
  split
  · exact nBotElim _ (List.mem_cons_self ..)
  · exact andMono (ih.A [] done (.up Qa) (Qa :: seen))
                  (ih.A [N] rest goal (rst seen))

/-- The `∃p` row of a parked compound implication transfers: the cut conjunct
is `⊤`, and the retained conjunct is the guarded implication, contravariant
in its guard. -/
noncomputable def eParkRow (ih : EasyLvl rst p f) (done : List Neg) (Qa : Pos)
    (N : Neg) (rest res : List Neg) (seen : List Pos) :
    Inv [nAnd (.imp (.down (interpP p f [] done (some (.up Qa))))
                    (interpP p f [N] rest none))
              (interpP p f res rest none)] [] .tru
        (parkRowE rst (interpG rst p f) done Qa N rest res seen) := by
  unfold parkRowE
  refine andMono ?_ (ih.E res rest (rst seen))
  split
  · exact nTopIntro
  · exact impMono (ih.A [] done (.up Qa) (Qa :: seen)) (ih.E [N] rest (rst seen))

/-- The `∃p` station rows transfer. -/
noncomputable def eRowsPW (ih : EasyLvl rst p f) (done : List Neg)
    (seen : List Pos) :
    PW (eConjRowsP p f done) (eRowsQ rst p (interpG rst p f) done seen) := by
  unfold eConjRowsP eRowsQ
  refine PW.attachMap (splits done) _ _ ?_
  rintro ⟨⟨X, rest⟩, hXr⟩
  match X with
  | .up (.atom a) => exact idNeg _ _ (List.mem_cons_self ..)
  | .imp (.atom a) N =>
      by_cases hap : a = p
      · simp only [pGuard, if_pos hap]; exact nTopIntro
      · simp only [pGuard, if_neg hap]
        exact impMonoAtom (ih.E [N] rest (rst seen))
  | .imp (.down (.imp Q' N')) N =>
      exact eParkRow ih done (.down (.imp Q' N')) N rest [.imp (.down N') N] seen
  | .circ Q => exact circMono (ih.E [.up Q] rest (rst seen))
  | .imp (.down (.circ Q')) N =>
      exact eParkRow ih done (.down (.circ Q')) N rest [] seen
  | .imp (.or Qa Qb) N => exact eParkRow ih done (.or Qa Qb) N rest [] seen
  | .imp (.down (.up Pa)) N => exact eParkRow ih done (.down (.up Pa)) N rest [] seen
  | .imp (.down (.and Ma Mb)) N =>
      exact eParkRow ih done (.down (.and Ma Mb)) N rest [] seen
  | .up .fls => exact nTopIntro
  | .up (.or _ _) => exact nTopIntro
  | .up (.down _) => exact nTopIntro
  | .imp .fls _ => exact nTopIntro
  | .and _ _ => exact nTopIntro

/-- The `∀p` station rows transfer at a shifted goal (no box row). -/
noncomputable def aRowsTruPW (ih : EasyLvl rst p f) (done : List Neg) (G : Pos)
    (seen : List Pos) :
    PW (aRowsQ rst p (interpG rst p f) done (.up G) false seen)
       (truStationRowsP p f done G) := by
  unfold aRowsQ truStationRowsP
  refine PW.mapAttach (splits done) _ _ ?_
  rintro ⟨⟨X, rest⟩, hXr⟩
  match X with
  | .imp (.atom a) N =>
      by_cases hap : a = p
      · simp only [pGuard, if_pos hap]; exact nBotElim _ (List.mem_cons_self ..)
      · simp only [pGuard, if_neg hap]
        exact andMono (idNeg _ _ (List.mem_cons_self ..))
                      (ih.A [N] rest (.up G) (rst seen))
  | .imp (.down (.imp Q' N')) N =>
      exact aParkRow ih done (.down (.imp Q' N')) N rest (.up G) seen
  | .imp (.down (.circ Q')) N =>
      exact aParkRow ih done (.down (.circ Q')) N rest (.up G) seen
  | .imp (.or Qa Qb) N => exact aParkRow ih done (.or Qa Qb) N rest (.up G) seen
  | .imp (.down (.up Pa)) N =>
      exact aParkRow ih done (.down (.up Pa)) N rest (.up G) seen
  | .imp (.down (.and Ma Mb)) N =>
      exact aParkRow ih done (.down (.and Ma Mb)) N rest (.up G) seen
  | .circ R => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.atom _) => exact nBotElim _ (List.mem_cons_self ..)
  | .up .fls => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.or _ _) => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.down _) => exact nBotElim _ (List.mem_cons_self ..)
  | .imp .fls _ => exact nBotElim _ (List.mem_cons_self ..)
  | .and _ _ => exact nBotElim _ (List.mem_cons_self ..)

/-- The `∀p` station rows transfer at a ◯-goal (the box row is present). -/
noncomputable def aRowsCircPW (ih : EasyLvl rst p f) (done : List Neg) (G : Pos)
    (seen : List Pos) :
    PW (aRowsQ rst p (interpG rst p f) done (.circ G) true seen)
       (circStationRowsP p f done G) := by
  unfold aRowsQ circStationRowsP
  refine PW.mapAttach (splits done) _ _ ?_
  rintro ⟨⟨X, rest⟩, hXr⟩
  match X with
  | .imp (.atom a) N =>
      by_cases hap : a = p
      · simp only [pGuard, if_pos hap]; exact nBotElim _ (List.mem_cons_self ..)
      · simp only [pGuard, if_neg hap]
        exact andMono (idNeg _ _ (List.mem_cons_self ..))
                      (ih.A [N] rest (.circ G) (rst seen))
  | .imp (.down (.imp Q' N')) N =>
      exact aParkRow ih done (.down (.imp Q' N')) N rest (.circ G) seen
  | .imp (.down (.circ Q')) N =>
      exact aParkRow ih done (.down (.circ Q')) N rest (.circ G) seen
  | .imp (.or Qa Qb) N => exact aParkRow ih done (.or Qa Qb) N rest (.circ G) seen
  | .imp (.down (.up Pa)) N =>
      exact aParkRow ih done (.down (.up Pa)) N rest (.circ G) seen
  | .imp (.down (.and Ma Mb)) N =>
      exact aParkRow ih done (.down (.and Ma Mb)) N rest (.circ G) seen
  | .circ R =>
      exact impMono (ih.E [.up R] rest (rst seen))
                    (ih.A [.up R] rest (.circ G) (rst seen))
  | .up (.atom _) => exact nBotElim _ (List.mem_cons_self ..)
  | .up .fls => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.or _ _) => exact nBotElim _ (List.mem_cons_self ..)
  | .up (.down _) => exact nBotElim _ (List.mem_cons_self ..)
  | .imp .fls _ => exact nBotElim _ (List.mem_cons_self ..)
  | .and _ _ => exact nBotElim _ (List.mem_cons_self ..)

/-- The lax goal-inversion prefix transfers. -/
noncomputable def laxPrefixPW (ih : EasyLvl rst p f) (done : List Neg) (Q : Pos)
    (seen : List Pos) :
    PW (laxPrefixQ (interpG rst p f) done seen Q) (laxPrefixP p f done Q) := by
  match Q with
  | .atom q => exact .cons (ih.A [] done (.up (.atom q)) seen) .nil
  | .fls => exact .cons (ih.A [] done (.up .fls) seen) .nil
  | .or P₁ P₂ =>
      exact .cons (ih.A [] done (.circ P₁) seen)
        (.cons (ih.A [] done (.circ P₂) seen)
          (.cons (ih.A [] done (.up (.or P₁ P₂)) seen) .nil))
  | .down (.up P') => exact .cons (ih.A [] done (.circ P') seen) .nil
  | .down (.circ P') => exact .cons (ih.A [] done (.circ P') seen) .nil
  | .down (.and M₁ M₂) =>
      exact .cons (ih.A [] done (.up (.down (.and M₁ M₂))) seen) .nil
  | .down (.imp Q₀ N₀) =>
      exact .cons (ih.A [] done (.up (.down (.imp Q₀ N₀))) seen) .nil

/-- **The `∃p` half, one fuel up.** -/
noncomputable def easyE_succ (ih : EasyLvl rst p f) (todo done : List Neg)
    (seen : List Pos) :
    Inv [interpP p (f + 1) todo done none] [] .tru
        (interpG rst p (f + 1) todo done none seen) := by
  match todo with
  | .up (.atom a) :: todo =>
      rw [show interpP p (f + 1) (.up (.atom a) :: todo) done none
            = interpP p f todo (.up (.atom a) :: done) none from by rw [interpP],
          qAtom (rst := rst) a todo done none seen]
      exact ih.E _ _ _
  | .up .fls :: todo =>
      rw [show interpP p (f + 1) (.up .fls :: todo) done none = nBot from by rw [interpP],
          qFlsE (rst := rst) (p := p) (f := f) todo done seen]
      exact idNeg _ _ (List.mem_cons_self ..)
  | .up (.or P₁ P₂) :: todo =>
      rw [qOrE (rst := rst) (p := p) (f := f) P₁ P₂ todo done seen, interpP]
      exact nOrAllPW (PW.attachMap _ _ _ (fun x => ih.E (x.1 ++ todo) done (rst seen)))
  | .up (.down M) :: todo =>
      rw [show interpP p (f + 1) (.up (.down M) :: todo) done none
            = interpP p f (M :: todo) done none from by rw [interpP],
          qDown (rst := rst) M todo done none seen]
      exact ih.E _ _ _
  | .and M N :: todo =>
      rw [show interpP p (f + 1) (.and M N :: todo) done none
            = interpP p f (M :: N :: todo) done none from by rw [interpP],
          qAnd (rst := rst) M N todo done none seen]
      exact ih.E _ _ _
  | .imp .fls N :: todo =>
      rw [show interpP p (f + 1) (.imp .fls N :: todo) done none
            = interpP p f todo done none from by rw [interpP],
          qImpFls (rst := rst) N todo done none seen]
      exact ih.E _ _ _
  | .imp (.atom a) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.atom a) N :: todo) done none
            = interpP p f todo (.imp (.atom a) N :: done) none from by rw [interpP],
          qParkAtom (rst := rst) a N todo done none seen]
      exact ih.E _ _ _
  | .imp (.or Q₁ Q₂) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.or Q₁ Q₂) N :: todo) done none
            = interpP p f todo (.imp (.or Q₁ Q₂) N :: done) none from by rw [interpP],
          qParkOr (rst := rst) Q₁ Q₂ N todo done none seen]
      exact ih.E _ _ _
  | .imp (.down (.up P')) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.down (.up P')) N :: todo) done none
            = interpP p f todo (.imp (.down (.up P')) N :: done) none from by rw [interpP],
          qParkShift (rst := rst) P' N todo done none seen]
      exact ih.E _ _ _
  | .imp (.down (.and M₁ M₂)) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.down (.and M₁ M₂)) N :: todo) done none
            = interpP p f todo (.imp (.down (.and M₁ M₂)) N :: done) none from by
              rw [interpP],
          qParkAnd (rst := rst) M₁ M₂ N todo done none seen]
      exact ih.E _ _ _
  | .imp (.down (.imp Q' N')) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.down (.imp Q' N')) N :: todo) done none
            = interpP p f todo (.imp (.down (.imp Q' N')) N :: done) none from by
              rw [interpP],
          qParkDyk (rst := rst) Q' N' N todo done none seen]
      exact ih.E _ _ _
  | .circ Q :: todo =>
      rw [show interpP p (f + 1) (.circ Q :: todo) done none
            = interpP p f todo (.circ Q :: done) none from by rw [interpP],
          qParkBox (rst := rst) Q todo done none seen]
      exact ih.E _ _ _
  | .imp (.down (.circ Q')) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.down (.circ Q')) N :: todo) done none
            = interpP p f todo (.imp (.down (.circ Q')) N :: done) none from by
              rw [interpP],
          qParkCimp (rst := rst) Q' N todo done none seen]
      exact ih.E _ _ _
  | [] =>
      match hfr : findFire done (splits done) with
      | some (a, N, rest) =>
          rw [interpPFire_eq hfr none, qFire (rst := rst) hfr none seen]
          exact ih.E _ _ _
      | none =>
          rw [interpPE_eq hfr, qAgg (rst := rst) hfr none seen, aggQ_none]
          exact nAndAllPW (eRowsPW ih done seen)

/-- **The `∀p` half, one fuel up.** -/
noncomputable def easyA_succ (ih : EasyLvl rst p f) (todo done : List Neg) (G : Neg)
    (seen : List Pos) :
    Inv [interpG rst p (f + 1) todo done (some G) seen] [] .tru
        (interpP p (f + 1) todo done (some G)) := by
  match todo with
  | .up (.atom a) :: todo =>
      rw [show interpP p (f + 1) (.up (.atom a) :: todo) done (some G)
            = interpP p f todo (.up (.atom a) :: done) (some G) from by rw [interpP],
          qAtom (rst := rst) a todo done (some G) seen]
      exact ih.A _ _ _ _
  | .up .fls :: todo =>
      rw [show interpP p (f + 1) (.up .fls :: todo) done (some G) = nTop from by
            rw [interpP],
          qFlsA (rst := rst) (p := p) (f := f) todo done G seen]
      exact nTopIntro
  | .up (.or P₁ P₂) :: todo =>
      rw [qOrA (rst := rst) (p := p) (f := f) P₁ P₂ todo done G seen, interpP]
      exact nAndAllPW (PW.mapAttach _ _ _ (fun x =>
        impMono (ih.E (x.1 ++ todo) done (rst seen))
                (ih.A (x.1 ++ todo) done G (rst seen))))
  | .up (.down M) :: todo =>
      rw [show interpP p (f + 1) (.up (.down M) :: todo) done (some G)
            = interpP p f (M :: todo) done (some G) from by rw [interpP],
          qDown (rst := rst) M todo done (some G) seen]
      exact ih.A _ _ _ _
  | .and M N :: todo =>
      rw [show interpP p (f + 1) (.and M N :: todo) done (some G)
            = interpP p f (M :: N :: todo) done (some G) from by rw [interpP],
          qAnd (rst := rst) M N todo done (some G) seen]
      exact ih.A _ _ _ _
  | .imp .fls N :: todo =>
      rw [show interpP p (f + 1) (.imp .fls N :: todo) done (some G)
            = interpP p f todo done (some G) from by rw [interpP],
          qImpFls (rst := rst) N todo done (some G) seen]
      exact ih.A _ _ _ _
  | .imp (.atom a) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.atom a) N :: todo) done (some G)
            = interpP p f todo (.imp (.atom a) N :: done) (some G) from by rw [interpP],
          qParkAtom (rst := rst) a N todo done (some G) seen]
      exact ih.A _ _ _ _
  | .imp (.or Q₁ Q₂) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.or Q₁ Q₂) N :: todo) done (some G)
            = interpP p f todo (.imp (.or Q₁ Q₂) N :: done) (some G) from by rw [interpP],
          qParkOr (rst := rst) Q₁ Q₂ N todo done (some G) seen]
      exact ih.A _ _ _ _
  | .imp (.down (.up P')) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.down (.up P')) N :: todo) done (some G)
            = interpP p f todo (.imp (.down (.up P')) N :: done) (some G) from by
              rw [interpP],
          qParkShift (rst := rst) P' N todo done (some G) seen]
      exact ih.A _ _ _ _
  | .imp (.down (.and M₁ M₂)) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.down (.and M₁ M₂)) N :: todo) done (some G)
            = interpP p f todo (.imp (.down (.and M₁ M₂)) N :: done) (some G) from by
              rw [interpP],
          qParkAnd (rst := rst) M₁ M₂ N todo done (some G) seen]
      exact ih.A _ _ _ _
  | .imp (.down (.imp Q' N')) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.down (.imp Q' N')) N :: todo) done (some G)
            = interpP p f todo (.imp (.down (.imp Q' N')) N :: done) (some G) from by
              rw [interpP],
          qParkDyk (rst := rst) Q' N' N todo done (some G) seen]
      exact ih.A _ _ _ _
  | .circ Q :: todo =>
      rw [show interpP p (f + 1) (.circ Q :: todo) done (some G)
            = interpP p f todo (.circ Q :: done) (some G) from by rw [interpP],
          qParkBox (rst := rst) Q todo done (some G) seen]
      exact ih.A _ _ _ _
  | .imp (.down (.circ Q')) N :: todo =>
      rw [show interpP p (f + 1) (.imp (.down (.circ Q')) N :: todo) done (some G)
            = interpP p f todo (.imp (.down (.circ Q')) N :: done) (some G) from by
              rw [interpP],
          qParkCimp (rst := rst) Q' N todo done (some G) seen]
      exact ih.A _ _ _ _
  | [] =>
      match hfr : findFire done (splits done) with
      | some (a, N, rest) =>
          rw [interpPFire_eq hfr (some G), qFire (rst := rst) hfr (some G) seen]
          exact ih.A _ _ _ _
      | none =>
          rw [qAgg (rst := rst) hfr (some G) seen]
          match G with
          | .imp Q N =>
              rw [interpPA_imp_eq hfr Q N, aggQ_imp]
              exact nAndAllPW (PW.mapAttach _ _ _ (fun x =>
                impMono (ih.E x.1 done seen) (ih.A x.1 done N seen)))
          | .and M N =>
              rw [interpPA_and_eq hfr M N, aggQ_and]
              exact andMono (ih.A [] done M seen) (ih.A [] done N seen)
          | .up (.atom q) =>
              by_cases hq : atomMem q done = true
              · rw [interpPA_atomT_eq hfr hq, aggQ_atomT _ hq]
                exact nTopIntro
              · rw [interpPA_atom_eq hfr hq, aggQ_atomF _ hq]
                exact nOrAllPW ((PW.refl (atomHead p q)).append
                  (aRowsTruPW ih done (.atom q) seen))
          | .up .fls =>
              rw [interpPA_fls_eq hfr, aggQ_fls]
              exact nOrAllPW (aRowsTruPW ih done .fls seen)
          | .up (.or P₁ P₂) =>
              rw [interpPA_or_eq hfr P₁ P₂, aggQ_or]
              exact nOrAllPW ((PW.cons (ih.A [] done (.up P₁) seen)
                (PW.cons (ih.A [] done (.up P₂) seen) PW.nil)).append
                  (aRowsTruPW ih done (.or P₁ P₂) seen))
          | .up (.down M) =>
              rw [interpPA_down_eq hfr M, aggQ_down]
              exact nOrAllPW ((PW.cons (ih.A [] done M seen) PW.nil).append
                (aRowsTruPW ih done (.down M) seen))
          | .circ Q =>
              rw [interpP_circ_laxRows hfr Q, aggQ_circ]
              exact circMono (nOrAllPW ((laxPrefixPW ih done Q seen).append
                (aRowsCircPW ih done Q seen)))

end Step

/-- **The two easy halves, at every fuel.** -/
noncomputable def easyLvl (rst : List Pos → List Pos) (p : String) :
    ∀ f, EasyLvl rst p f
  | 0 => easyLvl_zero rst p
  | f + 1 =>
      { E := easyE_succ (easyLvl rst p f)
        A := easyA_succ (easyLvl rst p f) }

/-! # Part 5 · The easy halves at the cells `PQEquiv` names -/

/-- **`interpP ⊢ interpQ` on the `∃p` side**, at every fuel and every
station: the dropped conjunct is `⊤`. -/
noncomputable def pqEasyE (p : String) (f : Nat) (done : List Neg) :
    Inv [interpP p f [] done none] [] .tru (interpQ p f [] done none []) :=
  (easyLvl id p f).E [] done []

/-- **`interpQ ⊢ interpP` on the `∀p` side**, at every fuel, station and
goal: the dropped disjunct is `⊥`. -/
noncomputable def pqEasyA (p : String) (f : Nat) (done : List Neg) (G : Neg) :
    Inv [interpQ p f [] done (some G) []] [] .tru (interpP p f [] done (some G)) :=
  (easyLvl id p f).A [] done G []

/-! # Part 6 · What is left: the hard halves

The redundancy claim of `docs/n4-circfree-cases.md` §3.3, as data.  It is
the exact complement of Part 5: the `∃p` half in the direction that must
recover the dropped conjunct, and the `∀p` half in the direction that must
recover the dropped disjunct.  OPEN — no term of this type is built. -/

/-- **The hard halves of the redundancy obligation.**  OPEN. -/
def PQHard (p : String) : Type :=
  (∀ (f : Nat) (done : List Neg),
      Inv [interpQ p f [] done none []] [] .tru (interpP p f [] done none)) ×
  (∀ (f : Nat) (done : List Neg) (G : Neg),
      Inv [interpP p f [] done (some G)] [] .tru (interpQ p f [] done (some G) []))

/-- **`PQEquiv` from the hard halves alone**: the easy halves are supplied
by `easyLvl`, so the redundancy obligation reduces from four halves to
two. -/
noncomputable def pqEquiv_of_hard {p : String} (hd : PQHard p) : PQEquiv p := by
  intro f done g
  match g with
  | none => exact ⟨pqEasyE p f done, hd.1 f done⟩
  | some G => exact ⟨hd.2 f done G, pqEasyA p f done G⟩

end LJFO

/-! ## Pins -/

#axioms_within LJFO.PW.append []
#axioms_within LJFO.PW.refl [propext, Quot.sound]
#axioms_within LJFO.PW.mapBoth []
#axioms_within LJFO.nOrAllPW [propext, Quot.sound]
#axioms_within LJFO.nAndAllPW [propext, Quot.sound]
#axioms_within LJFO.attachMapEq [propext, Quot.sound]
#axioms_within LJFO.PW.attachMap [propext, Quot.sound]
#axioms_within LJFO.PW.mapAttach [propext, Quot.sound]
#axioms_within LJFO.andMono [propext, Quot.sound]
#axioms_within LJFO.circMono [propext, Quot.sound]
#axioms_within LJFO.impUse [propext, Quot.sound]
#axioms_within LJFO.impUseAtom [propext, Quot.sound]
#axioms_within LJFO.impMono [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.impMonoAtom [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.easyLvl_zero [propext, Quot.sound]
#axioms_within LJFO.easyE_succ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.easyA_succ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.easyLvl [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.pqEasyE [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.pqEasyA [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.pqEquiv_of_hard [propext, Classical.choice, Quot.sound]
