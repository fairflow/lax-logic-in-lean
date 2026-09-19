/-
# Round D, superseded verbatim: `TLF` and `ULF`

Removed from `LaxLogic/Focusing/LJF.lean` on 2026-09-18 when the two were
replaced by the single mode-indexed family `XLF`.  Kept verbatim, per the rule
of `docs/ljf-simp-round1.md` ("everything deleted preserved in `Archive/`").
This file is NOT part of any build target; it is a record.

Why one family and not the emission record Round D proposed: an emission record
means passing a mutual sibling as a function argument, and the termination
checker must then bound the recursion at an arbitrary argument.  The certificate
is in `docs/ljf-round-d-2026-09-18.md`.
-/

/-
def TLF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {H : Neg} {P : Pos},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeN p H → PFreeP p P →
      LFoc Γ' H P → LFoc (interp p [] done none :: K) H P
  | _, _, _, _, hm, hm2, hK, hH, hp, .rel d =>
      .rel (TInv done hsat hP hm hm2 hK
        (PFreeΩ.cons hH PFreeΩ.nil) hp d)
  | _, _, _, _, hm, hm2, hK, hH, hp, .impL s lf =>
      .impL (TStab done hsat hP hm hm2 hK hH.1 s)
            (TLF done hsat hP hm hm2 hK hH.2 hp lf)
  | _, _, _, _, hm, hm2, hK, hH, hp, .and1 lf =>
      .and1 (TLF done hsat hP hm hm2 hK hH.1 hp lf)
  | _, _, _, _, hm, hm2, hK, hH, hp, .and2 lf =>
      .and2 (TLF done hsat hP hm hm2 hK hH.2 hp lf)
  termination_by Γ' K H P hm hm2 hK hH hp lf => (2 * sum3 [] + sum3 done, sizeOf lf)
  decreasing_by ljf_dec_e


def ULF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {P₀ : Pos} {L : List Neg} {H : Neg},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      interp p [] done (some (.up P₀)) = nOrAll L →
      (∀ {c : String} {Nc : Neg} {rest : List Neg},
        (Neg.imp (.atom c) Nc, rest) ∈ splits done →
        pGuard p c nBot (nAnd (.up (.atom c))
          (interp p [Nc] rest (some (.up P₀)))) ∈ L) →
      (∀ {Q' : Pos} {N' N : Neg} {rest : List Neg},
        (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (.up P₀))) ∈ L) →
      PFreeN p H →
      LFoc Γ' H P₀ → LFoc (interp p [] done none :: K) H (orChain L)
  | _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, hH, .rel d =>
      .rel (UInvG done hsat hP hm hm2 hK hV qmem dmem
        (PFreeΩ.cons hH PFreeΩ.nil) d)
  | _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, hH, .impL s lf =>
      .impL (TStab done hsat hP hm hm2 hK hH.1 s)
            (ULF done hsat hP hm hm2 hK hV qmem dmem hH.2 lf)
  | _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, hH, .and1 lf =>
      .and1 (ULF done hsat hP hm hm2 hK hV qmem dmem hH.1 lf)
  | _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, hH, .and2 lf =>
      .and2 (ULF done hsat hP hm hm2 hK hV qmem dmem hH.2 lf)
  termination_by Γ' K P₀ L H hm hm2 hK hV qmem dmem hH lf =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf lf)
  decreasing_by ljf_dec_a


-/
