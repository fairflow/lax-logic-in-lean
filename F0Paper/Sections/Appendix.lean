import Verso
import VersoManual
import CLPPaper.Src
import CLPPaper.Cite
import F0Paper.Math
import F0Paper.Blocks

/-
Appendix A of the F0 paper (v0.7, 2026-10-29): the definitions that neither
the running text nor a displayed result of the sections mentions, and the
supporting lemmas whose statements use them (the classification is in
`F0Paper/STATUS.md`).  Detachable: `F0Paper/Paper.lean` includes it by one
line, and one sentence of the Introduction ("New in v0.7") names it; nothing
else in the sections refers to it.  `{letteredAppendix}` letters it in the PDF.
-/

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Cite PaperKit.Math PaperKit.Blocks
open PLLND PLLND.SemUI PLLND.F0 PLLND.RNEmbed PLLND.F0.FreeHAn PLLND.F0.Base3
open PLLND.LaxInfinite (atomFree)

#doc (Manual) "Supporting definitions and lemmas" =>
%%%
number := false
%%%

{letteredAppendix}

The definitions that the sections show in no statement and name nowhere in
their text, with the supporting lemmas whose statements use them, by the
section they support, in the order of the sections.  The rows are set as in
the tables at the ends of the sections: the name, the definition or statement
printed from the compiled declaration, and the source line.  The sections can
be read without this appendix.

# Section 4: Independence of the odd gaps

{lemmaTable IsEdge cmM_chainF}

Pins (`#axioms_within`) as for Section 4; the axioms, computed by
`collectAxioms` when the document is built: {axiomsOf}`IsEdge cmM_chainF`.

# Section 5: The rationals

{lemmaTable thr F_eval}

Pins (`#axioms_within`) with the dyadic construction of Section 5; the
axioms, computed when the document is built: {axiomsOf}`thr F_eval`.

# Section 10: Free Heyting algebras in F0

{lemmaTable FreeIPL.FreeIPL1InAboveT3 FreeIPL.freeIPL1 MeetCount.NoMeetCopyH2 MeetCount.noMeetCopyH2_bot MeetCount.noMeetCopyH2_t3 Free3 free3 freeFamily3_of_free3 Base3.FreeOmega3 Base3.freeOmega3 EmbedForms.PairwiseHimp EmbedForms.pairwiseHimp EmbedForms.Shift EmbedForms.shift EmbedForms.ShiftH2 EmbedForms.shiftH2 EmbedForms.ShiftOrderEmb EmbedForms.shift2_orderEmb EmbedForms.ShiftMeetFails EmbedForms.shiftMeetFails AnyFamily.AnyFamily3 AnyFamily.anyFamily3 AnyFamily.SigShiftω AnyFamily.sigShiftω FreePLL.FreePLLnAbove FreePLL.freePLLnAbove_base3}

Pins (`#axioms_within`): within `propext`, `Quot.sound`, except
`pairwiseHimp` and `shift` (`wip/f0EmbedForms.lean`), within no axioms.  The
axioms, computed when the document is built: {axiomsOf}`FreeIPL.freeIPL1 MeetCount.noMeetCopyH2_bot MeetCount.noMeetCopyH2_t3 free3 freeFamily3_of_free3 Base3.freeOmega3 EmbedForms.shiftH2 EmbedForms.shift2_orderEmb EmbedForms.shiftMeetFails AnyFamily.anyFamily3 AnyFamily.sigShiftω FreePLL.freePLLnAbove_base3`
for these lemmas, and {axiomsOf}`EmbedForms.pairwiseHimp EmbedForms.shift`
for `pairwiseHimp` and `shift`.

# Section 12: The Dedekind–MacNeille completion

{lemmaTable PLLND.F0.Points.CF PLLND.F0.Points.CF.onto}

Pins (`#axioms_within`) as for Section 12; the axioms, computed when the
document is built: {axiomsOf}`PLLND.F0.Points.CF.onto`.
