import Verso
import VersoManual
import CLPPaper.Src
import CLPPaper.Cite
import F0Paper.Math
import F0Paper.Blocks

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Cite PaperKit.Math PaperKit.Blocks
open PLLND PLLND.SemUI PLLND.F0 PLLND.RNEmbed
open F0Nuclear MacNeille MacNeille.JoinDenseHeytingEmbedding

#doc (Manual) "What is established" =>

Every headline result that is PROVED, or REFUTED by a kernel-checked
counterexample, with the pin of its declarations (the key of Section 1),
computed by `collectAxioms` when the document is built.  Where choice appears,
the last column names where it enters, from `#axiom_path` (`Meta/Audit.lean`);
_Mathlib's sets_ is `Set.instCompleteAtomicBooleanAlgebra`, through the order on
cuts, and _Mathlib's nuclei_ is `InfHomClass.toOrderHomClass`, through
`Nucleus.monotone` (Section 12).  A dash: no choice.

:::f0table (widths := "0.41 0.09 0.1 0.24 0.04")
* * Result
  * Status
  * Pin
  * Where choice enters
  * §
* * The order among the rungs is decided by `rungLe`
  * PROVED
  * {pinsOf}`rnSub_order`
  * excluded middle in the ladder's truth sets (`sat_rnP`)
  * 2
* * From $`g_2` on the gaps are pairwise incomparable
  * PROVED
  * {pinsOf}`gap_incomparable`
  * excluded middle in a frame law (`cmE`)
  * 2
* * Every variable-free formula lies above $`\bigcirc\bot` or below $`\lnot\bigcirc\bot`
  * PROVED
  * {pinsOf}`dichotomy`
  * –
  * 2
* * The downsets of $`t_1, \ldots, t_5` and the downset method
  * PROVED
  * {pinsOf}`DownTable.classify D5_table`
  * –
  * 3
* * Seven covers at the bottom; $`F_0` is not dense
  * PROVED
  * {pinsOf}`cover_0_1 cover_0_2 cover_1_3 cover_2_3 cover_1_4 cover_3_5 cover_4_5`
  * –
  * 3
* * $`F_0 = \{\bot, \lnot\bigcirc\bot\} \cup {\uparrow}\bigcirc\bot`
  * PROVED
  * {pinsOf}`low_trichotomy`
  * –
  * 3
* * The odd gaps are independent
  * PROVED
  * {pinsOf}`indep multi_edge_forcing`
  * –
  * 4
* * The dyadic rationals order-embed in $`F_0`
  * PROVED
  * {pinsOf}`dyadic_embedding`
  * –
  * 5
* * $`\mathbb{Q}` order-embeds in $`F_0`, explicitly (Minkowski's $`\mathord{?}`)
  * PROVED
  * {pinsOf}`Mink.qm_lt Mink.qm_onto rat_embedding_cf`
  * –
  * 5
* * $`\mathbb{Q}` order-embeds in $`F_0`, by Cantor's theorem
  * PROVED
  * {pinsOf}`rat_embedding`
  * the isomorphism taken out of `Nonempty` (`ratIso`)
  * 5
* * The gaps have no greatest lower bound
  * PROVED
  * {pinsOf}`gap_no_glb L_no_greatest`
  * excluded middle (`plain_trace_dichotomy`)
  * 6
* * The rungs up to $`t_{15}` lie under the dyadic thread
  * PROVED
  * {pinsOf}`ladder_le_formula`
  * –
  * 7
* * The odd gaps generate a free distributive lattice
  * PROVED
  * {pinsOf}`lpoly_deriv_iff`
  * –
  * 7
* * Pairs of the odd-gap lattice have $`\aleph_0` pairwise $`\parallel` threads
  * PROVED
  * {pinsOf}`incomparable_copies`
  * –
  * 7
* * Outside a finite downset table there is an upper cover
  * PROVED
  * {pinsOf}`cover_above`
  * –
  * 7
* * The halves $`f(1/2^{n})` have no greatest lower bound
  * PROVED
  * {pinsOf}`halves_no_glb halves_no_glb_vf`
  * excluded middle (`plain_trace_dichotomy`)
  * 7
* * $`t_6` is double-negation elimination for $`\bigcirc\bot`
  * PROVED
  * {pinsOf}`T6.t6_regular`
  * –
  * 8
* * Every $`{\downarrow}t_n` is finite
  * REFUTED
  * {pinsOf}`T6.t6_downset_infinite T6.rung_downset_infinite`
  * –
  * 8
* * Friedman's A-translation for PLL; $`\sigma^{n}` is faithful
  * PROVED
  * {pinsOf}`Sig.aTr_deriv Sig.sigN_faithful`
  * –
  * 9
* * The copies $`\sigma^{n}(F_0)` are strictly nested; $`\sigma(t_n) = \mathrm{rel}(r_n)`
  * PROVED
  * {pinsOf}`Sig.copies_strict Sig.sig_ladder`
  * –
  * 9
* * $`\sigma` is onto $`[t_3, \top]`; $`\sigma` preserves covers
  * REFUTED
  * {pinsOf}`SigOnto.sig_not_onto SigOnto.sig_not_cover`
  * –
  * 9
* * $`[t_3, \top]` is order-isomorphic to $`F_0`
  * REFUTED
  * {pinsOf}`NotIso.t3_filter_not_iso`
  * –
  * 9
* * On variable-free formulas the interval translation is $`\tau_{a,b}(A) \dashv\vdash A[\bot := a] \land b`; $`F_0` embeds in $`[a, b]` iff $`b` proves $`C[\bot := a]` only for theorems $`C`
  * PROVED
  * {pinsOf}`MovingTop.relClosed MovingTop.copyIffTopAvoid`
  * –
  * 9
* * $`F_0` embeds in $`[t_3, t_6]`, $`t_6 < \top`; the iterates of $`\tau` are interval translations, strictly nested
  * PROVED
  * {pinsOf}`MovingTop.copyT3T6 MovingTop.t3_t6 MovingTop.nd_t6 MovingTop.w2 MovingTop.w3`
  * –
  * 9
* * $`F_0` embeds in $`[t_3, t_5]` by $`\tau_{t_3,t_5}`
  * REFUTED
  * {pinsOf}`MovingTop.not_copyT3T5 MovingTop.t5_sig2_imp`
  * –
  * 9
* * The base criterion; the necessary conditions for every top
  * PROVED
  * {pinsOf}`Endpoints.baseCriterion Endpoints.necBox Endpoints.necPow Endpoints.necCells`
  * –
  * 9
* * $`t_6` is the least top of the extension by two top worlds; PLL embeds in $`[t_3, b']`, $`b'` incomparable with $`t_6`; PLL in $`[t_5, t_5 \lor t_6]`, with a strictly nested tower
  * PROVED
  * {pinsOf}`Endpoints.extTops Endpoints.topT3Alt Endpoints.selfStep_t5_t56 Endpoints.tower_t5`
  * –
  * 9
* * The tops over $`t_3` are closed under $`\land`; they have a least element
  * REFUTED
  * {pinsOf}`Endpoints.meetNotTop Endpoints.topsT3NotMeet Endpoints.noLeastTopT3`
  * –
  * 9
* * $`\sigma` maps each shell $`L_n` one-to-one onto $`L_{n+1}`; $`\sigma^{\omega}(F_0) = \{\top\}`; every orbit leaves every $`{\downarrow}x`, $`x \ne \top`
  * PROVED
  * {pinsOf}`InsideOut.shell_shift InsideOut.lim_eq_top InsideOut.orbit_order_limit`
  * –
  * 9
* * $`H_\omega` and every $`H_n` lie in $`[\sigma^{3}\bot, \top]` as Heyting subalgebras, from one family of variable-free generators: derivability between $`\bigcirc`-free formulas preserved and reflected
  * PROVED
  * {pinsOf}`Base3.freeHAnAbove_base3 Base3.freeHAωAbove_base3 Base3.freeFamily3`
  * –
  * 10
* * $`\forall n\, \exists m.\ H_n \hookrightarrow [\sigma^{m}\bot, \top]`, with $`m = 3`
  * PROVED
  * {pinsOf}`Base3.conjecture`
  * –
  * 10
* * Any $`n + 1` $`\sigma^{2}\bot`-maximal worlds of pairwise different types give $`H_n \hookrightarrow [\sigma^{3}\bot, \top]`; the $`\sigma`-shift of a free copy; $`H_n` and $`H_\omega` in every $`[\sigma^{m}\bot, \top]`, $`m \ge 3`
  * PROVED
  * {pinsOf}`AnyFamily.anyFamily3 AnyFamily.freeHAnAbove_base3_of_distinct AnyFamily.sigShift AnyFamily.sigShiftω AnyFamily.allAbove3 AnyFamily.allAbove3ω`
  * –
  * 10
* * PLL embeds faithfully in $`[\sigma^{3}\bot, \top]`, all formulas, with the readers as generators and $`\bigcirc \mapsto \bigcirc` (`freeReaders`, `freePLLAbove_base3`); $`\bigcirc x_1` is not in the range of the copy of IPC (`not_image_circ_x1`, `sep_circ_x1`)
  * PROVED
  * {pinsOf}`FreePLL.freeReaders FreePLL.freePLLAbove_base3 FreePLL.not_image_circ_x1 FreePLL.sep_circ_x1`
  * –
  * 10
* * $`H_1 \hookrightarrow [t_3, \top]`; $`H_2 \hookrightarrow [\sigma^{2}\bot, \top]`
  * PROVED
  * {pinsOf}`FreeIPL.freeIPL1 Pair.freePair Pair.freeHAnAbove_base2_two`
  * –
  * 10
* * Some pair of variable-free formulas generates $`H_2` over $`t_3`; $`H_\omega \hookrightarrow [t_3, \top]`
  * REFUTED
  * {pinsOf}`FreeIPL.noFreeHA2 FreeIPL.not_FreeIPLInAboveT3`
  * –
  * 10
* * A one-to-one $`\land`-preserving copy of $`H_n` with bottom $`a` needs $`k(a) \ge 2^{n}`; $`k(\bot) \le 2`, $`k(t_3) \le 3`, $`k(\sigma^{2}\bot) = \infty`
  * PROVED
  * {pinsOf}`MeetCount.meet_counting MeetCount.typeBound_bot MeetCount.typeBound_t3 FreeHAn.not_typeBound_base2 FreeHAn.base2_unbounded`
  * –
  * 10
* * The pairwise lemma; the shift; an order copy of $`H_2` with bottom $`\bot` that does not preserve $`\land`
  * PROVED
  * {pinsOf}`EmbedForms.pairwiseHimp EmbedForms.shift EmbedForms.shift2_orderEmb EmbedForms.shiftMeetFails`
  * –
  * 10
* * $`\bigcirc`-free derivability in PLL is derivability in IPC
  * PROVED
  * {pinsOf}`conservativity_IPL`
  * –
  * 10
* * The core lemma; a faithful interval copy carries it; $`H_\omega` in every non-degenerate interval of its copy above $`\sigma^{3}\bot`
  * PROVED
  * {pinsOf}`Interval.coreLemma Interval.nest Interval.mainTheorem Interval.bridge3`
  * –
  * 10
* * The tower of copies of $`H_\omega` to every depth, with the interval operations of $`F_0` hereditarily
  * PROVED
  * {pinsOf}`Interval.nestAll Interval.hereditary_ops`
  * –
  * 10
* * The core lemma without $`\zeta \nvdash \xi`
  * REFUTED
  * {pinsOf}`Interval.not_coreNoStrict`
  * –
  * 10
* * PLL embeds in its own interval $`[t_3, t_6]`; the tower of copies; the tower carried into $`F_0`, first step $`[\sigma^{4}\bot, \sigma^{3}(t_6)]`; towers over every $`[a, b]` with $`\mathit{SelfStep}(a, b)`
  * PROVED
  * {pinsOf}`MovingTop.pllSelf MovingTop.pllSelfTower MovingTop.pllTowerInF0 MovingTop.towerFirstStep Endpoints.selfTower Endpoints.selfToClosed`
  * –
  * 10
* * The readers give PLL in $`[\sigma^{3}\bot, t_6 \lor \sigma^{3}\bot]`; variable-free generators give PLL in some $`[t_3, b]`
  * REFUTED
  * {pinsOf}`MovingTop.not_pllBelowTop Endpoints.noClosedStepT3`
  * –
  * 10
* * $`F_0 = \{\bot, t_1, t_2, t_4\} \cup {\uparrow}t_3`, and $`t_3 \le p \iff \lnot\lnot p = \top`
  * PROVED
  * {pinsOf}`FilterIso.classify_low FilterIso.above_t3_iff_compl_compl_eq_top`
  * –
  * 11
* * The filter question is the residue above $`t_3`
  * PROVED
  * {pinsOf}`FilterIso.filterIsoQ_iff_aboveResidue_t3`
  * –
  * 11
* * $`[p, \top]` is order-isomorphic to $`F_0`, for $`p = t_1, t_2, t_4, t_5, c_1` and every $`\sigma^{n}(t_3)`, $`\sigma^{n}(c_1)`
  * REFUTED
  * {pinsOf}`FilterIso.e_filter_not_iso FilterIso.ne_filter_not_iso FilterIso.t4_filter_not_iso FilterIso.t5_filter_not_iso FilterIso.c1_filter_not_iso FilterIso.sigN_filter_not_iso FilterIso.C1n_filter_not_iso`
  * –
  * 11
* * Obstruction A, and the four cases at an isomorphism
  * PROVED
  * {pinsOf}`FilterIso.obstructionA FilterIso.iso_cases`
  * –
  * 11
* * $`F_0` is a Heyting algebra with the nucleus $`\bigcirc`
  * PROVED
  * {pinsOf}`instHeyting circNucleus`
  * –
  * 12
* * $`\mathrm{DM}(H)` is a frame, and $`H` a join- and meet-dense Heyting subalgebra
  * PROVED
  * {pinsOf}`le_cutHimp_iff principal_himp sSup_principal_left sInf_principal_right`
  * Mathlib's sets
  * 12
* * The upper extension of a nucleus is a nucleus, the greatest; the extensions form an interval
  * PROVED
  * {pinsOf}`exists_nucleus_extension extends_iff_mem_Icc`
  * Mathlib's nuclei
  * 12
* * $`\bigcirc` extends to $`F^{*}`, greatest among monotone extensions
  * PROVED
  * {pinsOf}`circ_extends_to_DM`
  * Mathlib's sets and nuclei
  * 12
* * Nuclear extensions to the completion are unique
  * REFUTED
  * {pinsOf}`MacNeilleNonUnique.nucleus_extension_not_unique`
  * the counterexample's nuclei, defined by cases (`threshold`)
  * 12
* * $`F^{*}` has a point that is not principal
  * PROVED
  * {pinsOf}`Points.gapCut_ne_principal Points.exists_nonprincipal`
  * Mathlib's sets; excluded middle (`L_no_greatest`); the completeness theorem
  * 12
* * $`|F^{*}| = 2^{\aleph_0}`; $`\mathbb{R}` maps one-to-one into $`F^{*}`
  * PROVED
  * {pinsOf}`Points.card_eq_continuum Points.X_injective`
  * Mathlib's sets; $`\mathbb{R}` (`Real.linearOrder`), cardinals, `Countable`
  * 12
* * $`F_0` has a filter that is not normal: $`F_7`, non-principal, with meet $`t_7`
  * PROVED
  * {pinsOf}`Normal.notAllNormal Normal.F7_meet Normal.F7_nonPrincipal Normal.F7_not_normal Normal.descending Normal.strictlyDescending Normal.lowerBound Normal.greatestLowerBound`
  * –
  * 12
* * In every finite subframe model with decidable $`S` every world forces some $`\rho_k`, and some odd rung
  * PROVED
  * {pinsOf}`Normal.star Normal.starOdd`
  * –
  * 12
* * $`\bigvee_k \rho_k = \top` and $`\bigvee_k t_{2k+1} = \top` in $`F_0`
  * PROVED
  * {pinsOf}`Normal.supRho Normal.supOddRungs`
  * –
  * 12
* * The only upper bound of the bases $`\sigma^{n}\bot` in $`F_0` is $`\top`; none lies above $`t_6`
  * PROVED
  * {pinsOf}`MovingTop.basesOnlyTop MovingTop.notCofinal`
  * –
  * 12
* * The $`t_6` tower: its ends, closing, at most one element in every interval, and one iff $`\tau` has a fixed point
  * PROVED
  * {pinsOf}`Endpoints.towerEnds Endpoints.closing Endpoints.inAllUnique Endpoints.fixedIffInAll`
  * –
  * 12
:::

Every other declaration in the paper is in a table of supporting
declarations, with its pin.
