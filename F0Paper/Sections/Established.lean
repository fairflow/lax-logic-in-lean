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
counterexample, with the axioms its declarations depend on, computed by
`collectAxioms` when the document is built.  Where `Classical.choice` appears,
the last column names where it enters, from `#axiom_path` (`Meta/Audit.lean`);
"Mathlib's sets" is `Set.instCompleteAtomicBooleanAlgebra`, through the order on
cuts, and "Mathlib's nuclei" is `InfHomClass.toOrderHomClass`, through
`Nucleus.monotone` (Section 11).  A dash: no choice.

:::f0table (widths := "0.34 0.09 0.2 0.28 0.05")
* * Result
  * Status
  * Axioms
  * Where choice enters
  * §
* * The order among the rungs is decided by `rungLe`
  * PROVED
  * {axiomsOf}`rnSub_order`
  * excluded middle in the ladder's truth sets (`sat_rnP`)
  * 2
* * From $`g_2` on the gaps are pairwise incomparable
  * PROVED
  * {axiomsOf}`gap_incomparable`
  * excluded middle in a frame law (`cmE`)
  * 2
* * Every variable-free formula lies above $`\bigcirc\bot` or below $`\lnot\bigcirc\bot`
  * PROVED
  * {axiomsOf}`dichotomy`
  * –
  * 2
* * The downsets of $`t_1, \ldots, t_5` and the downset method
  * PROVED
  * {axiomsOf}`DownTable.classify D5_table`
  * –
  * 3
* * Seven covers at the bottom; $`F_0` is not dense
  * PROVED
  * {axiomsOf}`cover_0_1 cover_0_2 cover_1_3 cover_2_3 cover_1_4 cover_3_5 cover_4_5`
  * –
  * 3
* * $`F_0 = \{\bot, \lnot\bigcirc\bot\} \cup {\uparrow}\bigcirc\bot`
  * PROVED
  * {axiomsOf}`low_trichotomy`
  * –
  * 3
* * The odd gaps are independent
  * PROVED
  * {axiomsOf}`indep multi_edge_forcing`
  * –
  * 4
* * The dyadic rationals order-embed in $`F_0`
  * PROVED
  * {axiomsOf}`dyadic_embedding`
  * –
  * 5
* * $`\mathbb{Q}` order-embeds in $`F_0`, explicitly (Minkowski's $`\mathord{?}`)
  * PROVED
  * {axiomsOf}`Mink.qm_lt Mink.qm_onto rat_embedding_cf`
  * –
  * 5
* * $`\mathbb{Q}` order-embeds in $`F_0`, by Cantor's theorem
  * PROVED
  * {axiomsOf}`rat_embedding`
  * the isomorphism taken out of `Nonempty` (`ratIso`)
  * 5
* * The gaps have no greatest lower bound
  * PROVED
  * {axiomsOf}`gap_no_glb L_no_greatest`
  * excluded middle (`plain_trace_dichotomy`)
  * 6
* * The rungs up to $`t_{15}` lie under the dyadic thread
  * PROVED
  * {axiomsOf}`ladder_le_formula`
  * –
  * 7
* * The odd gaps generate a free distributive lattice
  * PROVED
  * {axiomsOf}`lpoly_deriv_iff`
  * –
  * 7
* * Pairs of the odd-gap lattice have $`\aleph_0` pairwise $`\parallel` threads
  * PROVED
  * {axiomsOf}`incomparable_copies`
  * –
  * 7
* * Outside a finite downset table there is an upper cover
  * PROVED
  * {axiomsOf}`cover_above`
  * –
  * 7
* * The halves $`f(1/2^{n})` have no greatest lower bound
  * PROVED
  * {axiomsOf}`halves_no_glb halves_no_glb_vf`
  * excluded middle (`plain_trace_dichotomy`)
  * 7
* * $`t_6` is double-negation elimination for $`\bigcirc\bot`
  * PROVED
  * {axiomsOf}`T6.t6_regular`
  * –
  * 8
* * Every $`{\downarrow}t_n` is finite
  * REFUTED
  * {axiomsOf}`T6.t6_downset_infinite T6.rung_downset_infinite`
  * –
  * 8
* * Friedman's A-translation for PLL; $`\sigma^{n}` is faithful
  * PROVED
  * {axiomsOf}`Sig.aTr_deriv Sig.sigN_faithful`
  * –
  * 9
* * The copies $`\sigma^{n}(F_0)` are strictly nested; $`\sigma(t_n) = \mathrm{rel}(r_n)`
  * PROVED
  * {axiomsOf}`Sig.copies_strict Sig.sig_ladder`
  * –
  * 9
* * $`\sigma` is onto $`[t_3, \top]`; $`\sigma` preserves covers
  * REFUTED
  * {axiomsOf}`SigOnto.sig_not_onto SigOnto.sig_not_cover`
  * –
  * 9
* * $`[t_3, \top]` is order-isomorphic to $`F_0`
  * REFUTED
  * {axiomsOf}`NotIso.t3_filter_not_iso`
  * –
  * 9
* * $`F_0 = \{\bot, t_1, t_2, t_4\} \cup {\uparrow}t_3`, and $`t_3 \le p \iff \lnot\lnot p = \top`
  * PROVED
  * {axiomsOf}`FilterIso.classify_low FilterIso.above_t3_iff_compl_compl_eq_top`
  * –
  * 10
* * The filter question is the residue above $`t_3`
  * PROVED
  * {axiomsOf}`FilterIso.filterIsoQ_iff_aboveResidue_t3`
  * –
  * 10
* * $`[p, \top]` is order-isomorphic to $`F_0`, for $`p = t_1, t_2, t_4, t_5, c_1` and every $`\sigma^{n}(t_3)`, $`\sigma^{n}(c_1)`
  * REFUTED
  * {axiomsOf}`FilterIso.e_filter_not_iso FilterIso.ne_filter_not_iso FilterIso.t4_filter_not_iso FilterIso.t5_filter_not_iso FilterIso.c1_filter_not_iso FilterIso.sigN_filter_not_iso FilterIso.C1n_filter_not_iso`
  * –
  * 10
* * Obstruction A, and the four cases at an isomorphism
  * PROVED
  * {axiomsOf}`FilterIso.obstructionA FilterIso.iso_cases`
  * –
  * 10
* * $`F_0` is a Heyting algebra with the nucleus $`\bigcirc`
  * PROVED
  * {axiomsOf}`instHeyting circNucleus`
  * –
  * 11
* * $`\mathrm{DM}(H)` is a frame, and $`H` a join- and meet-dense Heyting subalgebra
  * PROVED
  * {axiomsOf}`le_cutHimp_iff principal_himp sSup_principal_left sInf_principal_right`
  * Mathlib's sets
  * 11
* * The upper extension of a nucleus is a nucleus, the greatest; the extensions form an interval
  * PROVED
  * {axiomsOf}`exists_nucleus_extension extends_iff_mem_Icc`
  * Mathlib's nuclei
  * 11
* * $`\bigcirc` extends to $`F^{*}`, greatest among monotone extensions
  * PROVED
  * {axiomsOf}`circ_extends_to_DM`
  * Mathlib's sets and nuclei
  * 11
* * Nuclear extensions to the completion are unique
  * REFUTED
  * {axiomsOf}`MacNeilleNonUnique.nucleus_extension_not_unique`
  * the counterexample's nuclei, defined by cases (`threshold`)
  * 11
* * $`F^{*}` has a point that is not principal
  * PROVED
  * {axiomsOf}`Points.gapCut_ne_principal Points.exists_nonprincipal`
  * Mathlib's sets; excluded middle (`L_no_greatest`); the completeness theorem
  * 11
* * $`|F^{*}| = 2^{\aleph_0}`; $`\mathbb{R}` maps one-to-one into $`F^{*}`
  * PROVED
  * {axiomsOf}`Points.card_eq_continuum Points.X_injective`
  * Mathlib's sets; $`\mathbb{R}` (`Real.linearOrder`), cardinals, `Countable`
  * 11
:::

Every other declaration in the paper is in the supporting tables at the ends
of the sections, with its pin.
