/-
# The hloc-lift, brick 1: the regular `◯Z`-case closes hloc-free

The promise-join port's design pass (2026-08-28, HANDOFF §2026-08-28c)
splits the `hloc` hypothesis of `completenessV` into three consumption
points.  This file closes the first — and largest — of them:

    the regular `(n+1, ◯Z)`-case of `minModF` needs NO `hloc` at all.

The construction: `a ⊮ ◯Z` gives a cone-refutation witness (`minZeta`:
some `e ≥ a` whose whole `Rm`-cone refutes `Z`); walking `Rm`-up inside
that cone (`maxRmAbove`) reaches a CONE-TRIVIAL world `m` — still
refuting `Z`, since cone-refutation transports along `Rm` — and there
ONE barren `⋈^◯` with the corner machinery's `(R)`-coverage concludes
`◯Z` directly.  No `Z`-row, no descent into `Z`, no tagged recursion:
the row is `barren` for free and floats down to `a` as a `RegWitV`.

Two facts make it work at ANY world of ANY infallible model:

  * cone-trivial worlds are `Λ*`-circ-free (`forceStar` for `◯Y` needs
    `⊮ Y`, but cone-triviality forces `◯Y ⊩ → Y ⊩`), so the barren
    context's missing `◯`-zone loses nothing — `corner_lamStar_mem`
    below upgrades the corner coverage from `Clo`-coverage to LITERAL
    membership: every `Λ*`-atom sits in the joint atom zone and every
    `Λ*`-implication is KEPT (its antecedent is refuted by `forceStar`,
    so `keptOf_saturated` adopts it);

  * pledge-existence is a non-issue here because nothing is pledged:
    the peer's refutation `not_pledgeFam_of_circ_mem` blocks pledging
    `F` where `◯F ∈ Λ*` — but a cone-refuted `Z` never has `◯Z ∈ Λ*_m`
    (`m ⊩ ◯Z` would put a `Z`-forcing successor inside the refuting
    cone), and the barren route needs no pledge family at all.

The float-cell interface `ifl` carries `K.le a b` so that a future
caller (the lifted `minModF`) can discharge its recursive obligations:
an `IFloat` cell at `b ≥ a` recurses at a `minEta`-witness `e` with
`b ≤ e`, `e ≠ b` (the world forces the antecedent the anchor refutes),
so `ht e < ht b ≤ ht a` and the measure drops.

What this does NOT close (the design map, docs/next-session.md): the
free-grade prime/or cases at circ-carrying worlds (fallible joins; the
float-premises' `Θ^◯`-zone obligation is the pledge-existence question
instance-wise) and the irregular `(0, ◯Z)`-cells (a genuine `Z`-row is
required by `◯∉`, and its `⊃`-descent floats can land at circ-carrying
worlds where only blocked tags are available — the §8 corner's V-form).
-/
import wip.minmodv_assembly

namespace FRJ

open Form

section Lift

variable {K : Kripke} {G : Form}

/-- **`Λ*`-membership at a cone-trivial world.**  Literal membership in
the barren Or-base plus kept chain — strictly more than the corner
coverage's `Clo`-derivability, and exactly what `RegWitV.cov` demands.
Atoms: the joint atom zone.  Implications: `forceStar` refutes their
antecedents, so `(R)`-coverage plus `keptOf_saturated` keeps them.
`◯`-formulas: impossible (`forceStar` needs the body refuted, but the
trivial cone forces it). -/
theorem corner_lamStar_mem {a : K.W}
    (hcone : K.ConeTrivial a) (hinfa : ¬ K.Fal a)
    (cc : CornerCtx K G a) :
    lamStar K a G ⊆
      joinCtxOrVBase (istF cc.jr cc.jrs) (ithF cc.jr cc.jrs) ++
        keptOf (upsilon (irhsF cc.jr cc.jrs))
          (joinCtxOrVBase (istF cc.jr cc.jrs) (ithF cc.jr cc.jrs))
          (thPool (fun j => ithF cc.jr cc.jrs j)) := by
  have hbase : ∀ p : String, Form.atom p ∈ sfL G → K.force a (.atom p) →
      Form.atom p ∈ joinCtxOrVBase (istF cc.jr cc.jrs) (ithF cc.jr cc.jrs) := by
    intro p hp hfp
    exact List.mem_append_left _ (List.mem_append_right _
      (cc_interAt cc (List.mem_filter.mpr ⟨hp, rfl⟩) hfp))
  intro X hX
  obtain ⟨hsf, hstar⟩ := mem_lamStar.mp hX
  cases X with
  | atom p =>
      exact List.mem_append_left _ (hbase p hsf (K.forceStar_force hstar))
  | bot => exact hstar.elim
  | and X₁ X₂ => exact hstar.elim
  | or X₁ X₂ => exact hstar.elim
  | imp A B =>
      obtain ⟨hf, hnA⟩ := hstar
      exact List.mem_append_right _
        (keptOf_saturated (cc_pool cc hsf hf)
          (corner_coverage_refuted hcone hinfa (cc_supply cc hcone _ hbase)
            A (sfL_imp hsf).1 hnA))
  | circ Y =>
      obtain ⟨hf, hnY⟩ := hstar
      obtain ⟨c, hrc, hc⟩ := hf a (K.le_refl a)
      exact absurd ((hcone c hrc) ▸ hc) hnY

/-- **The hloc-free regular `◯Z`-witness.**  Re-anchor through
`minZeta` and `maxRmAbove`, conclude by one barren `⋈^◯` at the
cone-trivial world, float back down.  Works at any world of any
infallible model — no `hloc`, no supply, no guard. -/
def circRegWit (K : Kripke) (G : Form) (hinf : K.Infallible)
    {a : K.W} {Z : Form}
    (hOZ : Form.circ Z ∈ sfR G) (hnf : ¬ K.force a (.circ Z))
    (ifl : ∀ b : K.W, K.le a b → IFloat K G b) :
    RegWitV K G a (.circ Z) :=
  let mz := minZeta hnf
  let mr := maxRmAbove K mz.e
  have hwle : K.le a mr.m := K.le_trans mz.le (K.sub_mi mr.rm)
  have hnfZ : ¬ K.force mr.m Z := mz.cone mr.m mr.rm
  have hnfOZ : ¬ K.force mr.m (.circ Z) := fun hf => by
    obtain ⟨c, hrc, hc⟩ := hf mr.m (K.le_refl _)
    exact mz.cone c (K.rm_trans mr.rm hrc) hc
  let cc := mkCornerCtx (ifl mr.m hwle) (sfR_circ hOZ) hnfZ
  let crow := circLeaf cc mr.cone (hinf mr.m) Z hOZ hnfOZ
  { ctx := crow.ctx
    t := crow.t
    der := crow.der
    tOK := crow.tOK
    wld := mr.m
    wle := hwle
    cov := corner_lamStar_mem mr.cone (hinf mr.m) cc }

end Lift

/-- info: 'FRJ.corner_lamStar_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms corner_lamStar_mem

/-- info: 'FRJ.circRegWit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms circRegWit

end FRJ
