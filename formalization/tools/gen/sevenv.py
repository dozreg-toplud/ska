#!/usr/bin/env python3
"""Generate lemmas/Ska/CompSevenV.lean: `[7 p q]` with `q` in `Frag` and a
`p` whose runs may make proxies (`OKNV`), from the text of `runOKP_n7g` and
`runOKN_n7` (CompFragM.lean) and of the case `seven` of `runX_clean`.
Run from formalization/:  python3 tools/gen/sevenv.py
Every extraction and replacement asserts its match count.
"""
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
SKA = ROOT / "lemmas" / "Ska"


def lines(name):
    return (SKA / name).read_text().split("\n")


def find(ls, text, start=0):
    hits = [i for i in range(start, len(ls)) if ls[i] == text]
    assert hits, (text, start)
    return hits[0]


def seg(ls, first, last_excl=None, last_incl=None, start=0):
    i = find(ls, first, start)
    if last_excl is not None:
        j = find(ls, last_excl, i + 1)
    else:
        j = find(ls, last_incl, i + 1) + 1
    return ls[i:j]


def rep(text, old, new, count=1):
    n = text.count(old)
    assert n == count, (old, n, count)
    return text.replace(old, new)


def dedent(ls, k):
    out = []
    for l in ls:
        if l.strip() == "":
            out.append("")
        else:
            assert l.startswith(" " * k), l
            out.append(l[k:])
    return out


fm = lines("CompFragM.lean")

# ---------------------------------------------------------------- %done, %pick
P = "\n".join(seg(fm, "theorem runOKP_n7g (lib : Lib) {p q : Nomm} {goal : CGoal S} (hg : NotNext goal) (hq : Frag q goal)",
                  last_excl="/-! ## The fragment -/"))
P = rep(P, "theorem runOKP_n7g (lib : Lib)", "theorem runOKV_n7g (lib : Lib)")
P = rep(P, "    (hp : NextOK (S := S) (Map := Map) lib p) (hargs : ∀ j, GoalJ goal j → j.args = []) {region : List Nat}",
        "    (hp : OKNV (S := S) (Map := Map) lib p) (hargs : ∀ j, GoalJ goal j → j.args = []) {region : List Nat}")
P = rep(P, "    (d0 : g0.drop = false) (hu : UpBelow g0) (h : runL (Nomm.n7 p q) (CGoal.toL goal) region g0 = some (nex, g2)) :\n"
           "    RunOKP (Map := Map) lib (Nomm.n7 p q) goal g0 g2 nex := by",
        "    (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0) (hcb0 : CondBelow g0)\n"
        "    (gin : GoalIn g0.re goal) (gab : GoalA (g0.re ≤ ·) goal)\n"
        "    (h : runL (Nomm.n7 p q) (CGoal.toL goal) region g0 = some (nex, g2)) :\n"
        "    RunOKV (Map := Map) lib (Nomm.n7 p q) goal g0 g2 nex := by")
P = rep(P, "  have GQ : GrowU g0 g' := Dq.grow.toU hu\n",
        "  have GQ : GrowU g0 g' := Dq.grow.toU hu\n"
        "  have cq : g'.cond = g0.cond := (kc_run q goal).keep g0 n g' hr\n"
        "  have cbq : CondBelow g' := (condFresh_of_eq Rq.ext.1 cq).below hcb0\n"
        "  have hkq : ∀ r, NMem n.laz.ned r → HoonMap.get g'.cond r = Option.none := fun r hr => by\n"
        "    rw [cq]\n"
        "    rcases Rq.regs r hr with h' | h'\n"
        "    · exact (notNext_gmem hg r h').elim\n"
        "    · exact condBelow_none hcb0 h'.1\n")
P = rep(P, "    ⟨Dq.lo, Dq.hi⟩ fa hok' hcl' hcount (Nat.le_trans b0 Dq.grow.bo) dg (GQ.up hu) h2",
        "    ⟨Dq.lo, Dq.hi⟩ fa hok' hcl' hcount (Nat.le_trans b0 Dq.grow.bo) dg (GQ.up hu) (hcl0.growU GQ) cbq hkq h2")
P = rep(P, "  refine ⟨Rq.ext.trans Rp.ext, GQ.trans Rp.grow, Rp.cnd.trans ((kc_run q goal).keep g0 n g' hr),\n"
           "    Rp.lo, Rp.hi, ?_, fun r hr => ?_, Rp.dist, fun e he => ?_, fun e he => ?_, Rp.nodup, ?_,\n"
           "    fun s hs => ?_, ?_⟩",
        "  refine ⟨Rq.ext.trans Rp.ext, GQ.trans Rp.grow, (condFresh_of_eq Rq.ext.1 cq).trans Rp.cfr,\n"
        "    Rp.lo, Rp.hi, ?_, fun r hr => ?_, Rp.dist, fun e he => ?_, fun e he => ?_, Rp.nodup, ?_,\n"
        "    fun s hs => ?_, Rp.ncond, Rp.econd, ?_⟩")
SEMHEAD_OLD = ("  · intro c ned σ O st t gul s0 s ag hned regs hh hn\n"
               "    have agP : AgreeP lib O c gul st t ned g' g2 nex.laz s0 s :=\n"
               "      ⟨fun o h0 h1 hnl => ag.1 o (Nat.le_trans Rq.ext.2.1 h0) h1 hnl, ag.2⟩\n"
               "    have Sp := Rp.sem c ned σ O st t gul s0 s agP hned regs hh hn\n"
               "    have agQ : Agree c g0 g' := fun o h0 h1 => by\n"
               "      rw [ag.1 o h0 (Nat.lt_of_lt_of_le h1 Rp.ext.2.1) (fun hm => ?_)]\n"
               "      · exact Rp.ext.2.2.2 o h1\n")
SEMHEAD_NEW = ("  · intro cf hcf c ned σ O st t gul s0 s ag hned regs hh hn\n"
               "    have agP : AgreeU lib O c gul st t cf ned g' g2 nex.laz s0 s :=\n"
               "      ⟨fun o h0 h1 hnl => ag.1 o (Nat.le_trans Rq.ext.2.1 h0) h1 hnl, ag.2⟩\n"
               "    have Sp := Rp.sem cf hcf c ned σ O st t gul s0 s agP hned regs hh hn\n"
               "    have u0 : ∀ x, x < g'.re → unproxy cf x = unproxy g'.cond x :=\n"
               "      unproxy_agree (fun k hk => (hcf k (by omega)).trans (Rp.cfr.get_lt hk))\n"
               "    have u1 : ∀ x, ABOVEP → unproxy g'.cond x = id x := fun x hx => unproxy_none (ABOVEPF)\n"
               "    have agQ : Agree c g0 g' := fun o h0 h1 => by\n"
               "      rw [ag.1 o h0 (Nat.lt_of_lt_of_le h1 Rp.ext.2.1) (fun hm => ?_)]\n"
               "      · rw [Rp.ext.2.2.2 o h1]\n"
               "        cases hgb : HoonMap.get g'.blocks o with\n"
               "        | none => rfl\n"
               "        | some b =>\n"
               "          simp only [Option.map_some]\n"
               "          rw [unproxyBlob, renBlob_congr u0 (Bq o b h0 h1 hgb), renBlob_congr u1 (Aq o b h0 h1 hgb),\n"
               "            renBlob_id]\n")
P = rep(P, SEMHEAD_OLD, SEMHEAD_NEW.replace(
    "(ABOVEPF)", "(by rw [cq]; exact condBelow_none hcb0 hx)").replace("ABOVEP", "g0.re ≤ x"))
P = rep(P, "  have l1 := Rq.ext.1\n",
        "  have Bq : BelowIn g0.bo g' := run_below d0 gin hr\n"
        "  have Aq : AboveIn (g0.re ≤ ·) g0.bo g' := run_above d0 gab (ple_le (Nat.le_refl _)) hr\n"
        "  have l1 := Rq.ext.1\n")
P_DOC = ("/-- **`[7 p q]` for `%done` or `%pick` with a `p` that may make proxies**\n"
         "(`runOKP_n7g` with `OKNV` of `p`): `q` makes no proxy and its blocks mention\n"
         "registers allocated in its run, which unproxying leaves alone. -/\n")

# ---------------------------------------------------------------- %next
iN = find(fm, "theorem runOKN_n7 (lib : Lib) {p q : Nomm} {sur : Sure S} {th : Jmp} (hq : Frag q (CGoal.next sur th))")
jN = next(j for j in range(iN + 1, len(fm)) if fm[j].startswith("/-") or fm[j].startswith("theorem "))
N = "\n".join(fm[iN:jN])
N = N.rstrip("\n") + "\n"
N = rep(N, "theorem runOKN_n7 (lib : Lib)", "theorem runOKNV_n7 (lib : Lib)")
N = rep(N, "    (hp : NextOK (S := S) (Map := Map) lib p) {region : List Nat} {g0 g2 : Gen Map} {nex : NextL S}",
        "    (hp : OKNV (S := S) (Map := Map) lib p) {region : List Nat} {g0 g2 : Gen Map} {nex : NextL S}")
N = rep(N, "    (hcl : Clean sur.ned) (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)\n"
           "    (h : runL (Nomm.n7 p q) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g2)) :\n"
           "    RunOKN (Map := Map) lib (Nomm.n7 p q) sur th g0 g2 nex := by",
        "    (hcl : Clean sur.ned) (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)\n"
        "    (hcl0 : Clear g0) (hcb0 : CondBelow g0) (hkg : ∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none)\n"
        "    (h : runL (Nomm.n7 p q) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g2)) :\n"
        "    RunOKNV (Map := Map) lib (Nomm.n7 p q) sur th g0 g2 nex := by")
N = rep(N, "  have GQ : GrowU g0 g' := Dq.grow.toU hu\n",
        "  have GQ : GrowU g0 g' := Dq.grow.toU hu\n"
        "  have cq : g'.cond = g0.cond := (kc_run q _).keep g0 n g' hr\n"
        "  have cbq : CondBelow g' := (condFresh_of_eq Rq.ext.1 cq).below hcb0\n"
        "  have hkq : ∀ r, NMem n.laz.ned r → HoonMap.get g'.cond r = Option.none := fun r hr => by\n"
        "    rw [cq]\n"
        "    rcases Rq.regs r hr with h' | h'\n"
        "    · exact hkg r h'\n"
        "    · exact condBelow_none hcb0 h'.1\n")
N = rep(N, "    ⟨Dq.lo, Dq.hi⟩ fa hok' hcl' hcount (Nat.le_trans b0 Dq.grow.bo) dg (GQ.up hu) h2",
        "    ⟨Dq.lo, Dq.hi⟩ fa hok' hcl' hcount (Nat.le_trans b0 Dq.grow.bo) dg (GQ.up hu) (hcl0.growU GQ) cbq hkq h2")
N = rep(N, "  refine ⟨Rq.ext.trans Rp.ext, GQ.trans Rp.grow, Rp.cnd.trans ((kc_run q _).keep g0 n g' hr),\n"
           "    Rp.lo, Rp.hi, ?_, fun r hr => ?_, Rp.dist, fun e he => ?_, fun e he => ?_, Rp.nodup, ?_,\n"
           "    fun s hs => ?_, ?_⟩",
        "  refine ⟨Rq.ext.trans Rp.ext, GQ.trans Rp.grow, (condFresh_of_eq Rq.ext.1 cq).trans Rp.cfr,\n"
        "    Rp.lo, Rp.hi, ?_, fun r hr => ?_, Rp.dist, fun e he => ?_, fun e he => ?_, Rp.nodup, ?_,\n"
        "    fun s hs => ?_, Rp.ncond, Rp.econd, ?_⟩")
N = rep(N, SEMHEAD_OLD, SEMHEAD_NEW.replace(
    "(ABOVEPF)", "(by rw [cq]; exact hx)").replace("ABOVEP", "HoonMap.get g0.cond x = Option.none"))
N = rep(N, "  have l1 := Rq.ext.1\n",
        "  have Bq : BelowIn g0.bo g' := run_below (goal := CGoal.next sur th) d0 ⟨fun r hr => hok.2 r hr, jmpIn_nil hth⟩ hr\n"
        "  have Aq : AboveIn (fun r => HoonMap.get g0.cond r = Option.none) g0.bo g' :=\n"
        "    run_above (goal := CGoal.next sur th) d0 ⟨hkg, jmpIn_nil hth⟩ (fun r hr => condBelow_none hcb0 hr) hr\n"
        "  have l1 := Rq.ext.1\n")
N_DOC = ("/-- **`[7 p q]` under a fork-free `%next` with a `p` that may make\n"
         "proxies** (`runOKN_n7` with `OKNV` of `p`): `q`'s blocks mention the goal's\n"
         "registers (no keys, `hkg`) and registers allocated in its run. -/\n")

# ---------------------------------------------------------------- tags
def tag_of(text, kind):
    head, _, _ = text.partition("  have Bq : BelowIn g0.bo g'")
    head = rep(head, "  have Rp := hp (sur := n.laz)", "  have Tp := tp (sur := n.laz)")
    return head + "  exact (CondTag.of_eq cq).trans Tp\n"

TP = tag_of(P, "P")
TP = rep(TP, "theorem runOKV_n7g (lib : Lib)", "theorem seven_tagV (lib : Lib)")
TP = rep(TP, "    RunOKV (Map := Map) lib (Nomm.n7 p q) goal g0 g2 nex := by",
         "    CondTag region g0.cond g2.cond := by")
TP = rep(TP, "    (hp : OKNV (S := S) (Map := Map) lib p) (hargs",
         "    (tp : TagNV (S := S) (Map := Map) p) (hargs")
TN = tag_of(N, "N")
TN = rep(TN, "theorem runOKNV_n7 (lib : Lib)", "theorem seven_tagNV (lib : Lib)")
TN = rep(TN, "    RunOKNV (Map := Map) lib (Nomm.n7 p q) sur th g0 g2 nex := by",
         "    CondTag region g0.cond g2.cond := by")
TN = rep(TN, "    (hp : OKNV (S := S) (Map := Map) lib p) {region",
         "    (tp : TagNV (S := S) (Map := Map) p) {region")

# ---------------------------------------------------------------- clean
fx = lines("CompFragX.lean")
i7 = find(fx, "  | seven hq _ ih =>")
cl = seg(fx, "    intro goal region g0 g1 nex hc h", last_incl="    exact ih (goal := CGoal.next n.laz n.th) (run_clean _ goal _ _ n hc hr) h2",
         start=i7)
cl = "\n".join(dedent(cl, 2))

HEAD = '''import lemmas.Ska.CompFragUJGen

/-!
# `[7 p q]` with a `p` whose runs make proxies

README Gaps 12.2 (tenth session).  Generated by `tools/gen/sevenv.py` from
`runOKP_n7g`, `runOKN_n7` (`CompFragM.lean`) and the case `seven` of
`runX_clean`; do not edit by hand.  `q` is in `Frag` (no `%6`), so it runs
through `run`, makes no proxy and returns a fork-free `next`, under which `p`
runs with `OKNV`.  `q`'s blocks mention its goal's registers and registers
allocated in its run, no key of any later `cond`, so unproxying leaves them
alone (`run_below`, `run_above`).

* `runOKV_n7g`: `RunOKV` of `[7 p q]` for `%done` and `%pick`.
* `runOKNV_n7`: `RunOKNV` of `[7 p q]` under a fork-free `%next`.
* `seven_tagV`, `seven_tagNV`: the tag clauses (`q` keeps `cond`, `p`'s
  `TagNV`).
* `cleanA_seven`: `CleanA` of `[7 p q]` from `CleanA` of `p`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

'''

CLEAN = '''/-- **`CleanA` of `[7 p q]` with `q` in `Frag` from `CleanA` of `p`** (the
case of `runX_clean`). -/
theorem cleanA_seven {p q : Nomm} (hq : ∀ goal : CGoal S, Frag q goal) (ih : CleanA S Map p) :
    CleanA S Map (Nomm.n7 p q) := by
'''

TAIL = '''
end Comp
end SkaModel
end Formalization
'''

out = (HEAD + P_DOC + P.rstrip("\n") + "\n\n" + N_DOC + N.rstrip("\n") + "\n\n"
       + "/-- **The tag clause of `[7 p q]` for `%done` or `%pick`.** -/\n" + TP + "\n"
       + "/-- **The tag clause of `[7 p q]` under a fork-free `%next`.** -/\n" + TN + "\n"
       + CLEAN + cl + "\n" + TAIL)
(SKA / "CompSevenV.lean").write_text(out)
print("wrote", SKA / "CompSevenV.lean", len(out.split("\n")), "lines")
