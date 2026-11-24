#!/usr/bin/env python3
"""Generate lemmas/Ska/CompFiveV.lean: `[5 p q]` with parts whose runs may
make proxies, from the text of `runOKG_n5` (CompN5N.lean) and of the case
`five` of `runX_clean`.  Run from formalization/:  python3 tools/gen/fivev.py
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


nn = lines("CompN5N.lean")
i = find(nn, "theorem runOKG_n5 (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)")
j = find(nn, "end Comp", i)
G = "\n".join(nn[i:j]).rstrip("\n") + "\n"
G = rep(G, "theorem runOKG_n5 (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)\n"
           "    (hq : NextOK (S := S) (Map := Map) lib q)",
        "theorem runOKGV_n5 (lib : Lib) {p q : Nomm} (hp : OKNV (S := S) (Map := Map) lib p)\n"
        "    (hq : OKNV (S := S) (Map := Map) lib q)")
G = rep(G, "    (d0 : g0.drop = false) (hu : UpBelow g0)\n"
           "    (h : runL (Nomm.n5 p q) (CGoal.toL goal) region g0 = some (nex, g1)) :\n"
           "    RunOKG (Map := Map) lib (Nomm.n5 p q) goal g0 g1 nex := by",
        "    (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0) (hcb : CondBelow g0) (gin : GoalIn g0.re goal)\n"
        "    (gak : GoalA (fun r => HoonMap.get g0.cond r = Option.none) goal)\n"
        "    (h : runL (Nomm.n5 p q) (CGoal.toL goal) region g0 = some (nex, g1)) :\n"
        "    RunOKGV (Map := Map) lib (Nomm.n5 p q) goal g0 g1 nex := by")
G = rep(G, "  have u2 : UpBelow g2 := (G2.toU hu).up hu\n",
        "  have u2 : UpBelow g2 := (G2.toU hu).up hu\n"
        "  have cl2 : Clear g2 := hcl0.growU (G2.toU hu)\n"
        "  have cb2 : CondBelow g2 := (condFresh_of_eq E2.1 c2).below hcb\n")
G = rep(G, "    (Nat.le_trans b0 G2.bo) d2 u2 h3",
        "    (Nat.le_trans b0 G2.bo) d2 u2 cl2 cb2\n"
        "    (fun r hr => by simp only [lazyReg, NMem] at hr; rw [c2]; exact condBelow_none hcb (by omega)) h3")
G = rep(G, "    (Nat.le_trans b0 (Nat.le_trans G2.bo Rq.grow.bo)) (Rq.ext.2.2.1.trans d2) (Rq.grow.up u2) h4",
        "    (Nat.le_trans b0 (Nat.le_trans G2.bo Rq.grow.bo)) (Rq.ext.2.2.1.trans d2) (Rq.grow.up u2)\n"
        "    (cl2.growU Rq.grow) (Rq.cfr.below cb2)\n"
        "    (fun r hr => by\n"
        "      simp only [lazyReg, NMem] at hr\n"
        "      rw [Rq.cfr.get_lt (show r < g2.re by omega), c2]; exact condBelow_none hcb (by omega)) h4")
OPEN = G.split("  exact binaryN_ok (pureEval_n5 p q) hg E2 (G2.toU hu) c2\n")[0]
G = rep(G, "  exact binaryN_ok (pureEval_n5 p q) hg E2 (G2.toU hu) c2\n",
        "  have AS : AboveIn (fun r => HoonMap.get g0.cond r = Option.none) g0.bo g2 :=\n"
        "    (keepsA_n5Pre (P := fun r => HoonMap.get g0.cond r = Option.none)\n"
        "      (g := { { g0 with re := g0.re + 1 } with re := g0.re + 1 + 1 }) d0 gak\n"
        "      (condBelow_none hcb (show g0.re ≤ g0.re by omega)) (condBelow_none hcb (show g0.re ≤ g0.re + 1 by omega))\n"
        "      (fun r hr => condBelow_none hcb (Nat.le_trans (show g0.re ≤ g0.re + 1 + 1 by omega) hr)) h2).ab _\n"
        "      (aboveIn_start _ _)\n"
        "  have BS : BelowIn g0.bo g2 :=\n"
        "    (keeps_n5Pre (g := { { g0 with re := g0.re + 1 } with re := g0.re + 1 + 1 }) d0 (gin.mono (show g0.re ≤ g0.re + 1 + 1 by omega))\n"
        "      (show g0.re < g0.re + 1 + 1 by omega) (show g0.re + 1 < g0.re + 1 + 1 by omega) h2).bel _\n"
        "      (belowIn_start { { g0 with re := g0.re + 1 } with re := g0.re + 1 + 1 })\n"
        "  exact binaryGV_ok (pureEval_n5 p q) hg E2 (G2.toU hu) c2 hcb\n")
G = rep(G, "    (fun x y hn => absurd (hn.elim (fun a => a (fitsS_lazyReg _ x)) (fun a => a (fitsS_lazyReg _ y))) id)\n",
        "    (fun x y hn => absurd (hn.elim (fun a => a (fitsS_lazyReg _ x)) (fun a => a (fitsS_lazyReg _ y))) id)\n"
        "    (fun cf hcf k h0 h1 => by\n"
        "      have u0 : ∀ x, x < g2.re → unproxy cf x = unproxy g0.cond x := unproxy_agree (fun k hk => hcf k hk)\n"
        "      have u1 : ∀ x, HoonMap.get g0.cond x = Option.none → unproxy g0.cond x = id x :=\n"
        "        fun x hx => unproxy_none hx\n"
        "      cases hgb : HoonMap.get g2.blocks k with\n"
        "      | none => rfl\n"
        "      | some b =>\n"
        "        simp only [Option.map_some]\n"
        "        rw [unproxyBlob, renBlob_congr u0 (BS k b h0 h1 hgb), renBlob_congr u1 (AS k b h0 h1 hgb),\n"
        "          renBlob_id])\n")

# the tag clause: the opening, `Tq`, `Tp` and the chain
T = OPEN
T = rep(T, "theorem runOKGV_n5 (lib : Lib)", "theorem five_tagG (lib : Lib)")
T = rep(T, "(cp : CleanN S Map p) (cq : CleanN S Map q) (hpp : p.pure = true)", "(hpp : p.pure = true)")
T = rep(T, " (gin : GoalIn g0.re goal)\n    (gak : GoalA (fun r => HoonMap.get g0.cond r = Option.none) goal)\n", "\n")
T = rep(T, "    RunOKGV (Map := Map) lib (Nomm.n5 p q) goal g0 g1 nex := by",
        "    CondTag region g0.cond g1.cond := by")
T = rep(T, "theorem five_tagG (lib : Lib) {p q : Nomm} (hp : OKNV (S := S) (Map := Map) lib p)\n"
           "    (hq : OKNV (S := S) (Map := Map) lib q)",
        "theorem five_tagG (lib : Lib) {p q : Nomm} (hp : OKNV (S := S) (Map := Map) lib p)\n"
        "    (hq : OKNV (S := S) (Map := Map) lib q) (tp : TagNV (S := S) (Map := Map) p)\n"
        "    (tq : TagNV (S := S) (Map := Map) q)")
iq = T.index("  have Rq := hq (sur := lazyReg (g0.re + 1))")
ip = T.index("  have Rp := hp (sur := lazyReg g0.re)")
TQ = T[iq:ip].replace("  have Rq := hq", "  have Tq := tq")
TP = T[ip:].replace("  have Rp := hp", "  have Tp := tp")
T = T + TQ + TP + (
    "  have c1 : g1.cond = g4.cond := (kc_copyL _ _).keep _ _ _ hc\n"
    "  exact (CondTag.of_eq c2).trans (Tq.trans (Tp.trans (CondTag.of_eq c1)))\n")

# clean
fx = lines("CompFragX.lean")
i5 = find(fx, "  | @five p q hp' _ ihp ihq =>")
j5 = find(fx, "  | @ten a v q hv' hq' ihv ihq =>", i5)
cl = fx[i5 + 1:j5]
assert cl[0] == "    have hpp := fragX_pure hp'", cl[0]
cl = "\n".join(dedent(cl[1:], 2))

HEAD = '''import lemmas.Ska.CompFragUJGen

/-!
# `[5 p q]` with parts whose runs make proxies

README Gaps 12.2 (tenth session).  Generated by `tools/gen/fivev.py` from
`runOKG_n5` (`CompN5N.lean`) and the case `five` of `runX_clean`; do not
edit by hand.  The two operands run under the fork-free `%next` of their fresh
registers (`OKNV`), and the block of `n5Pre` mentions the goal's registers
and fresh ones, no key of a later `cond` when the goal's registers are no
keys (`gak`), so unproxying leaves it alone (`keepsA_n5Pre`, `keeps_n5Pre`).

* `runOKGV_n5`: `RunOKGV` of `[5 p q]` for every fork-free goal.
* `five_tagG`: its tag clause (`re`, `n5Pre` and `+copy` keep `cond`).
* `cleanA_five`: `CleanA` of `[5 p q]` from `CleanA` of its parts.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`[5 p q]` with operands that may make proxies** (`runOKG_n5` with
`OKNV` operands), for every fork-free goal whose registers are no keys. -/
'''

CLEAN = '''
/-- **`CleanA` of `[5 p q]` from `CleanA` of its parts** (the case of
`runX_clean`). -/
theorem cleanA_five {p q : Nomm} (hpp : p.pure = true) (ihp : CleanA S Map p) (ihq : CleanA S Map q) :
    CleanA S Map (Nomm.n5 p q) := by
'''

TAIL = '''
end Comp
end SkaModel
end Formalization
'''

out = (HEAD + G + "\n/-- **The tag clause of `[5 p q]`** for every fork-free goal. -/\n" + T + CLEAN + cl.rstrip("\n")
       + "\n" + TAIL)
(SKA / "CompFiveV.lean").write_text(out)
print("wrote", SKA / "CompFiveV.lean", len(out.split("\n")), "lines")
