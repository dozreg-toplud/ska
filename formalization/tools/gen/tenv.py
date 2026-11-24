#!/usr/bin/env python3
"""Generate lemmas/Ska/CompTenV.lean: `[10 [a v] q]` with operands whose
runs may make proxies, from the text of `n10N_body`, `runOKN_n10`,
`runOKP_n10D`, `runOKP_n10P` (CompN10N.lean) and the case `ten` of
`runX_clean` (CompFragX.lean).  Run from formalization/:
python3 tools/gen/tenv.py.  Every extraction and replacement asserts its
match count.
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


def thm(ls, name):
    """The text of `theorem name` up to the next doc comment, section or theorem."""
    i = [k for k in range(len(ls)) if ls[k].startswith("theorem " + name + " ")]
    assert len(i) == 1, (name, i)
    i = i[0]
    j = i + 1
    while j < len(ls) and not (ls[j].startswith("/-") or ls[j].startswith("theorem ") or ls[j].startswith("end ")):
        j += 1
    return "\n".join(ls[i:j]).rstrip("\n") + "\n"


nn = lines("CompN10N.lean")
fx = lines("CompFragX.lean")

P0 = "(fun r => HoonMap.get g0.cond r = Option.none)"

# --- the body under %next -----------------------------------------------
B = thm(nn, "n10N_body")
B = rep(B, "theorem n10N_body (lib : Lib) {a : Nat} {v q : Nomm} (hv : NextOK (S := S) (Map := Map) lib v)\n"
           "    (hq : NextOK (S := S) (Map := Map) lib q)",
        "theorem n10NV_body (lib : Lib) {a : Nat} {v q : Nomm} (hv : OKNV (S := S) (Map := Map) lib v)\n"
        "    (hq : OKNV (S := S) (Map := Map) lib q)")
B = rep(B, "    {nex : NextL S} (hj : GJ g0.bo (CGoal.next sur th)) (hok : GoalOK g0 (CGoal.next sur th)) (hcl : Clean sur.ned)\n"
           "    (hcount : sixCount (Nomm.n10 a v q) ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)\n"
           "    (h : n10Body a v q ⟨ofSure sur, th⟩ region g0 = some (nex, g1)) :\n"
           "    RunOKN (Map := Map) lib (Nomm.n10 a v q) sur th g0 g1 nex := by\n",
        "    {nex : NextL S} (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = [])\n"
        "    (hok : GoalOK g0 (CGoal.next sur th)) (hcl : Clean sur.ned)\n"
        "    (hcount : sixCount (Nomm.n10 a v q) ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)\n"
        "    (hcl0 : Clear g0) (hcb : CondBelow g0) (hkg : ∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none)\n"
        "    (h : n10Body a v q ⟨ofSure sur, th⟩ region g0 = some (nex, g1)) :\n"
        "    RunOKNV (Map := Map) lib (Nomm.n10 a v q) sur th g0 g1 nex := by\n")
B = rep(B, "  simp only [sixCount] at hcount\n",
        "  simp only [sixCount] at hcount\n"
        "  have cl2 : Clear g2 := hcl0.growU (ID.1.toU hu)\n"
        "  have cb2 : CondBelow g2 := (condFresh_of_eq E2.1 c2).below hcb\n"
        "  have nk2 : ∀ (n : Need), (∀ y, NMem n y → NMem sur.ned y ∨ (g0.re ≤ y ∧ y < g2.re)) →\n"
        "      ∀ y, NMem n y → HoonMap.get g2.cond y = Option.none := fun n M y hy => by\n"
        "    rw [c2]\n"
        "    rcases M y hy with e | ⟨e, _⟩\n"
        "    · exact hkg y e\n"
        "    · exact condBelow_none hcb e\n")
B = rep(B, "    (by omega) (by omega) d2 u2 h3\n",
        "    (by omega) (by omega) d2 u2 cl2 cb2 (nk2 _ Md) h3\n")
B = rep(B, "    (by have := Rv.lo; have := Rv.hi; omega) (Rv.ext.2.2.1.trans d2) (Rv.grow.up u2) h4\n",
        "    (by have := Rv.lo; have := Rv.hi; omega) (Rv.ext.2.2.1.trans d2) (Rv.grow.up u2) (cl2.growU Rv.grow)\n"
        "    (Rv.cfr.below cb2) (fun y hy => by rw [Rv.cfr.get_lt (lt2 _ Mr y hy)]; exact nk2 _ Mr y hy) h4\n")
OPEN = B.split("  refine (binaryN_ok")[0]
B = rep(B, "  refine (binaryN_ok (pureEval_n10 (by omega) v q) hok E2 (ID.1.toU hu) c2 Mr Md (fun r hr hd => Ddr r hd hr)\n"
           "    Rv Rq (cv CI.1 h3) (cq CI.2 h4) hcp hu d0 (by simp only [sixCount]; omega)\n"
           "    (fun x y hn => ?_) (fun c hc σ O st regs t gul x y fx fy hx hy => ?_)).toN\n",
        "  refine binaryNV_ok (pureEval_n10 (by omega) v q) hok E2 (ID.1.toU hu) c2 hcb Mr Md (fun r hr hd => Ddr r hd hr)\n"
        "    Rv Rq (cv CI.1 h3) (cq CI.2 h4) hcp hu d0 (by simp only [sixCount]; omega)\n"
        "    (fun x y hn => ?_)\n"
        "    (fix_of_keeps (gs := g0) rfl\n"
        "      (keepsA_into (P := " + P0 + ") (nex := ⟨sur, th⟩) d0 ⟨hkg, jmpIn_nil hth⟩\n"
        "        (fun r hr => condBelow_none hcb hr) hs2).1\n"
        "      (keeps_into (nex := ⟨sur, th⟩) d0 ⟨fun r hr => hok.2 r hr, jmpIn_nil hth⟩ hs2).1)\n"
        "    (fun c hc σ O st regs t gul x y fx fy hx hy => ?_)\n")

# --- the tag clause of the body --------------------------------------------
TB = OPEN
TB = rep(TB, "theorem n10NV_body (lib : Lib) {a : Nat} {v q : Nomm} (hv : OKNV (S := S) (Map := Map) lib v)\n"
             "    (hq : OKNV (S := S) (Map := Map) lib q)",
         "theorem n10NV_tagBody (lib : Lib) {a : Nat} {v q : Nomm} (hv : OKNV (S := S) (Map := Map) lib v)\n"
         "    (hq : OKNV (S := S) (Map := Map) lib q) (tv : TagNV (S := S) (Map := Map) v)\n"
         "    (tq : TagNV (S := S) (Map := Map) q)")
TB = rep(TB, "(cv : CleanN S Map v) (cq : CleanN S Map q)\n    (hvp : v.pure = true)", "(cv : CleanN S Map v)\n    (hvp : v.pure = true)")
TB = rep(TB, "    RunOKNV (Map := Map) lib (Nomm.n10 a v q) sur th g0 g1 nex := by\n",
         "    CondTag region g0.cond g1.cond := by\n")
iv = TB.index("  have Rv := hv (sur := don)")
iq = TB.index("  have Rq := hq (sur := rec)")
TB = TB + TB[iv:iq].replace("  have Rv := hv", "  have Tv := tv") + TB[iq:].replace("  have Rq := hq", "  have Tq := tq")
TB += ("  exact (CondTag.of_eq c2).trans (Tv.trans (Tq.trans (CondTag.of_eq ((kc_copyL _ _).keep _ _ _ hcp))))\n")

# --- under %next ------------------------------------------------------------
N = thm(nn, "runOKN_n10")
N = rep(N, "theorem runOKN_n10 (lib : Lib) {a : Nat} {v q : Nomm} (hv : NextOK (S := S) (Map := Map) lib v)\n"
           "    (hq : NextOK (S := S) (Map := Map) lib q) (cv : CleanN S Map v) (cq : CleanN S Map q)\n"
           "    (hvp : v.pure = true) (hqp : q.pure = true) : NextOK (S := S) (Map := Map) lib (Nomm.n10 a v q) :=\n"
           "  fun hj _ hok hcl hcount b0 d0 hu h => by\n",
        "theorem runOKNV_n10 (lib : Lib) {a : Nat} {v q : Nomm} (hv : OKNV (S := S) (Map := Map) lib v)\n"
        "    (hq : OKNV (S := S) (Map := Map) lib q) (cv : CleanN S Map v) (cq : CleanN S Map q)\n"
        "    (hvp : v.pure = true) (hqp : q.pure = true) : OKNV (S := S) (Map := Map) lib (Nomm.n10 a v q) :=\n"
        "  fun hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h => by\n")
N = rep(N, "    exact n10N_body lib hv hq cv cq hvp hqp hj hok hcl hcount b0 d0 hu h\n",
        "    exact n10NV_body lib hv hq cv cq hvp hqp hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h\n")
TN = rep(N, "theorem runOKNV_n10 (lib : Lib) {a : Nat} {v q : Nomm} (hv : OKNV (S := S) (Map := Map) lib v)\n"
            "    (hq : OKNV (S := S) (Map := Map) lib q) (cv : CleanN S Map v) (cq : CleanN S Map q)\n"
            "    (hvp : v.pure = true) (hqp : q.pure = true) : OKNV (S := S) (Map := Map) lib (Nomm.n10 a v q) :=\n",
         "theorem ten_tagNV (lib : Lib) {a : Nat} {v q : Nomm} (hv : OKNV (S := S) (Map := Map) lib v)\n"
         "    (hq : OKNV (S := S) (Map := Map) lib q) (tv : TagNV (S := S) (Map := Map) v)\n"
         "    (tq : TagNV (S := S) (Map := Map) q) (cv : CleanN S Map v)\n"
         "    (hvp : v.pure = true) (hqp : q.pure = true) : TagNV (S := S) (Map := Map) (Nomm.n10 a v q) :=\n")
TN = rep(TN, "    exact n10NV_body lib hv hq cv cq hvp hqp hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h\n",
         "    exact n10NV_tagBody lib hv hq tv tq cv hvp hqp hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h\n")

# --- for %done and %pick ------------------------------------------------------
NEWARGS = ("    (by simpa [emitted_drop] using d0) ((G.toU hu).up hu) (hcl0.growU (G.toU hu))\n"
           "    (CondFresh.below (condFresh_of_eq (g0 := g0) (Nat.le_succ _) rfl) hcb)\n"
           "    (fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; exact condBelow_none hcb (Nat.le_refl _)) h\n")


def doneish(name, new, goalty, extra, finb, fink, tagname):
    T = thm(nn, name)
    T = rep(T, "theorem " + name + " (lib : Lib) {a : Nat} {v q : Nomm} (hv : NextOK (S := S) (Map := Map) lib v)\n"
               "    (hq : NextOK (S := S) (Map := Map) lib q)",
            "theorem " + new + " (lib : Lib) {a : Nat} {v q : Nomm} (hv : OKNV (S := S) (Map := Map) lib v)\n"
            "    (hq : OKNV (S := S) (Map := Map) lib q)")
    T = rep(T, "    OKP (Map := Map) lib " + goalty + " (Nomm.n10 a v q) := by\n",
            extra + "    OKV (Map := Map) lib " + goalty + " (Nomm.n10 a v q) := by\n")
    T = rep(T, "  intro region g0 g1 nex _ ", "  intro region g0 g1 nex _ ")
    T = rep(T, " hcount b0 d0 hu h\n", " hcount b0 d0 hu hcl0 hcb h\n")
    T = rep(T, "  have Hn := n10N_body lib hv hq cv cq hvp hqp (sur := lazyReg g0.re) (th := jmp0 g0.bo)\n"
               "    ⟨b0, by simp [jmp0, emitted_bo]⟩ ⟨trivial,",
            "  have Hn := n10NV_body lib hv hq cv cq hvp hqp (sur := lazyReg g0.re) (th := jmp0 g0.bo)\n"
            "    ⟨b0, by simp [jmp0, emitted_bo]⟩ rfl ⟨trivial,")
    T = rep(T, "    (by simpa [emitted_drop] using d0) ((G.toU hu).up hu) h\n", NEWARGS)
    op = T.split("  refine unaryG_ok")[0]
    T = rep(T, "  refine unaryG_ok", "  refine unaryGV_ok")
    T = rep(T, "    (fresh_emitted (by simpa using d0) rfl rfl) Hn rfl ?_\n",
            "    (fresh_emitted (by simpa using d0) rfl rfl) Hn rfl\n"
            "    (fix_of_keeps (gs := g0) rfl ((keepsA_reg _ g0 _ (Nat.le_succ _)).trans (keepsA_emitted d0\n"
            "        (blobIn_fin " + finb + ")))\n"
            "      ((keeps_reg g0 _ (Nat.le_succ _)).trans (keeps_emitted d0 (blobIn_fin " + fink + "))))\n"
            "    ?_\n")
    # the tag clause: the opening, then the body's tag clause
    TT = op
    TT = rep(TT, "theorem " + new + " (lib : Lib)", "theorem " + tagname + " (lib : Lib)")
    TT = rep(TT, "    (hq : OKNV (S := S) (Map := Map) lib q)",
             "    (hq : OKNV (S := S) (Map := Map) lib q) (tv : TagNV (S := S) (Map := Map) v)\n"
             "    (tq : TagNV (S := S) (Map := Map) q)")
    TT = rep(TT, "    OKV (Map := Map) lib " + goalty + " (Nomm.n10 a v q) := by\n",
             "    TagV (Map := Map) " + goalty + " (Nomm.n10 a v q) := by\n")
    TT = rep(TT, "  have Hn := n10NV_body lib hv hq cv cq hvp hqp", "  have Tn := n10NV_tagBody lib hv hq tv tq cv hvp hqp")
    TT += "  exact Tn\n"
    return T, TT


D, TD = doneish("runOKP_n10D", "runOKV_n10D", "(CGoal.done : CGoal S)", "",
                "(condBelow_none hcb (Nat.le_refl _))", "(Nat.lt_succ_self _)", "ten_tagD")
P, TP = doneish("runOKP_n10P", "runOKV_n10P", "(CGoal.pick z o : CGoal S)",
                "    (hz : z.args = []) (hzo : o.args = []) :\n",
                "⟨condBelow_none hcb (Nat.le_refl _), jmpIn_nil hz, jmpIn_nil hzo⟩",
                "⟨Nat.lt_succ_self _, jmpIn_nil hz, jmpIn_nil hzo⟩", "ten_tagP")
P = rep(P, "(hvp : v.pure = true) (hqp : q.pure = true) (z o : Jmp) :\n    (hz", "(hvp : v.pure = true) (hqp : q.pure = true) (z o : Jmp)\n    (hz")
TP = rep(TP, "(hvp : v.pure = true) (hqp : q.pure = true) (z o : Jmp) :\n    (hz : z.args = []) (hzo : o.args = []) :\n",
         "(hvp : v.pure = true) (hqp : q.pure = true) (z o : Jmp) :\n")

# --- clean ----------------------------------------------------------------
i = find(fx, "  | @ten a v q hv' hq' ihv ihq =>", find(fx, "theorem runX_clean {nm : Nomm} (hf : FragX (S := S) nm) : CleanA S Map nm := by"))
j = find(fx, "  | @sevenFrom axe q ha _ ihq =>", i)
cl = fx[i + 1:j]
assert cl[0] == "    have hvp := fragX_pure hv'" and cl[1] == "    have hqp := fragX_pure hq'", cl[:2]
cl = "\n".join(dedent(cl[2:], 2)).rstrip("\n") + "\n"

HEAD = '''import lemmas.Ska.CompFourV
import lemmas.Ska.CompN10N

/-!
# `[10 [a v] q]` with operands whose runs make proxies

README Gaps 12.2 (eleventh session).  Generated by `tools/gen/tenv.py` from
`n10N_body`, `runOKN_n10`, `runOKP_n10D`, `runOKP_n10P` (`CompN10N.lean`) and
the case `ten` of `runX_clean`; do not edit by hand.  The donor `v` runs
under the fork-free `%next` of the donor need of `+into`, the recipient `q`
under that of the recipient need (`OKNV`); the `%con` blocks of `+into`
mention the goal's registers and fresh ones, so unproxying by a later `cond`
leaves them alone (`keepsA_into`, `keeps_into`, `fix_of_keeps`).

* `n10NV_body`, `runOKNV_n10`: under `%next`, through `binaryNV_ok`.
* `runOKV_n10D`, `runOKV_n10P`: for `%done` and `%pick` (`unaryGV_ok`).
* `n10NV_tagBody`, `ten_tagNV`, `ten_tagD`, `ten_tagP`: the tag clauses
  (`+into` and `+copy` keep `cond`).
* `cleanA_ten`: `CleanA` of `[10 [a v] q]`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`%10` under a fork-free `%next` with `OKNV` operands**, after
`+simple-next` (`n10N_body` with `binaryNV_ok`). -/
'''

TAIL = '''
end Comp
end SkaModel
end Formalization
'''

out = (HEAD + B
       + "\n/-- **The tag clause of the body of `%10`.** -/\n" + TB
       + "\n/-- **`%10` under a fork-free `%next` with `OKNV` operands.** -/\n" + N
       + "\n/-- **The tag clause of `%10` under `%next`.** -/\n" + TN
       + "\n/-- **`%10` for `%done` with `OKNV` operands.** -/\n" + D
       + "\n/-- **The tag clause of `%10` for `%done`.** -/\n" + TD
       + "\n/-- **`%10` for `%pick` with `OKNV` operands.** -/\n" + P
       + "\n/-- **The tag clause of `%10` for `%pick`.** -/\n" + TP
       + "\n/-- **`CleanA` of `[10 [a v] q]`** (the case of `runX_clean`). -/\n"
       + "theorem cleanA_ten {a : Nat} {v q : Nomm} (ihv : CleanA S Map v) (ihq : CleanA S Map q) (hvp : v.pure = true)\n"
       + "    (hqp : q.pure = true) : CleanA S Map (Nomm.n10 a v q) := by\n" + cl
       + TAIL)
(SKA / "CompTenV.lean").write_text(out)
print("wrote", SKA / "CompTenV.lean", len(out.split("\n")), "lines")
