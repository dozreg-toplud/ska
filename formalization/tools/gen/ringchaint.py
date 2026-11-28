#!/usr/bin/env python3
"""The threaded run link at `mono` `&` against `runLCMR` (track K, README Gaps 19 (h)).

Copies the T chain (`lemmas/Compiler/CompRunT{Leaf,...,Class}.lean`) and the declarations of the R
chain it uses (`CompRunR*.lean`, `CompRunDirectMonoP.lean`) whose statements mention `runLCM`,
with `runLCM` replaced by `runLCMR` (`Ska/CompRingRun.lean`, the same structure with the case
`%2` as `callLMR`) and every copied name `X` renamed `XG`.  Only the declarations the goal
theorems reach are copied (a closure over the names they use).  Hand-written: the transfer of
`runLCM_true` (`runLCM_trueG`, from `runLCMR_eq`), `runLCM_cons_doneG`, `CallOkTG` (the call's
ring is `env.ring b`, `RinOk`, `CallNounMTG`), `callOkTG_of_T`, `dirCallsTG_of_T`; the case `%2`
of the induction by `comp_run_n2_directXTTG` (`CompRunDirectRingM.lean`).  Every patch is
asserted by count.

Run from `formalization/`: `python3 tools/gen/ringchaint.py` writes
`lemmas/Compiler/CompRunTG{Base,Case,Six,Class}.lean`.
"""
import re
import sys

C = "lemmas/Compiler/"
TPARTS = "Leaf Cons Five Ten SixS SixN SixF SixL SixAll Class".split()
RFILES = ["CompRunRBase", "CompRunRRes", "CompRunRLeaf", "CompRunRCons", "CompRunRFive", "CompRunRTen",
          "CompRunRSixS", "CompRunRSixN", "CompRunRSixF", "CompRunRSixL", "CompRunRSixAll", "CompRunRClass",
          "CompRunDirectMonoP"]
TFILES = ["CompRunT" + p for p in TPARTS]
ROOTS = ["comp_run_dirT", "comp_run_dirXT", "res_dirT"]

# names whose copies are written by hand (or exist): name -> replacement
HAND = {
    "PartRT": "PartRTR",
    "runLCM_true": "runLCM_trueG",
    "runLCM_cons_done": "runLCM_cons_doneG",
    "CallOkT": "CallOkTG",
    "comp_run_n2_directXTT": "comp_run_n2_directXTTG",
    "crd_model_n2M": "crd_model_n2MR",
    "crd_model_dropM": "crd_model_dropMR",
    "crd_goalsM": "crd_goalsMR",
    "crdCallMM": "crdCallMMR",
}
# names never copied (they do not depend on the run model, or are replaced by a patch)
SKIP = {"dirCallsT_of", "dirCallsT_nested", "callOkT_of", "comp_run_n2_directXT", "yOk_eq"}

HEAD_RE = re.compile(r"^(/--|/-!|theorem |def |noncomputable |structure |abbrev |lemma |section|end |end$|variable |"
                     r"open |set_option |namespace |@\[|instance |private )")
DECL_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private )?(?:noncomputable )?(theorem|def|structure|abbrev|lemma)\s+"
                     r"([A-Za-z0-9_'.]+)", re.M)
RUN = re.compile(r"\brunLCM\b")
TOK = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")


def chunks(path):
    """The top-level chunks of a file: (name or None, kind, text); a doc comment goes with its declaration."""
    lines = open(path).read().split("\n")
    out, cur = [], []
    for ln in lines:
        doc_only = bool(cur) and cur[0].startswith("/--") and not any(DECL_RE.match(c) for c in cur)
        if HEAD_RE.match(ln) and cur and not doc_only:
            out.append("\n".join(cur))
            cur = []
        cur.append(ln)
    if cur:
        out.append("\n".join(cur))
    res = []
    for t in out:
        m = DECL_RE.search(t)
        if m and not t.lstrip().startswith("/-!"):
            res.append((m.group(2), m.group(1), t))
        else:
            res.append((None, None, t))
    return res


def strip(t):
    t = re.sub(r"/-.*?-/", "", t, flags=re.S)
    return re.sub(r"--[^\n]*", "", t)


def sig(kind, t):
    s = strip(t)
    return s.split(":=", 1)[0] if kind in ("theorem", "lemma") else s


src = {}   # name -> (file, kind, text)
order = []
for f in RFILES + TFILES:
    for n, k, t in chunks(C + f + ".lean"):
        if n is None:
            continue
        if n in src:
            sys.exit(f"duplicate {n} in {f} and {src[n][0]}")
        src[n] = (f, k, t)
        order.append(n)

# qualify: the statement mentions runLCM or a qualifying name
qual = set(HAND)
changed = True
while changed:
    changed = False
    for n in order:
        if n in qual:
            continue
        f, k, t = src[n]
        s = sig(k, t)
        if RUN.search(s) or (set(TOK.findall(s)) & qual):
            qual.add(n)
            changed = True

# closure from the roots through the full text
need, todo = set(), list(ROOTS)
while todo:
    n = todo.pop()
    if n in need or n in HAND or n in SKIP:
        continue
    need.add(n)
    for t in set(TOK.findall(strip(src[n][2]))):
        if t in src and t in qual and t not in need:
            todo.append(t)

ren = {n: n + "G" for n in need}
ren.update(HAND)
for n, v in ren.items():
    assert not v.endswith("NG"), v
    assert v == HAND.get(n) or v not in src, v


def rename(t):
    t = RUN.sub("runLCMR", t)
    return re.sub(r"[A-Za-z_][A-Za-z0-9_']*", lambda m: ren.get(m.group(0), m.group(0)), t)


def patch(t, a, b, n=1):
    c = t.count(a)
    assert c == n, (a[:80], c, n)
    return t.replace(a, b)


PATCHES = {
    # the copies of the call's results: the ring model (`crd_model_n2MR` takes no `hri`)
    "res_n2_callMono": [
        ("(hdr : crdDrop (env.pure b) goal = false) (hri : env.ring b = Option.none) (hnb : env.need b = some nb)",
         "(hdr : crdDrop (env.pure b) goal = false) (hnb : env.need b = some nb)"),
        ("crd_model_n2MR env msup p q b nb goal region hdr hri hnb", "crd_model_n2MR env msup p q b nb goal region hdr hnb"),
    ],
    "res_n2_directMono": [
        ("{b : Bell} {nb : NeedOrd} (hri : env.ring b = Option.none)\n", "{b : Bell} {nb : NeedOrd}\n"),
        ("res_n2_callMonoG ihp ihq hdr hri hnb hi h", "res_n2_callMonoG ihp ihq hdr hnb hi h"),
    ],
    "comp_run_dirT": [
        ("obtain ⟨⟨hcd, -, hri, nb, hnb, hE⟩, hdp, hdq⟩ := hd", "obtain ⟨⟨hcd, -, hro, nb, hnb, hE⟩, hdp, hdq⟩ := hd"),
        ("comp_run_n2_directXTTG (hY msup) h7 hcode env p q P Q b hcd nb hE hri hnb goal g hi",
         "comp_run_n2_directXTTG (hY msup) h7 hcode env p q P Q b hcd (env.ring b) rfl hro nb hE hnb goal g hi"),
        ("res_n2_directMonoG P.res Q.res hri hnb", "res_n2_directMonoG P.res Q.res hnb"),
    ],
}

HEADER = """
namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun} {X : GenRest → Noun → Noun → Prop} {Y : GenRest → GenRest → Prop}
"""
FOOT = "\nend Compiler\nend Formalization\n"

BASE_HAND = r'''
/-! ## Hand-written: `runLCMR` on a nomm with no direct call, the cons step -/

/-- A nomm with no direct call has no ring at a direct call. -/
theorem ringFreeN_of_noDirectG (env : CallEnv) : ∀ (nm : Nomm), nm.noDirect = true → RingFreeN env nm := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro h; simp only [Nomm.noDirect, Bool.and_eq_true] at h; exact ⟨ihp h.1, ihq h.2⟩
  | n2 p q info ihp ihq =>
    intro h
    cases info with
    | none =>
      simp only [Nomm.noDirect, Option.isNone_none, Bool.true_and, Bool.and_eq_true] at h
      exact ⟨fun _ _ e => (by cases e), ihp h.1, ihq h.2⟩
    | some _ => simp [Nomm.noDirect] at h
  | n3 p ih => intro h; exact ih h
  | n4 p ih => intro h; exact ih h
  | n5 p q ihp ihq =>
    intro h; simp only [Nomm.noDirect, Bool.and_eq_true] at h; exact ⟨ihp h.1, ihq h.2⟩
  | n6 p q r ihp ihq ihr =>
    intro h; simp only [Nomm.noDirect, Bool.and_eq_true] at h; exact ⟨ihp h.1.1, ihq h.1.2, ihr h.2⟩
  | n7 p q ihp ihq =>
    intro h; simp only [Nomm.noDirect, Bool.and_eq_true] at h; exact ⟨ihp h.1, ihq h.2⟩
  | n10 a v q ihv ihq =>
    intro h; simp only [Nomm.noDirect, Bool.and_eq_true] at h; exact ⟨ihv h.1, ihq h.2⟩
  | _ => intro _; simp [RingFreeN]

section
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **With `mono` `&`, on a nomm without a direct call, `runLCMR` is `runLC`.** -/
theorem runLCM_trueG (env : CallEnv) {nm : Nomm} (h : nm.noDirect = true) (sup : Option Nomm)
    (goal : CGoalL S) (region : List Nat) :
    (runLCMR env true sup nm goal region : CM Map (NextL S)) = runLC env sup nm goal region :=
  (runLCMR_eq env true nm (ringFreeN_of_noDirectG env nm h) sup goal region).trans (runLCM_true env h sup goal region)

theorem runLCM_cons_doneG (env : CallEnv) (sup : Option Nomm) (p q : Nomm) (region : List Nat) :
    (runLCMR env true sup (Nomm.cons p q) CGoalL.done region : CM Map (NextL S)) = (do
      let r ← re
      let o ← emit ⟨[], [], Termin.don r⟩
      runLCMR env true sup (Nomm.cons p q) (CGoalL.next (Lazy.ofSure (lazyReg r)) (jmp0 o)) region) := by
  conv => lhs; unfold runLCMR
  rfl

end
'''

CLASS_HAND = r'''
/-! ## Hand-written: the call through a ring -/

/-- **What one direct call takes, threaded, ring or not**: `CallOkT` with the callee's ring
`env.ring b` (a ring noun, `RinOk`) in place of "no ring", and the call's nouns `CallNounMTG` at
that ring (no hot driver: `RinAt`). -/
def CallOkTG (env : CallEnv) (cod ctx : Noun) (E : GenRest → Prop) (Y : GenRest → GenRest → Prop)
    (msup : Option Nomm) (p q : Nomm) (b : Bell) : Prop :=
  CodePure cod env b ∧ env.cod b = some (env.pure b) ∧ RinOk (env.ring b) ∧
    ∃ nb, env.need b = some nb ∧ ∀ x, x.NoSoft → E x → ∃ x' sur SOF, Y x x' ∧
      CallNounMTG msup ctx p q b nb sur x x' (A 0) SOF (env.ring b)

/-- The old `CallOkT` (no ring) is `CallOkTG`. -/
theorem callOkTG_of_T {env : CallEnv} {cod : Noun} {E : GenRest → Prop} {Y : GenRest → GenRest → Prop}
    {msup : Option Nomm} {p q : Nomm} {b : Bell} (h : CallOkT env cod ctx E Y msup p q b) :
    CallOkTG env cod ctx E Y msup p q b := by
  obtain ⟨h1, h2, h3, nb, h4, h5⟩ := h
  refine ⟨h1, h2, by rw [h3]; trivial, nb, h4, fun x hx hE => ?_⟩
  obtain ⟨x', sur, SOF, hy, hT, -⟩ := h5 x hx hE
  rw [h3]
  exact ⟨x', sur, SOF, hy, callNounMTG_of_mt hT⟩
'''

CLASS_TAIL = r'''
/-- **The old `DirCallsT` (no ring) is `DirCallsTG`.** -/
theorem dirCallsTG_of_T {env : CallEnv} {cod : Noun} {E : GenRest → Prop} {Y : GenRest → GenRest → Prop} :
    ∀ (ms : Option Nomm) (n : Nomm), DirCallsT env cod ctx E Y ms n → DirCallsTG env cod ctx E Y ms n
  | ms, Nomm.cons p q, h => ⟨dirCallsTG_of_T ms p h.1, dirCallsTG_of_T ms q h.2⟩
  | _, Nomm.n0 _, _ => trivial
  | _, Nomm.n1 _, _ => trivial
  | ms, Nomm.n2 p q Option.none, h => ⟨dirCallsTG_of_T ms p h.1, dirCallsTG_of_T ms q h.2⟩
  | ms, Nomm.n2 p q (some (_, _)), h => ⟨callOkTG_of_T h.1, dirCallsTG_of_T ms p h.2.1, dirCallsTG_of_T ms q h.2.2⟩
  | ms, Nomm.n3 p, h => dirCallsTG_of_T ms p h
  | ms, Nomm.n4 p, h => dirCallsTG_of_T ms p h
  | ms, Nomm.n5 p q, h => ⟨dirCallsTG_of_T ms p h.1, dirCallsTG_of_T ms q h.2⟩
  | ms, Nomm.n6 p q r, h => ⟨dirCallsTG_of_T ms p h.1, dirCallsTG_of_T ms q h.2.1, dirCallsTG_of_T ms r h.2.2⟩
  | ms, Nomm.n7 p q, h => ⟨dirCallsTG_of_T ms p h.1, dirCallsTG_of_T (some p) q h.2⟩
  | ms, Nomm.n10 _ v q, h => ⟨dirCallsTG_of_T ms v h.1, dirCallsTG_of_T ms q h.2⟩
  | _, Nomm.n11s _ _ _, _ => trivial
  | _, Nomm.n11d _ _ _ _, _ => trivial
  | _, Nomm.n12 _ _, _ => trivial
  | _, Nomm.mean _ _ _ _ _, _ => trivial
'''

OUT = [
    ("CompRunTGBase", ["lemmas.Compiler.CompRunTClass", "lemmas.Compiler.CompRunDirectRingM", "lemmas.Ska.CompRingRunEq"], RFILES, BASE_HAND, "",
     "the declarations of the R chain the T chain uses, against `runLCMR`"),
    ("CompRunTGCase", ["lemmas.Compiler.CompRunTGBase"], ["CompRunT" + p for p in "Leaf Cons Five Ten".split()], "", "",
     "the cases `%3`, `%4`, cons, `%5`, `%2` (indirect), `%10`, threaded, against `runLCMR`"),
    ("CompRunTGSix", ["lemmas.Compiler.CompRunTGCase"], ["CompRunT" + p for p in "SixS SixN SixF SixL SixAll".split()], "", "",
     "the case `%6`, threaded, against `runLCMR`"),
    ("CompRunTGClass", ["lemmas.Compiler.CompRunTGSix"], ["CompRunTClass"], CLASS_HAND, CLASS_TAIL,
     "the induction over the nomm, threaded, against `runLCMR env true` (the call through a ring included)"),
]

done = set()
for name, imps, files, pre, post, what in OUT:
    body = []
    for f in files:
        insec, secvars = False, []
        for n, k, t in chunks(C + f + ".lean"):
            if n is None:
                st = t.strip()
                if st.startswith("section"):
                    insec, secvars = True, []
                elif insec and st.startswith("variable"):
                    secvars.append(st.split("\n\n")[0])
                elif insec and (st == "end" or st.startswith("end\n")):
                    insec, secvars = False, []
            if n in need:
                tt = rename(t)
                for a, b2 in PATCHES.get(n, []):
                    tt = patch(tt, a, b2)
                tt = tt.rstrip() + "\n"
                if secvars:
                    tt = "section\n" + "\n".join(secvars) + "\n\n" + tt + "\nend\n"
                body.append(tt)
                done.add(n)
    doc = (f"/-!\n# {what} (track K, README Gaps 19 (h))\n\nGenerated by `tools/gen/ringchaint.py` from "
           + ", ".join(f"`{f}.lean`" for f in files)
           + "; do not edit.  Each copy is its source with `runLCM` replaced by `runLCMR`"
           + " (`Ska/CompRingRun.lean`) and every copied name `X` renamed `XG`.\n-/\n")
    txt = "\n".join(f"import {i}" for i in imps) + "\n\n" + doc + HEADER + pre + "\n" + "\n".join(body) + post + FOOT
    open(C + name + ".lean", "w").write(txt)

missing = need - done
assert not missing, missing
for n, ps in PATCHES.items():
    assert n in need, n
print("copied", len(need), "declarations", file=sys.stderr)
