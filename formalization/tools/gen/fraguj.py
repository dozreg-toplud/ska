#!/usr/bin/env python3
"""Generate the copied proofs of lemmas/Ska/CompFragUJGen.lean.

Each theorem below is the opening of an existing proof (the part that
establishes the hypotheses at each part's start), followed by the tag or clean
conclusion.  Run from formalization/:  python3 tools/gen/fraguj.py
It rewrites lemmas/Ska/CompFragUJGen.lean.  Every extraction and replacement
asserts its match count, so a change in the source proofs fails loudly.
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
    """Lines from the line equal to `first` (searching from `start`) up to the
    line equal to `last_excl` (excluded) or `last_incl` (included)."""
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


# --- clean needs of `%6` and cons (from `runX_clean`) -----------------------
fx = lines("CompFragX.lean")
i6 = find(fx, "  | @six c a b hc' _ _ ihc _ _ =>")
six_clean = seg(fx, "    intro goal region g0 g1 nex hc h", last_excl="  | four _ ih =>", start=i6)
six_clean = dedent(six_clean, 2)
ic = find(fx, "  | @cons p q hp' hq' ihp ihq =>")
cons_clean = seg(fx, "    intro goal region g0 g1 nex hc h", last_excl="  | @five p q hp' _ ihp ihq =>", start=ic)
cons_clean = dedent(cons_clean, 2)

# --- `%6` under a fork-free `%next` (from `sixNext_okNV`) -------------------
sv = lines("CompSixNextV.lean")
sn = seg(sv, "  rw [runL_n6_next, sixNextL_ofSure] at h", last_excl="  have uC : UpBelow gC := Rc.grow.up uS")
sn = "\n".join(sn)
sn = rep(sn, "  have Rc := ihc (jmp0 gQ.bo)", "  have Tc := tgc (jmp0 gQ.bo)")
hb = seg(sv, "  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))] []) = false := by",
         last_incl="    have := Ra.size; have := Rb.size; simp only [lazyMax]; omega")
sn = sn + "\n" + "\n".join(hb) + """
  have hc9 : g9.cond = gC.cond := (kc_copyL _ _).keep _ _ _ (hrest hbig)
  exact (CondTag.of_eq cnF).trans ((CondTag.mono (fun t ht => Sfx.tail ht) Tb).trans
    ((CondTag.mono (fun t ht => Sfx.tail ht) Ta).trans ((CondTag.of_eq cS).trans (Tc.trans (CondTag.of_eq hc9)))))"""

# --- `%6` for `%done` and `%pick` (from `sixP_okV`) -------------------------
fu = lines("CompFragU.lean")
sp = seg(fu, "  intro region g0 g4 nex hg hj hcount b0 d0 hu hcl0 hcb0 h", last_excl="  have u3 : UpBelow g3 := Rc.grow.up uG")
sp = "\n".join(sp)
sp = rep(sp, "  have Rc := ihc (jmp0 g2.bo)", "  have Tc := tgc (jmp0 g2.bo)")
sp = rep(sp, "  have Rb := ihb hg hj (by omega) b0 d0 hu hcl0 hcb0 h1\n",
         "  have Rb := ihb hg hj (by omega) b0 d0 hu hcl0 hcb0 h1\n"
         "  have Tb := tgb hg hj (by omega) b0 d0 hu hcl0 hcb0 h1\n")
sp = rep(sp, "  have Ra := iha hg (hj.mono b01) (by omega) b1 d1 u1 cl1 cb1 h2\n",
         "  have Ra := iha hg (hj.mono b01) (by omega) b1 d1 u1 cl1 cb1 h2\n"
         "  have Ta := tga hg (hj.mono b01) (by omega) b1 d1 u1 cl1 cb1 h2\n")
sp = sp + """
  have hc4 : g4.cond = g3.cond := (kc_copyL _ _).keep _ _ _ (hrest hbig)
  exact Tb.trans (Ta.trans ((CondTag.of_eq (sixGenL_cond g2 x0.th x1.th region)).trans
    (Tc.trans (CondTag.of_eq hc4))))"""

# --- cons under a fork-free `%next` (from `consNV_body`) --------------------
cn = lines("CompConsNV.lean")
cb = seg(cn, "  obtain ⟨⟨hed', tel', o⟩, g2x, h2, h⟩ := bind_some h",
         last_excl="  have AS : AboveIn (fun r => HoonMap.get g0.cond r = Option.none) g0.bo g2 :=")
cb = "\n".join(cb)
rq = seg(cn, "  have Rq := hq (sur := tel) (th := jmp0 g0.bo) ⟨b0, by simp only [jmp0]; omega⟩ rfl ⟨Dt, lt2' _ Mt⟩ CS.2",
         last_incl="    (by omega) (by omega) d2 u2 cl2 cb2 (nk2 _ Mt) h3")
rp = seg(cn, "  have Rp := hp (sur := hed) (th := nex2.th) ⟨Rq.lo, Rq.hi⟩ (nextArgs_nil Rq.ent rfl)",
         last_incl="    (fun y hy => by rw [Rq.cfr.get_lt (lt2' _ Mh y hy)]; exact nk2 _ Mh y hy) h4")
tq = rep("\n".join(rq), "  have Rq := hq", "  have Tq := tq")
tp = rep("\n".join(rp), "  have Rp := hp", "  have Tp := tp")
cb = cb + "\n" + tq + "\n" + tp + """
  have c4 : g1.cond = g4.cond := (kc_copyL _ _).keep _ _ _ hcp
  exact (CondTag.of_eq c2).trans (Tq.trans (Tp.trans (CondTag.of_eq c4)))"""

# --- cons for `%pick` (from `runOKV_consP`) ---------------------------------
cv = lines("CompConsV.lean")
ip = find(cv, "theorem runOKV_consP (lib : Lib) {p q : Nomm} (hp : OKNV (S := S) (Map := Map) lib p)")
cp = seg(cv, "  intro region g0 g1 nex _ hj hcount b0 d0 hu hcl0 hcb h",
         last_excl="  refine RunOKGV.toV (goal := CGoal.pick z o) trivial (binaryGV_ok (goal := CGoal.pick z o) (pureEval_cons p q)",
         start=ip)
cp = "\n".join(cp)
rq2 = seg(cv, "  have Rq := hq (sur := Sure.bunt) (th := jmp0 g0.bo) ⟨b0, by simp [jmp0, emitted_bo]⟩ rfl",
          last_incl="    ⟨trivial, fun r hr => hr.elim⟩ trivial (by omega) (by simp [emitted_bo]) d2 u2 cl2 cb2 (fun r hr => hr.elim) h3",
          start=ip)
rp2 = seg(cv, "  have Rp := hp (sur := Sure.bunt) (th := nex2.th) ⟨Rq.lo, Rq.hi⟩ (nextArgs_nil Rq.ent rfl)",
          last_incl="    (Rq.ext.2.2.1.trans d2) (Rq.grow.up u2) (cl2.growU Rq.grow) (Rq.cfr.below cb2) (fun r hr => hr.elim) h4",
          start=ip)
tq2 = rep("\n".join(rq2), "  have Rq := hq", "  have Tq := tq")
tp2 = rep("\n".join(rp2), "  have Rp := hp", "  have Tp := tp")
cp = cp + "\n" + tq2 + "\n" + tp2 + """
  have c1 : g1.cond = g4.cond := (kc_copyL _ _).keep _ _ _ h
  exact (CondTag.of_eq (emitted_cond g0 _)).trans (Tq.trans (Tp.trans (CondTag.of_eq c1)))"""

HEAD = '''import lemmas.Ska.CompSixNextV
import lemmas.Ska.CompConsV

/-!
# The clean and tag clauses of `%6` and cons with proxy runs

README Gaps 12.2 (tenth session).  Generated by `tools/gen/fraguj.py` from
the openings of `runX_clean` (`cleanA_six`, `cleanA_cons`), `sixNext_okNV`
(`sixNext_tagNV`), `sixP_okV` (`sixP_tagV`), `consNV_body` (`cons_tagNV`)
and `runOKV_consP` (`cons_tagP`): each opening establishes the hypotheses at
the start of every part, then the parts' clauses are chained.  Do not edit by
hand: change the script and rerun it.

* `TagV goal nm`: with the hypotheses of `OKV`, every key a run adds to
  `cond` has a tag with its region as a suffix (`TagNV` for `%done` and
  `%pick`).
* `cleanA_six`, `cleanA_cons`: `CleanA` of `%6` from `CleanA` of its test,
  of cons from `CleanA` of its parts.
* `sixNext_tagNV`, `sixP_tagV`: the tag clauses of `%6` from those of its
  parts; the branches under `%next` run in the region `rid :: region`, which
  `Sfx.tail` weakens to `region`, `+fork-sure`, `+sect` and `+copy` keep
  `cond`.
* `cons_tagNV`, `cons_tagP`: the tag clauses of cons; `+split`, the
  `[%bom ~]` block and `+copy` keep `cond`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The tag clause of a run for `%done` or `%pick`**, with the hypotheses
of `OKV`: every key it adds to `cond` has a tag with its region as a
suffix. -/
abbrev TagV (goal : CGoal S) (nm : Nomm) : Prop :=
  ∀ {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}, NotNext goal → GJ g0.bo goal →
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runL nm (CGoal.toL goal) region g0 = some (nex, g1) → CondTag region g0.cond g1.cond

/-- **`CleanA` of `%6` from `CleanA` of its test** (the case of
`runX_clean`): the sure need of the result is that of the test's run for
`%pick`, copied. -/
theorem cleanA_six {c : Nomm} (a b : Nomm) (hcp : c.pure = true) (ihc : CleanA S Map c) :
    CleanA S Map (Nomm.n6 c a b) := by
'''

CONS_CLEAN = '''
/-- **`CleanA` of cons from `CleanA` of its parts** (the case of
`runX_clean`). -/
theorem cleanA_cons {p q : Nomm} (hpp : p.pure = true) (hqp : q.pure = true) (ihp : CleanA S Map p)
    (ihq : CleanA S Map q) : CleanA S Map (Nomm.cons p q) := by
'''

SIXN = '''
/-- **The tag clause of `%6` under a fork-free `%next`**: `+fork-sure` keeps
`cond`, the branches run in the region `gF.id :: region` (`TagNV`, weakened
by `Sfx.tail`), `+sect` keeps `cond` (`sect_specV`), the test runs for
`%pick` in `region` (`TagV`), `+copy` keeps `cond`. -/
theorem sixNext_tagNV (lib : Lib) {c a b : Nomm} (hcp : c.pure = true)
    (tgc : ∀ z o : Jmp, z.args = [] → o.args = [] → TagV (Map := Map) (CGoal.pick z o : CGoal S) c)
    (iha : OKNV (S := S) (Map := Map) lib a) (ihb : OKNV (S := S) (Map := Map) lib b)
    (tga : TagNV (S := S) (Map := Map) a) (tgb : TagNV (S := S) (Map := Map) b) :
    TagNV (S := S) (Map := Map) (Nomm.n6 c a b) := by
  intro sur th region g0 g9 nex hj hth hok hcl hcount b0 d0 hu hcl0 hcb0 hkg h
'''

SIXP = '''
/-- **The tag clause of `%6` for `%done` or `%pick`**: the branches and the
test run in `region`, the yes and no blocks and `+copy` keep `cond`. -/
theorem sixP_tagV (lib : Lib) {goal : CGoal S} {c a b : Nomm} (hcp : c.pure = true)
    (tgc : ∀ z o : Jmp, z.args = [] → o.args = [] → TagV (Map := Map) (CGoal.pick z o : CGoal S) c)
    (iha : OKV (Map := Map) lib goal a) (ihb : OKV (Map := Map) lib goal b)
    (tga : TagV (Map := Map) goal a) (tgb : TagV (Map := Map) goal b) :
    TagV (Map := Map) goal (Nomm.n6 c a b) := by
'''

CONSN = '''
/-- **The tag clause of cons under a fork-free `%next`**: `+split` keeps
`cond`, the tail and the head run in `region`, `+copy` keeps `cond`. -/
theorem cons_tagNV (lib : Lib) {p q : Nomm} (hp : OKNV (S := S) (Map := Map) lib p)
    (hq : OKNV (S := S) (Map := Map) lib q) (tp : TagNV (S := S) (Map := Map) p)
    (tq : TagNV (S := S) (Map := Map) q) (hpp : p.pure = true) (hqp : q.pure = true) :
    TagNV (S := S) (Map := Map) (Nomm.cons p q) := by
  intro sur th region g0 g1 nex hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  rw [runL_cons_next] at h
'''

CONSP = '''
/-- **The tag clause of cons for `%pick`**: the `[%bom ~]` block keeps
`cond`, the tail and the head run in `region`, `+copy` keeps `cond`. -/
theorem cons_tagP (lib : Lib) {p q : Nomm} (hp : OKNV (S := S) (Map := Map) lib p)
    (hq : OKNV (S := S) (Map := Map) lib q) (tp : TagNV (S := S) (Map := Map) p)
    (tq : TagNV (S := S) (Map := Map) q) (hpp : p.pure = true) (z o : Jmp) :
    TagV (Map := Map) (CGoal.pick z o : CGoal S) (Nomm.cons p q) := by
'''

TAIL = '''
end Comp
end SkaModel
end Formalization
'''

out = (HEAD + "\n".join(six_clean) + "\n" + CONS_CLEAN + "\n".join(cons_clean) + "\n" + SIXN + sn + "\n" + SIXP + sp +
       "\n" + CONSN + cb + "\n" + CONSP + cp + "\n" + TAIL)
(SKA / "CompFragUJGen.lean").write_text(out)
print("wrote", SKA / "CompFragUJGen.lean", len(out.split("\n")), "lines")
