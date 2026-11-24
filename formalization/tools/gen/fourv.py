#!/usr/bin/env python3
"""Generate lemmas/Ska/CompFourV.lean: `[4 p]` and `[3 p]` with an operand
whose runs may make proxies, from the text of `unaryN_ok`, `runOKN_n4`,
`runOKP_n4p`, `runOKN_n3_of_none`, `runOKN_n3`, `runOKP_n3p` (CompFragM.lean),
`runOKP_n4`, `runOKP_n3` (CompSevenN.lean) and the cases `four`, `three` of
`runX_clean` (CompFragX.lean).  Run from formalization/:
python3 tools/gen/fourv.py.  Every extraction and replacement asserts its
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


fm = lines("CompFragM.lean")
sn = lines("CompSevenN.lean")
fx = lines("CompFragX.lean")

P0 = "(fun r => HoonMap.get g0.cond r = Option.none)"
POLE = ("(fun x hx => by\n"
        "        simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx\n"
        "        rcases hx with rfl | rfl\n")
CB = "(CondFresh.below (condFresh_of_eq (g0 := g0) (by romega) rfl) hcb)"

# --- unaryNV_ok ---------------------------------------------------------
U = thm(fm, "unaryN_ok")
U = rep(U, "theorem unaryN_ok", "theorem unaryNV_ok")
U = rep(U, "(hp : RunOKN (Map := Map) lib p (lazyReg a) (jmp0 o) g' g1 nexp)",
        "(hp : RunOKNV (Map := Map) lib p (lazyReg a) (jmp0 o) g' g1 nexp)")
U = rep(U, "    (hsz : sixCount nm = sixCount p)\n",
        "    (hsz : sixCount nm = sixCount p)\n"
        "    (hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k) →\n"
        "      ∀ k, g0.bo ≤ k → k < g'.bo → (HoonMap.get g'.blocks k).map (unproxyBlob cf) = HoonMap.get g'.blocks k)\n")
U = rep(U, "    RunOKN (Map := Map) lib nm sur th g0 g1 nexp := by\n"
           "  refine ⟨hpre.trans hp.ext, hgr.trans hp.grow, hp.cnd.trans hcnd, hp.lo, hp.hi, ?_, fun r hr => ?_, hp.dist,\n"
           "    fun e he => ?_, fun e he => ?_, hp.nodup, by rw [hsz]; exact hp.size, fun s hs => ?_, ?_⟩\n",
        "    RunOKNV (Map := Map) lib nm sur th g0 g1 nexp := by\n"
        "  refine ⟨hpre.trans hp.ext, hgr.trans hp.grow, (condFresh_of_eq hpre.1 hcnd).trans hp.cfr, hp.lo, hp.hi, ?_,\n"
        "    fun r hr => ?_, hp.dist, fun e he => ?_, fun e he => ?_, hp.nodup, by rw [hsz]; exact hp.size, fun s hs => ?_,\n"
        "    hp.ncond, hp.econd, ?_⟩\n")
U = rep(U, "  · intro c ned σ O st t gul s0 s ag hned regs hh hn\n"
           "    have agP : AgreeP lib O c gul st t ned g' g1 nexp.laz s0 s :=\n",
        "  · intro cf hcf c ned σ O st t gul s0 s ag hned regs hh hn\n"
        "    have agP : AgreeU lib O c gul st t cf ned g' g1 nexp.laz s0 s :=\n")
U = rep(U, "    have Sp := hp.sem c ned σ O st t gul s0 s agP hned regs hh hn\n",
        "    have Sp := hp.sem cf hcf c ned σ O st t gul s0 s agP hned regs hh hn\n"
        "    have hcf0 : ∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k := fun k hk =>\n"
        "      (hcf k (Nat.lt_of_lt_of_le hk hp.ext.1)).trans ((hp.cfr.get_lt hk).trans (by rw [hcnd]))\n")
U = rep(U, "      · exact hp.ext.2.2.2 o' h1\n",
        "      · rw [hp.ext.2.2.2 o' h1]; exact hfix cf hcf0 o' h0 h1\n")

# --- [4 p] for %done ------------------------------------------------------
D4 = thm(sn, "runOKP_n4")
D4 = rep(D4, "theorem runOKP_n4 (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p) {region : List Nat} {g0 g1 : Gen Map}\n"
             "    {nex : NextL S} (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)\n"
             "    (h : runL (Nomm.n4 p) (CGoal.toL (CGoal.done : CGoal S)) region g0 = some (nex, g1)) :\n"
             "    RunOKP (Map := Map) lib (Nomm.n4 p) CGoal.done g0 g1 nex := by\n",
         "theorem runOKV_n4D (lib : Lib) {p : Nomm} (hp : OKNV (S := S) (Map := Map) lib p) :\n"
         "    OKV (Map := Map) lib (CGoal.done : CGoal S) (Nomm.n4 p) := by\n"
         "  intro region g0 g1 nex _ _ hcount b0 d0 hu hcl0 hcb h\n"
         "  simp only [sixCount] at hcount\n")
D4 = rep(D4, "    (((grow_reg g0 _).trans (grow_emit (jumpsBelow_nil rfl _))).toU hu |>.up hu) h\n",
         "    (((grow_reg g0 _).trans (grow_emit (jumpsBelow_nil rfl _))).toU hu |>.up hu)\n"
         "    (hcl0.growU (((grow_reg g0 _).trans (grow_emit (jumpsBelow_nil rfl _))).toU hu)) " + CB + "\n"
         "    (fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; exact condBelow_none hcb (by romega)) h\n")
D4 = rep(D4, "  refine unaryP_ok (pureEval_n4 p)", "  refine unaryGV_ok (goal := CGoal.done) trivial (pureEval_n4 p)")
D4 = rep(D4, "(fresh_emitted (by simpa using d0) rfl rfl) Rp rfl ?_\n",
         "(fresh_emitted (by simpa using d0) rfl rfl) Rp rfl\n"
         "    (fix_of_keeps (gs := g0) rfl ((keepsA_reg _ g0 _ (by romega)).trans (keepsA_emitted d0 (blobIn_one\n"
         "      " + POLE + "        <;> exact condBelow_none hcb (by romega)) (condBelow_none hcb (by romega)))))\n"
         "      ((keeps_reg g0 _ (by romega)).trans (keeps_emitted d0 (blobIn_one\n"
         "      " + POLE + "        <;> romega) (by simp only [FinIn]; romega)))))\n"
         "    ?_\n")
D4 = rep(D4, "  rw [goJ_jmp0 _ _ _ _ hb]\n", "  show goJ lib O c gul st regs t _ = _\n  rw [goJ_jmp0 _ _ _ _ hb]\n")

# --- [4 p] for %pick ------------------------------------------------------
P4 = thm(fm, "runOKP_n4p")
P4 = rep(P4, "theorem runOKP_n4p (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p) {z o : Jmp} {region : List Nat}\n"
             "    {g0 g1 : Gen Map} {nex : NextL S} (hj : GJ g0.bo (CGoal.pick z o : CGoal S)) (hcount : sixCount p ≤ 255)\n"
             "    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)\n"
             "    (h : runL (Nomm.n4 p) (CGoal.toL (CGoal.pick z o : CGoal S)) region g0 = some (nex, g1)) :\n"
             "    RunOKP (Map := Map) lib (Nomm.n4 p) (CGoal.pick z o) g0 g1 nex := by\n",
         "theorem runOKV_n4P (lib : Lib) {p : Nomm} (hp : OKNV (S := S) (Map := Map) lib p) (z o : Jmp)\n"
         "    (hz : z.args = []) (hzo : o.args = []) : OKV (Map := Map) lib (CGoal.pick z o : CGoal S) (Nomm.n4 p) := by\n"
         "  intro region g0 g1 nex _ hj hcount b0 d0 hu hcl0 hcb h\n"
         "  simp only [sixCount] at hcount\n")
P4 = rep(P4, "    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d0) ((G.toU hu).up hu) h\n",
         "    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d0) ((G.toU hu).up hu)\n"
         "    (hcl0.growU (G.toU hu)) " + CB + "\n"
         "    (fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; exact condBelow_none hcb (by romega)) h\n")
P4_OPEN = P4.split("  refine unaryG_ok (goal := CGoal.pick z o) trivial (pureEval_n4 p)\n")[0]
P4 = rep(P4, "  refine unaryG_ok (goal := CGoal.pick z o) trivial (pureEval_n4 p)",
         "  refine unaryGV_ok (goal := CGoal.pick z o) trivial (pureEval_n4 p)")
P4 = rep(P4, "(fresh_emitted (by simpa using d0) rfl rfl) Rp rfl ?_\n",
         "(fresh_emitted (by simpa using d0) rfl rfl) Rp rfl\n"
         "    (fix_of_keeps (gs := g0) rfl ((keepsA_reg _ g0 _ (by romega)).trans (keepsA_emitted d0 (blobIn_one\n"
         "      " + POLE + "        <;> exact condBelow_none hcb (by romega))\n"
         "      ⟨condBelow_none hcb (by romega), jmpIn_nil hz, jmpIn_nil hzo⟩)))\n"
         "      ((keeps_reg g0 _ (by romega)).trans (keeps_emitted d0 (blobIn_one\n"
         "      " + POLE + "        <;> romega) ⟨by romega, jmpIn_nil hz, jmpIn_nil hzo⟩))))\n"
         "    ?_\n")

# --- [4 p] under %next ----------------------------------------------------
N4 = thm(fm, "runOKN_n4")
N4 = rep(N4, "theorem runOKN_n4 (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p) {sur : Sure S} {th : Jmp}\n"
             "    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (hj : GJ g0.bo (CGoal.next sur th))\n"
             "    (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)\n"
             "    (h : runL (Nomm.n4 p) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1)) :\n"
             "    RunOKN (Map := Map) lib (Nomm.n4 p) sur th g0 g1 nex := by\n",
         "theorem runOKNV_n4 (lib : Lib) {p : Nomm} (hp : OKNV (S := S) (Map := Map) lib p) :\n"
         "    OKNV (S := S) (Map := Map) lib (Nomm.n4 p) := by\n"
         "  intro sur th region g0 g1 nex hj _ hok _ hcount b0 d0 hu hcl0 hcb hkg h\n"
         "  simp only [sixCount] at hcount\n")
N4 = rep(N4, "  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h\n",
         "  have AB : (KeepsA " + P0 + " g0 g3 ∧ HoonMap.get g0.cond pro = Option.none) ∧\n"
         "      (Keeps g0 g3 ∧ pro < g3.re) := by\n"
         "    obtain ⟨ka, ra⟩ := keepsA_collapseLazyAtom (P := " + P0 + ") (nex := ⟨sur, th⟩)\n"
         "      d0 hkg (fun r hr => condBelow_none hcb hr) h2\n"
         "    obtain ⟨kb, rb⟩ := keeps_collapseLazyAtom (nex := ⟨sur, th⟩) d0 (fun r hr => hok.2 r hr) h2\n"
         "    cases a with\n"
         "    | some x =>\n"
         "      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3\n"
         "      obtain ⟨rfl, rfl⟩ := h3\n"
         "      exact ⟨⟨ka, ra _ _ rfl⟩, ⟨kb, rb _ _ rfl⟩⟩\n"
         "    | none =>\n"
         "      simp only [bind_apply, re_apply, Option.bind_some, ea, if_true, pure_apply, Option.some.injEq,\n"
         "        Prod.mk.injEq] at h3\n"
         "      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h3\n"
         "      exact ⟨⟨ka.trans (keepsA_reg _ _ _ (Nat.le_succ _)), condBelow_none hcb ka.le⟩,\n"
         "        ⟨kb.trans (keeps_reg _ _ (Nat.le_succ _)), Nat.lt_succ_self _⟩⟩\n"
         "  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h\n")
N4 = rep(N4, "    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d3) ((G.toU hu).up hu) h\n",
         "    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d3) ((G.toU hu).up hu)\n"
         "    (hcl0.growU (G.toU hu))\n"
         "    (CondFresh.below (condFresh_of_eq (g0 := g0) (Nat.le_trans AB.2.1.le (Nat.le_succ _)) (P.2.1.trans c2)) hcb)\n"
         "    (fun r hr => by\n"
         "      simp only [lazyReg, NMem] at hr; subst hr\n"
         "      show HoonMap.get g3.cond _ = _\n"
         "      rw [P.2.1, c2]; exact condBelow_none hcb AB.2.1.le) h\n")
N4_OPEN = N4.split("  refine unaryN_ok (pureEval_n4 p)")[0]
N4 = rep(N4, "  refine unaryN_ok (pureEval_n4 p)", "  refine unaryNV_ok (pureEval_n4 p)")
N4 = rep(N4, "    (fresh_emitted (by simpa using d3) rfl rfl) Rp rfl ?_\n",
         "    (fresh_emitted (by simpa using d3) rfl rfl) Rp rfl\n"
         "    (fix_of_keeps (gs := g0) rfl (AB.1.1.trans ((keepsA_reg _ g3 _ (Nat.le_succ _)).trans (keepsA_emitted d3\n"
         "      (blobIn_one " + POLE + "        · exact condBelow_none hcb AB.2.1.le\n"
         "        · exact AB.1.2) (jmpIn_jmp0 _ _)))))\n"
         "      (AB.2.1.trans ((keeps_reg g3 _ (Nat.le_succ _)).trans (keeps_emitted d3\n"
         "      (blobIn_one " + POLE + "        · exact Nat.lt_succ_self _\n"
         "        · exact Nat.lt_succ_of_lt AB.2.2) (jmpIn_jmp0 _ _))))))\n"
         "    ?_\n")

# --- the tag clauses of [4 p] ---------------------------------------------
TN4 = N4_OPEN
TN4 = rep(TN4, "theorem runOKNV_n4 (lib : Lib) {p : Nomm} (hp : OKNV (S := S) (Map := Map) lib p) :\n"
               "    OKNV (S := S) (Map := Map) lib (Nomm.n4 p) := by\n",
          "theorem four_tagNV (lib : Lib) {p : Nomm} (tp : TagNV (S := S) (Map := Map) p) :\n"
          "    TagNV (S := S) (Map := Map) (Nomm.n4 p) := by\n")
TN4 = rep(TN4, "  have Rp := hp", "  have Tp := tp")
TN4 += "  exact (CondTag.of_eq (P.2.1.trans c2)).trans Tp\n"
TP4 = P4_OPEN
TP4 = rep(TP4, "theorem runOKV_n4P (lib : Lib) {p : Nomm} (hp : OKNV (S := S) (Map := Map) lib p) (z o : Jmp)\n"
               "    (hz : z.args = []) (hzo : o.args = []) : OKV (Map := Map) lib (CGoal.pick z o : CGoal S) (Nomm.n4 p) := by\n",
          "theorem four_tagP (lib : Lib) {p : Nomm} (tp : TagNV (S := S) (Map := Map) p) (z o : Jmp) :\n"
          "    TagV (Map := Map) (CGoal.pick z o : CGoal S) (Nomm.n4 p) := by\n")
TP4 = rep(TP4, "  have Rp := hp", "  have Tp := tp")
TP4 += "  exact Tp\n"

# --- [3 p] for %done ------------------------------------------------------
D3 = thm(sn, "runOKP_n3")
D3 = rep(D3, "theorem runOKP_n3 (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p) {region : List Nat}\n"
             "    {g0 g1 : Gen Map} {nex : NextL S} (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false)\n"
             "    (hu : UpBelow g0) (h : runL (Nomm.n3 p) (CGoal.toL (CGoal.done : CGoal S)) region g0 = some (nex, g1)) :\n"
             "    RunOKP (Map := Map) lib (Nomm.n3 p) CGoal.done g0 g1 nex := by\n",
         "theorem runOKV_n3D (lib : Lib) {p : Nomm} (hp : OKNV (S := S) (Map := Map) lib p) :\n"
         "    OKV (Map := Map) lib (CGoal.done : CGoal S) (Nomm.n3 p) := by\n"
         "  intro region g0 g1 nex _ _ hcount b0 d0 hu hcl0 hcb h\n"
         "  simp only [sixCount] at hcount\n")
D3 = rep(D3, "    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d2) ((G.toU hu).up hu) h\n",
         "    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d2) ((G.toU hu).up hu)\n"
         "    (hcl0.growU (G.toU hu))\n"
         "    (CondFresh.below (condFresh_of_eq (g0 := g0) (Nat.le_trans D.1 (Nat.le_succ _))\n"
         "      ((kc_doneBlocks.keep g0 _ g2 h2))) hcb)\n"
         "    (fun r hr => by\n"
         "      simp only [lazyReg, NMem] at hr; subst hr\n"
         "      show HoonMap.get g2.cond _ = _\n"
         "      rw [kc_doneBlocks.keep g0 _ g2 h2]; exact condBelow_none hcb D.1) h\n")
D3 = rep(D3, "  refine unaryP_ok (pureEval_n3 p)", "  refine unaryGV_ok (goal := CGoal.done) trivial (pureEval_n3 p)")
D3 = rep(D3, "    ⟨by omega, by simp [emitted_re]⟩ (by simp [emitted_bo]) (fresh_emitted (by simpa using d2) rfl rfl) Rp rfl ?_\n",
         "    ⟨by omega, by simp [emitted_re]⟩ (by simp [emitted_bo]) (fresh_emitted (by simpa using d2) rfl rfl) Rp rfl\n"
         "    (fix_of_keeps (gs := g0) rfl ((keepsA_doneBlocks d0 (fun r hr => condBelow_none hcb hr) h2).trans\n"
         "      ((keepsA_reg _ g2 _ (Nat.le_succ _)).trans (keepsA_emitted d2\n"
         "        (blobIn_fin ⟨condBelow_none hcb D.1, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩))))\n"
         "      ((keeps_doneBlocks d0 h2).trans ((keeps_reg g2 _ (Nat.le_succ _)).trans (keeps_emitted d2\n"
         "        (blobIn_fin ⟨Nat.lt_succ_self _, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)))))\n"
         "    ?_\n")
D3 = rep(D3, "  refine hj.trans ?_\n", "  show goJ lib O c gul st regs t _ = _\n  refine hj.trans ?_\n")

# --- [3 p] for %pick ------------------------------------------------------
P3 = thm(fm, "runOKP_n3p")
P3 = rep(P3, "theorem runOKP_n3p (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p) {z o : Jmp} {region : List Nat}\n"
             "    {g0 g1 : Gen Map} {nex : NextL S} (hj : GJ g0.bo (CGoal.pick z o : CGoal S)) (hcount : sixCount p ≤ 255)\n"
             "    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)\n"
             "    (h : runL (Nomm.n3 p) (CGoal.toL (CGoal.pick z o : CGoal S)) region g0 = some (nex, g1)) :\n"
             "    RunOKP (Map := Map) lib (Nomm.n3 p) (CGoal.pick z o) g0 g1 nex := by\n",
         "theorem runOKV_n3P (lib : Lib) {p : Nomm} (hp : OKNV (S := S) (Map := Map) lib p) (z o : Jmp)\n"
         "    (hz : z.args = []) (hzo : o.args = []) : OKV (Map := Map) lib (CGoal.pick z o : CGoal S) (Nomm.n3 p) := by\n"
         "  intro region g0 g1 nex _ hj hcount b0 d0 hu hcl0 hcb h\n"
         "  simp only [sixCount] at hcount\n")
P3 = rep(P3, "    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d0) ((G.toU hu).up hu) h\n",
         "    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d0) ((G.toU hu).up hu)\n"
         "    (hcl0.growU (G.toU hu)) " + CB + "\n"
         "    (fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; exact condBelow_none hcb (by romega)) h\n")
P3_OPEN = P3.split("  refine unaryG_ok (goal := CGoal.pick z o) trivial (pureEval_n3 p)")[0]
P3 = rep(P3, "  refine unaryG_ok (goal := CGoal.pick z o) trivial (pureEval_n3 p)",
         "  refine unaryGV_ok (goal := CGoal.pick z o) trivial (pureEval_n3 p)")
P3 = rep(P3, "    Rp rfl ?_\n",
         "    Rp rfl\n"
         "    (fix_of_keeps (gs := g0) rfl ((keepsA_reg _ g0 _ (Nat.le_succ _)).trans (keepsA_emitted d0\n"
         "        (blobIn_fin ⟨condBelow_none hcb (Nat.le_refl _), jmpIn_nil hz, jmpIn_nil hzo⟩)))\n"
         "      ((keeps_reg g0 _ (Nat.le_succ _)).trans (keeps_emitted d0\n"
         "        (blobIn_fin ⟨Nat.lt_succ_self _, jmpIn_nil hz, jmpIn_nil hzo⟩))))\n"
         "    ?_\n")

# --- [3 p] under %next ----------------------------------------------------
N0 = thm(fm, "runOKN_n3_of_none")
N0 = rep(N0, "theorem runOKN_n3_of_none", "theorem runOKNV_n3_of_none")
N0 = rep(N0, "(hp : RunOKN (Map := Map) lib p sur th g0 g1 nex) : RunOKN (Map := Map) lib (Nomm.n3 p) sur th g0 g1 nex := by",
         "(hp : RunOKNV (Map := Map) lib p sur th g0 g1 nex) : RunOKNV (Map := Map) lib (Nomm.n3 p) sur th g0 g1 nex := by")
N0 = rep(N0, "  refine ⟨hp.ext, hp.grow, hp.cnd, hp.lo,", "  refine ⟨hp.ext, hp.grow, hp.cfr, hp.lo,")
N0 = rep(N0, "by simp only [sixCount]; exact hp.size, fun s hs => ?_, ?_⟩",
         "by simp only [sixCount]; exact hp.size, fun s hs => ?_, hp.ncond, hp.econd, ?_⟩")
N0 = rep(N0, "  · intro c ned σ O st t gul s0 s ag hned regs hh hn'\n    have H := hp.sem c ned",
         "  · intro cf hcf c ned σ O st t gul s0 s ag hned regs hh hn'\n    have H := hp.sem cf hcf c ned")

N3 = thm(fm, "runOKN_n3")
N3 = rep(N3, "theorem runOKN_n3 (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p) {sur : Sure S} {th : Jmp}\n"
             "    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = [])\n"
             "    (hok : GoalOK g0 (CGoal.next sur th)) (hcl : Clean sur.ned)\n"
             "    (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)\n"
             "    (h : runL (Nomm.n3 p) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1)) :\n"
             "    RunOKN (Map := Map) lib (Nomm.n3 p) sur th g0 g1 nex := by\n",
         "theorem runOKNV_n3 (lib : Lib) {p : Nomm} (hp : OKNV (S := S) (Map := Map) lib p) :\n"
         "    OKNV (S := S) (Map := Map) lib (Nomm.n3 p) := by\n"
         "  intro sur th region g0 g1 nex hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h\n"
         "  simp only [sixCount] at hcount\n")
N3 = rep(N3, "    exact runOKN_n3_of_none en'.1 en'.2 (hp hj hth hok hcl hcount b0 d0 hu h)\n",
         "    exact runOKNV_n3_of_none en'.1 en'.2 (hp hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h)\n")
N3 = rep(N3, "  obtain ⟨hmr, _, hs⟩ := hsome r o rfl\n",
         "  obtain ⟨hmr, _, hs⟩ := hsome r o rfl\n"
         "  obtain ⟨ka, ra⟩ := keepsA_collapseLazyAtom (P := " + P0 + ") (nex := ⟨sur, th⟩)\n"
         "    d0 hkg (fun r hr => condBelow_none hcb hr) h2\n"
         "  have kb := (keeps_collapseLazyAtom (nex := ⟨sur, th⟩) d0 (fun r hr => hok.2 r hr) h2).1\n")
N3 = rep(N3, "    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d3) ((G.toU hu).up hu) h\n",
         "    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d3) ((G.toU hu).up hu)\n"
         "    (hcl0.growU (G.toU hu))\n"
         "    (CondFresh.below (condFresh_of_eq (g0 := g0) (Nat.le_trans (Nat.le_trans E2.1 E3.1) (Nat.le_succ _))\n"
         "      (c3.trans c2)) hcb)\n"
         "    (fun r hr => by\n"
         "      simp only [lazyReg, NMem] at hr; subst hr\n"
         "      show HoonMap.get g3.cond _ = _\n"
         "      rw [c3, c2]; exact condBelow_none hcb (Nat.le_trans E2.1 E3.1)) h\n")
N3_OPEN = N3.split("  refine unaryN_ok (pureEval_n3 p)")[0]
N3 = rep(N3, "  refine unaryN_ok (pureEval_n3 p)", "  refine unaryNV_ok (pureEval_n3 p)")
N3 = rep(N3, "    (fresh_emitted (by simpa using d3) rfl rfl) Rp rfl ?_\n",
         "    (fresh_emitted (by simpa using d3) rfl rfl) Rp rfl\n"
         "    (fix_of_keeps (gs := g0) rfl (ka.trans ((keepsA_forl d2 (ra r o rfl) (fun r' hr' => condBelow_none hcb\n"
         "        (Nat.le_trans E2.1 hr')) h3).trans ((keepsA_reg _ g3 _ (Nat.le_succ _)).trans (keepsA_emitted d3\n"
         "        (blobIn_fin ⟨condBelow_none hcb (Nat.le_trans E2.1 E3.1), jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)))))\n"
         "      (kb.trans ((keeps_forl d2 hr h3).trans ((keeps_reg g3 _ (Nat.le_succ _)).trans (keeps_emitted d3\n"
         "        (blobIn_fin ⟨Nat.lt_succ_self _, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩))))))\n"
         "    ?_\n")

# --- the tag clauses of [3 p] ---------------------------------------------
TN3 = N3_OPEN
TN3 = rep(TN3, "theorem runOKNV_n3 (lib : Lib) {p : Nomm} (hp : OKNV (S := S) (Map := Map) lib p) :\n"
               "    OKNV (S := S) (Map := Map) lib (Nomm.n3 p) := by\n",
          "theorem three_tagNV (lib : Lib) {p : Nomm} (tp : TagNV (S := S) (Map := Map) p) :\n"
          "    TagNV (S := S) (Map := Map) (Nomm.n3 p) := by\n")
TN3 = rep(TN3, "    exact runOKNV_n3_of_none en'.1 en'.2 (hp hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h)\n",
          "    exact tp hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h\n")
TN3 = rep(TN3, "  have Rp := hp", "  have Tp := tp")
TN3 += "  exact (CondTag.of_eq (c3.trans c2)).trans Tp\n"
TP3 = P3_OPEN
TP3 = rep(TP3, "theorem runOKV_n3P (lib : Lib) {p : Nomm} (hp : OKNV (S := S) (Map := Map) lib p) (z o : Jmp)\n"
               "    (hz : z.args = []) (hzo : o.args = []) : OKV (Map := Map) lib (CGoal.pick z o : CGoal S) (Nomm.n3 p) := by\n",
          "theorem three_tagP (lib : Lib) {p : Nomm} (tp : TagNV (S := S) (Map := Map) p) (z o : Jmp) :\n"
          "    TagV (Map := Map) (CGoal.pick z o : CGoal S) (Nomm.n3 p) := by\n")
TP3 = rep(TP3, "  have Rp := hp", "  have Tp := tp")
TP3 += "  exact Tp\n"

# --- clean ----------------------------------------------------------------
def case(name, nxt):
    i = find(fx, "  | " + name + " _ ih =>", find(fx, "theorem runX_clean {nm : Nomm} (hf : FragX (S := S) nm) : CleanA S Map nm := by"))
    j = find(fx, nxt, i)
    return "\n".join(dedent(fx[i + 1:j], 2)).rstrip("\n") + "\n"

C4 = case("four", "  | three _ ih =>")
C3 = case("three", "  | seven hq _ ih =>")

HEAD = '''import lemmas.Ska.CompFragUJGen

/-!
# `[4 p]` and `[3 p]` with an operand whose runs make proxies

README Gaps 12.2 (eleventh session).  Generated by `tools/gen/fourv.py` from
`unaryN_ok`, `runOKN_n4`, `runOKP_n4p`, `runOKN_n3_of_none`, `runOKN_n3`,
`runOKP_n3p` (`CompFragM.lean`), `runOKP_n4`, `runOKP_n3` (`CompSevenN.lean`)
and the cases `four`, `three` of `runX_clean`; do not edit by hand.  The
operand runs under the fork-free `%next` of one fresh register (`OKNV`).  The
blocks before it (`+collapse-lazy-atom`, `+forl`, the loobean blocks, the
block of the increment or the cell test) mention the goal's registers and
fresh ones, no key of a later `cond` when the goal's registers are no keys
(`hkg`), so unproxying leaves them alone (`fix_of_keeps`).

* `fix_of_keeps`: the `hfix` of `unaryGV_ok` from `KeepsA` and `Keeps` of the
  blocks before the operand.
* `unaryNV_ok`: `unaryN_ok` with a `RunOKNV` operand, giving `RunOKNV`.
* `runOKV_n4D`, `runOKV_n4P`, `runOKNV_n4`: `[4 p]` for `%done`, `%pick`
  and under `%next`; `four_tagNV`, `four_tagP`: its tag clauses;
  `cleanA_four`.
* `runOKV_n3D`, `runOKV_n3P`, `runOKNV_n3_of_none`, `runOKNV_n3`: `[3 p]`
  likewise; `three_tagNV`, `three_tagP`; `cleanA_three`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- `omega` after reducing the projections of the states. -/
local macro "romega" : tactic =>
  `(tactic| first | omega | (simp only [emitted_re, emitted_bo] at *; omega) | (dsimp only at *; omega))

/-- **Unproxying leaves the blocks before a part alone** when they mention
only registers below the part's start (`Keeps`) and no key of the first
state's `cond` (`KeepsA`), against every `cf` that agrees with that `cond`
below the part's start. -/
theorem fix_of_keeps {g0 gs g' : Gen Map} (hbo : gs.bo = g0.bo)
    (KA : KeepsA (fun r => HoonMap.get g0.cond r = Option.none) gs g') (KB : Keeps gs g') :
    ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < g'.bo → (HoonMap.get g'.blocks k).map (unproxyBlob cf) = HoonMap.get g'.blocks k := by
  intro cf hcf k h0 h1
  have AS := KA.ab _ (aboveIn_start _ gs)
  have BS := KB.bel _ (belowIn_start gs)
  rw [hbo] at AS BS
  have u0 : ∀ x, x < g'.re → unproxy cf x = unproxy g0.cond x := unproxy_agree (fun k hk => hcf k hk)
  have u1 : ∀ x, HoonMap.get g0.cond x = Option.none → unproxy g0.cond x = id x := fun x hx => unproxy_none hx
  cases hgb : HoonMap.get g'.blocks k with
  | none => rfl
  | some b =>
    simp only [Option.map_some]
    rw [unproxyBlob, renBlob_congr u0 (BS k b h0 h1 hgb), renBlob_congr u1 (AS k b h0 h1 hgb), renBlob_id]

/-- **A unary case for a fork-free `%next` whose operand may make proxies**
(`unaryN_ok` with a `RunOKNV` operand); the blocks before the operand are
left alone by unproxying by hypothesis (`hfix`). -/
'''

TAIL = '''
end Comp
end SkaModel
end Formalization
'''

out = (HEAD + U
       + "\n/-- **`[4 p]` for `%done`** with an `OKNV` operand. -/\n" + D4
       + "\n/-- **`[4 p]` for `%pick`** with an `OKNV` operand. -/\n" + P4
       + "\n/-- **`[4 p]` under a fork-free `%next`** with an `OKNV` operand. -/\n" + N4
       + "\n/-- **The tag clause of `[4 p]` under `%next`**: `+collapse-lazy-atom`, `re` and\nthe block keep `cond`. -/\n" + TN4
       + "\n/-- **The tag clause of `[4 p]` for `%pick`.** -/\n" + TP4
       + "\n/-- **`CleanA` of `[4 p]`** (the case of `runX_clean`). -/\n"
       + "theorem cleanA_four {p : Nomm} (ih : CleanA S Map p) : CleanA S Map (Nomm.n4 p) := by\n" + C4
       + "\n/-- **`[3 p]` for `%done`** with an `OKNV` operand. -/\n" + D3
       + "\n/-- **`[3 p]` for `%pick`** with an `OKNV` operand. -/\n" + P3
       + "\n/-- `[3 p]` under a `%next` that asks nothing of the product, with a\n`RunOKNV` operand. -/\n" + N0
       + "\n/-- **`[3 p]` under a fork-free `%next`** with an `OKNV` operand. -/\n" + N3
       + "\n/-- **The tag clause of `[3 p]` under `%next`.** -/\n" + TN3
       + "\n/-- **The tag clause of `[3 p]` for `%pick`.** -/\n" + TP3
       + "\n/-- **`CleanA` of `[3 p]`** (the case of `runX_clean`). -/\n"
       + "theorem cleanA_three {p : Nomm} (ih : CleanA S Map p) : CleanA S Map (Nomm.n3 p) := by\n" + C3
       + TAIL)
(SKA / "CompFourV.lean").write_text(out)
print("wrote", SKA / "CompFourV.lean", len(out.split("\n")), "lines")
