#!/usr/bin/env python3
"""Write the copy of `knowGo_sound` (lemmas/Ska/KnowSound.lean, from `IHK` to
`know_annot_of_implies`, without `slot1_eq`) for lemmas/Ska/AnnotSKnow.lean
(track Q, InvBSR, README Gaps 27): the input `Annot lib code` becomes
`AnnotK lib code`, the output `Annot lib code'` becomes `Glue.AnnotS lib code'`,
and the direct case gets the return of the folded formula part
(`knowGo_detK_safe`, `ret_of_detK`).  Also `Glue.AnnotS.mono` and
`Glue.AnnotS.mono_code` from `Annot.mono` (FolLoopFacts.lean) and
`Annot.mono_code` (MemoPoke.lean).  The originals are never edited.
Usage: annots_know.py FORMALIZATION_DIR OUT (the text goes after the marker
`-- BEGIN annots_know.py` of AnnotSKnow.lean)."""
import re, sys
root = sys.argv[1]
out = sys.argv[2]

def cut(path, start, end):
    s = open(root + '/' + path).read()
    i = s.index(start)
    j = s.index(end, i)
    return s[i:j]

def rep(s, old, new, n):
    c = s.count(old)
    assert c == n, (old, c, n)
    return s.replace(old, new)

def rer(s, pat, new, n):
    c = len(re.findall(pat, s))
    assert c == n, (pat, c, n)
    return re.sub(pat, new, s)

# --- AnnotS.mono and AnnotS.mono_code ---
mono = cut('lemmas/Ska/FolLoopFacts.lean', '/-- **`Annot` holds on fewer subjects.** -/',
           '/-! ## The cases of the `?+` -/')
mono = rep(mono, 'Annot.', 'Glue.AnnotS.', 29)
mono = rep(mono, 'Annot lib code', 'Glue.AnnotS lib code', 2)
mono = rep(mono, '`Annot`', '`AnnotS`', 1)
mono = rep(mono, 'theorem Glue.AnnotS.mono', 'theorem _root_.Formalization.SkaModel.Glue.AnnotS.mono', 1)
mono = rep(mono, """  | direct _ _ hc hy hg ih1 ih2 =>
    intro Q hQ
    exact Glue.AnnotS.direct (ih1 hQ) (ih2 hQ) hc (fun x gul y hx => hy x gul y (hQ x hx))
      (fun x gul g hx => hg x gul g (hQ x hx))
""", """  | direct _ _ hc hy hg hr ih1 ih2 =>
    intro Q hQ
    exact Glue.AnnotS.direct (ih1 hQ) (ih2 hQ) hc (fun x gul y hx => hy x gul y (hQ x hx))
      (fun x gul g hx => hg x gul g (hQ x hx)) (fun hk hs x gul hx => hr hk hs x gul (hQ x hx))
""", 1)
mc = cut('lemmas/Ska/MemoPoke.lean', 'theorem Annot.mono_code', '/-- `+memo-final-entry`')
mc = rep(mc, 'Annot.', 'Glue.AnnotS.', 29)
mc = rep(mc, 'Annot lib code', 'Glue.AnnotS lib code', 2)
mc = rep(mc, 'theorem Glue.AnnotS.mono_code', 'theorem _root_.Formalization.SkaModel.Glue.AnnotS.mono_code', 1)
mc = rep(mc, """  | direct _ _ hb hl hf ih1 ih2 =>
    obtain ⟨nb', hb'⟩ := hcc _ _ hb
    exact Glue.AnnotS.direct ih1 ih2 hb' hl hf
""", """  | direct _ _ hb hl hf hr ih1 ih2 =>
    obtain ⟨nb', hb'⟩ := hcc _ _ hb
    exact Glue.AnnotS.direct ih1 ih2 hb' hl hf hr
""", 1)
mc = "/-- `AnnotS` needs of the code table only that the bells it calls have a\nnomm. -/\n" + mc

# --- the copy of knowGo_sound ---
a = cut('lemmas/Ska/KnowSound.lean', '/-- The statement of `knowGo_sound` for one annotation',
        'theorem slot1_eq')
b = cut('lemmas/Ska/KnowSound.lean', '/-- `%8` and the forms `+know` gives it',
        '/-- `DatOK` from the provenance invariant')
s = a + b
s = rep(s, 'KnowOK lib code code\'', 'KnowOKK lib code code\'', 1)
s = rep(s, '(`KnowOK`)', '(`KnowOKK`)', 1)
s = rer(s, r'\bIHK\b', 'IHKK', 9)
s = rer(s, r'\bseven_core\b', 'seven_coreK', 4)
s = rer(s, r'\bn8_core\b', 'n8_coreK', 3)
s = rer(s, r'\bknowGo_sound\b', 'knowGo_soundK', 3)
s = rer(s, r'\bknow_annot\b', 'know_annotK', 2)
s = rer(s, r'\bknow_annot_of_implies\b', 'know_annot_of_impliesK', 1)
s = rep(s, "Annot lib code'", "Glue.AnnotS lib code'", 14)
s = rep(s, 'Annot lib code ', 'AnnotK lib code ', 8)
s = rer(s, r'\bAnnot\.', 'Glue.AnnotS.', 42)
# the one input `Annot.n0` (the pushed `[0 1]` of `%8`)
s = rep(s, 'n8_coreK hc hA1 Glue.AnnotS.n0', 'n8_coreK hc hA1 AnnotK.n0', 1)
s = rer(s, r'\bannot_safe_total\b', 'annot_safe_totalS', 4)
s = rer(s, r'\bannot_lit\b', 'annot_litS', 15)
s = rer(s, r'\blit_val hc\b', 'lit_valK hc', 10)
s = rer(s, r'\bsafe_known hc\b', 'safe_knownK hc', 6)
s = rer(s, r'\bnomm_mink hc (hA\w*)\b', r'nomm_minkK hc \1', 4)
s = rer(s, r'\bmink_nomm hc (hA\w*)\b', r'mink_nommK hc \1', 4)
s = rer(s, r'\bknowGo_n0\b', 'knowGo_n0K', 3)
# the direct case: the return of the folded formula part
s = rep(s, '  | direct hA1 hA2 hcode hy hg ih1 ih2 =>', '  | direct hA1 hA2 hcode hy hg hdk ih1 ih2 =>', 1)
s = rep(s, """      (fun x gul g hx hm => (hg x gul g (hQP x hx) hm).trans hvf.symm), ?_⟩""",
"""      (fun x gul g hx hm => (hg x gul g (hQP x hx) hm).trans hvf.symm)
      (fun hk hsf => ret_of_detK K2.1.toAnnot hsf (DetK.mono hQP _ (knowGo_detK_safe (hdk hk) hf hsf))), ?_⟩""", 1)
open(out, 'w').write(mono + mc + s)
