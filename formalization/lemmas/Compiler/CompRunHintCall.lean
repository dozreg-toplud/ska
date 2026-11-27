import lemmas.Compiler.CompRunHintDir

/-!
# The run link with hints inside direct calls: the class `HintOkC` (README Gaps 25)

`HintOkC` is `HintOk` (`CompRunHintClass.lean`) with the parts `p`, `q` of a
direct call `[2 p q [~ b ~]]` in the class themselves, so with hints, in
place of hint-free `DirOk` parts.  `HintCallsC` asks `CallOk` of every direct
call, also those under a hint (`HintCalls` stopped at a direct call with
`DirCalls`, which does not look under a hint), and `HintSoundC` is
`HintSound` with the parts of a direct call.

* `crx_iff_mmH`, `partLMH_of_partH`: `PartH` at `XM E msup` is what the
  generated direct call (`CompRunHintDir.lean`, `tools/gen/runhintdir.py`)
  takes of a part.
* **`comp_run_hintC`**: every member whose direct calls meet `CallOk` and
  whose kept hints meet `SoundAt` is a `PartH` at `XM E msup`; the call case
  by `comp_run_n2_directMMH` / `res_n2_directMonoH`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSectionVars false

variable {ctx : Noun}

theorem crx_iff_mmH {E : GenRest → Prop} {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {msup : Option Nomm}
    {n : Nomm} {goal : CGoalL CSet} {region : List Nat} {g : Gen (TreapMap mugF)} :
    CompRunAtX (runLCH env snd true msup) ctx (XM E msup) n goal region g ↔
      CompRunAtMMH env snd msup ctx E n goal region g := by
  constructor
  · intro h x hx hE
    exact h x _ _ hx ⟨hE, rfl, rfl⟩
  · rintro h x mono sup hx ⟨hE, rfl, rfl⟩
    exact h x hx hE

/-- `PartH` at `XM E msup` gives `PartLMH`. -/
theorem partLMH_of_partH {E : GenRest → Prop} {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {msup : Option Nomm}
    {n : Nomm} {region : List Nat} (P : PartH env snd msup ctx (XM E msup) n region) :
    PartLMH env snd msup ctx E n region :=
  ⟨fun goal g hi => crx_iff_mmH.1 (P.link goal g hi), P.res⟩

/-- **The class with hints inside direct calls**: `HintOk` whose direct
calls (no memo key) have parts in the class. -/
def HintOkC : Nomm → Bool
  | Nomm.cons p q => HintOkC p && HintOkC q
  | Nomm.n0 _ => true
  | Nomm.n1 _ => true
  | Nomm.n2 p q Option.none => HintOkC p && HintOkC q
  | Nomm.n2 p q (some (_, Option.none)) => HintOkC p && HintOkC q
  | Nomm.n3 p => HintOkC p
  | Nomm.n4 p => HintOkC p
  | Nomm.n5 p q => HintOkC p && HintOkC q
  | Nomm.n6 p q r => HintOkC p && HintOkC q && HintOkC r
  | Nomm.n7 p q => HintOkC p && HintOkC q
  | Nomm.n10 a v q => (a != 0 && HintOkC v) && HintOkC q
  | Nomm.n11s _ q _ => HintOkC q
  | Nomm.n11d _ h q _ => HintOkC h && HintOkC q
  | _ => false

/-- **`CallOk` of every direct call**, also under a hint, each at the
`msup` its run gets. -/
def HintCallsC (env : CallEnv) (cod ctx : Noun) (E : GenRest → Prop) : Option Nomm → Nomm → Prop
  | ms, Nomm.cons p q => HintCallsC env cod ctx E ms p ∧ HintCallsC env cod ctx E ms q
  | ms, Nomm.n2 p q Option.none => HintCallsC env cod ctx E ms p ∧ HintCallsC env cod ctx E ms q
  | ms, Nomm.n2 p q (some (b, _)) =>
      CallOk env cod ctx E ms p q b ∧ HintCallsC env cod ctx E ms p ∧ HintCallsC env cod ctx E ms q
  | ms, Nomm.n3 p => HintCallsC env cod ctx E ms p
  | ms, Nomm.n4 p => HintCallsC env cod ctx E ms p
  | ms, Nomm.n5 p q => HintCallsC env cod ctx E ms p ∧ HintCallsC env cod ctx E ms q
  | ms, Nomm.n6 p q r =>
      HintCallsC env cod ctx E ms p ∧ HintCallsC env cod ctx E ms q ∧ HintCallsC env cod ctx E ms r
  | ms, Nomm.n7 p q => HintCallsC env cod ctx E ms p ∧ HintCallsC env cod ctx E (some p) q
  | ms, Nomm.n10 _ v q => HintCallsC env cod ctx E ms v ∧ HintCallsC env cod ctx E ms q
  | ms, Nomm.n11s _ q _ => HintCallsC env cod ctx E ms q
  | ms, Nomm.n11d _ h q _ => HintCallsC env cod ctx E ms h ∧ HintCallsC env cod ctx E ms q
  | _, _ => True

/-- **`+sound` returns `snd` on the formula under every kept hint**
(`SoundAt`, read by `+past-if`). -/
def HintSoundC (ctx : Noun) (snd : Nomm → NeedOrd → Bool) : Nomm → Prop
  | Nomm.cons p q => HintSoundC ctx snd p ∧ HintSoundC ctx snd q
  | Nomm.n2 p q _ => HintSoundC ctx snd p ∧ HintSoundC ctx snd q
  | Nomm.n3 p => HintSoundC ctx snd p
  | Nomm.n4 p => HintSoundC ctx snd p
  | Nomm.n5 p q => HintSoundC ctx snd p ∧ HintSoundC ctx snd q
  | Nomm.n6 p q r => HintSoundC ctx snd p ∧ HintSoundC ctx snd q ∧ HintSoundC ctx snd r
  | Nomm.n7 p q => HintSoundC ctx snd p ∧ HintSoundC ctx snd q
  | Nomm.n10 _ v q => HintSoundC ctx snd v ∧ HintSoundC ctx snd q
  | Nomm.n11s tag q _ => (hintStatic tag = true → SoundAt ctx snd q) ∧ HintSoundC ctx snd q
  | Nomm.n11d tag h q _ => (hintDynamic tag = true → SoundAt ctx snd q) ∧ HintSoundC ctx snd h ∧ HintSoundC ctx snd q
  | _ => True

theorem callCode_of_hintC {env : CallEnv} {cod : Noun} {E : GenRest → Prop} :
    ∀ (n : Nomm), HintOkC n = true → ∀ (ms : Option Nomm), HintCallsC env cod ctx E ms n → CallCode cod env n
  | Nomm.cons p q, h, ms, hd => by
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hd; simp only [CallCode]
    exact ⟨callCode_of_hintC p h.1 ms hd.1, callCode_of_hintC q h.2 ms hd.2⟩
  | Nomm.n0 _, _, _, _ => trivial
  | Nomm.n1 _, _, _, _ => trivial
  | Nomm.n2 p q Option.none, h, ms, hd => by
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hd; simp only [CallCode]
    exact ⟨trivial, callCode_of_hintC p h.1 ms hd.1, callCode_of_hintC q h.2 ms hd.2⟩
  | Nomm.n2 p q (some (b, Option.none)), h, ms, hd => by
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hd; simp only [CallCode]
    exact ⟨⟨hd.1.1, hd.1.2.1⟩, callCode_of_hintC p h.1 ms hd.2.1, callCode_of_hintC q h.2 ms hd.2.2⟩
  | Nomm.n2 _ _ (some (_, some _)), h, _, _ => by simp [HintOkC] at h
  | Nomm.n3 p, h, ms, hd => by
    simp only [HintOkC] at h; simp only [HintCallsC] at hd; simp only [CallCode]; exact callCode_of_hintC p h ms hd
  | Nomm.n4 p, h, ms, hd => by
    simp only [HintOkC] at h; simp only [HintCallsC] at hd; simp only [CallCode]; exact callCode_of_hintC p h ms hd
  | Nomm.n5 p q, h, ms, hd => by
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hd; simp only [CallCode]
    exact ⟨callCode_of_hintC p h.1 ms hd.1, callCode_of_hintC q h.2 ms hd.2⟩
  | Nomm.n7 p q, h, ms, hd => by
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hd; simp only [CallCode]
    exact ⟨callCode_of_hintC p h.1 ms hd.1, callCode_of_hintC q h.2 (some p) hd.2⟩
  | Nomm.n10 a v q, h, ms, hd => by
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hd; simp only [CallCode]
    exact ⟨callCode_of_hintC v h.1.2 ms hd.1, callCode_of_hintC q h.2 ms hd.2⟩
  | Nomm.n6 p q r, h, ms, hd => by
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hd; simp only [CallCode]
    exact ⟨callCode_of_hintC p h.1.1 ms hd.1, callCode_of_hintC q h.1.2 ms hd.2.1, callCode_of_hintC r h.2 ms hd.2.2⟩
  | Nomm.n11s _ q _, h, ms, hd => by
    simp only [HintOkC] at h; simp only [HintCallsC] at hd; simp only [CallCode]
    exact callCode_of_hintC q h ms hd
  | Nomm.n11d _ h q _, hn, ms, hd => by
    simp only [HintOkC, Bool.and_eq_true] at hn; simp only [HintCallsC] at hd; simp only [CallCode]
    exact ⟨callCode_of_hintC h hn.1 ms hd.1, callCode_of_hintC q hn.2 ms hd.2⟩
  | Nomm.n12 _ _, h, _, _ => by simp [HintOkC] at h
  | Nomm.mean _ _ _ _ _, h, _, _ => by simp [HintOkC] at h

theorem noAx0_of_hintC : ∀ (n : Nomm), HintOkC n = true → Bake.NoAx0 n
  | Nomm.cons p q, h => by
    simp only [HintOkC, Bool.and_eq_true] at h; exact ⟨noAx0_of_hintC p h.1, noAx0_of_hintC q h.2⟩
  | Nomm.n0 _, _ => trivial
  | Nomm.n1 _, _ => trivial
  | Nomm.n2 p q Option.none, h => by
    simp only [HintOkC, Bool.and_eq_true] at h; exact ⟨noAx0_of_hintC p h.1, noAx0_of_hintC q h.2⟩
  | Nomm.n2 p q (some (b, Option.none)), h => by
    simp only [HintOkC, Bool.and_eq_true] at h; exact ⟨noAx0_of_hintC p h.1, noAx0_of_hintC q h.2⟩
  | Nomm.n2 _ _ (some (_, some _)), h => by simp [HintOkC] at h
  | Nomm.n3 p, h => by simp only [HintOkC] at h; exact noAx0_of_hintC p h
  | Nomm.n4 p, h => by simp only [HintOkC] at h; exact noAx0_of_hintC p h
  | Nomm.n5 p q, h => by
    simp only [HintOkC, Bool.and_eq_true] at h; exact ⟨noAx0_of_hintC p h.1, noAx0_of_hintC q h.2⟩
  | Nomm.n6 p q r, h => by
    simp only [HintOkC, Bool.and_eq_true] at h
    exact ⟨noAx0_of_hintC p h.1.1, noAx0_of_hintC q h.1.2, noAx0_of_hintC r h.2⟩
  | Nomm.n7 p q, h => by
    simp only [HintOkC, Bool.and_eq_true] at h; exact ⟨noAx0_of_hintC p h.1, noAx0_of_hintC q h.2⟩
  | Nomm.n10 a v q, h => by
    simp only [HintOkC, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact ⟨h.1.1, noAx0_of_hintC v h.1.2, noAx0_of_hintC q h.2⟩
  | Nomm.n11s _ q _, h => by
    simp only [HintOkC] at h; exact noAx0_of_hintC q h
  | Nomm.n11d _ h q _, hn => by
    simp only [HintOkC, Bool.and_eq_true] at hn; exact ⟨noAx0_of_hintC h hn.1, noAx0_of_hintC q hn.2⟩
  | Nomm.n12 _ _, h => by simp [HintOkC] at h
  | Nomm.mean _ _ _ _ _, h => by simp [HintOkC] at h

/-- **The run link with hints inside direct calls, at `mono` `&`**: every
nomm of `HintOkC` whose direct calls meet `CallOk` (also under hints) and
whose kept hints meet `SoundAt` is a `PartH` at `XM E msup` (link against
`runLCH env snd true msup` on every goal with `GInv`, result, `+past`),
every `snd`, `msup` and region. -/
theorem comp_run_hintC (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (E : GenRest → Prop) :
    ∀ (n : Nomm), HintOkC n = true → ∀ (msup : Option Nomm) (region : List Nat),
      HintCallsC env cod ctx E msup n → HintSoundC ctx snd n → PartH env snd msup ctx (XM E msup) n region
  | Nomm.cons p q, h, msup, region, hd, hs => by
    have hc := callCode_of_hintC (ctx := ctx) _ h msup hd
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hd
    simp only [HintSoundC] at hs
    have P := comp_run_hintC h7 hcode env snd E p h.1 msup region hd.1 hs.1
    have Q := comp_run_hintC h7 hcode env snd E q h.2 msup region hd.2 hs.2
    exact ⟨fun goal g hi => comp_run_consLRH h7 hcode env msup p q P Q goal g hi, res_consRH P.res Q.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n0 ax, h, msup, region, hd, hs =>
    partH_of_partR rfl (comp_run_dir h7 hcode env E (Nomm.n0 ax) rfl msup region trivial)
  | Nomm.n1 k, h, msup, region, hd, hs =>
    partH_of_partR rfl (comp_run_dir h7 hcode env E (Nomm.n1 k) rfl msup region trivial)
  | Nomm.n2 p q Option.none, h, msup, region, hd, hs => by
    have hc := callCode_of_hintC (ctx := ctx) _ h msup hd
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hd
    simp only [HintSoundC] at hs
    have P := comp_run_hintC h7 hcode env snd E p h.1 msup region hd.1 hs.1
    have Q := comp_run_hintC h7 hcode env snd E q h.2 msup region hd.2 hs.2
    exact ⟨fun goal g hi => comp_run_n2LRH h7 hcode env msup p q P Q goal g hi, res_n2RH P.res Q.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n2 p q (some (b, Option.none)), h, msup, region, hd, hs => by
    have hc := callCode_of_hintC (ctx := ctx) _ h msup hd
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hd
    simp only [HintSoundC] at hs
    obtain ⟨⟨hcd, -, hri, nb, hnb, hE⟩, hdp, hdq⟩ := hd
    have P := comp_run_hintC h7 hcode env snd E p h.1 msup region hdp hs.1
    have Q := comp_run_hintC h7 hcode env snd E q h.2 msup region hdq hs.2
    exact ⟨fun goal g hi => crx_iff_mmH.2 (comp_run_n2_directMMH h7 hcode env msup p q P.past
        (partLMH_of_partH P) (partLMH_of_partH Q) b hcd nb hE hri hnb goal g hi),
      res_n2_directMonoH P.res Q.res hri hnb, pastAt_code h7 hcode env hc⟩
  | Nomm.n2 _ _ (some (_, some _)), h, _, _, _, hs => by simp [HintOkC] at h
  | Nomm.n3 p, h, msup, region, hd, hs => by
    have hc := callCode_of_hintC (ctx := ctx) _ h msup hd
    simp only [HintOkC] at h; simp only [HintCallsC] at hd
    simp only [HintSoundC] at hs
    have P := comp_run_hintC h7 hcode env snd E p h msup region hd hs
    exact ⟨fun goal g hi => comp_run_n3LRH h7 env msup p goal region g hi P.link, res_n3RH P.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n4 p, h, msup, region, hd, hs => by
    have hc := callCode_of_hintC (ctx := ctx) _ h msup hd
    simp only [HintOkC] at h; simp only [HintCallsC] at hd
    simp only [HintSoundC] at hs
    have P := comp_run_hintC h7 hcode env snd E p h msup region hd hs
    exact ⟨fun goal g hi => comp_run_n4LRH h7 env msup p goal region g hi P.link, res_n4RH P.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n5 p q, h, msup, region, hd, hs => by
    have hc := callCode_of_hintC (ctx := ctx) _ h msup hd
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hd
    simp only [HintSoundC] at hs
    have P := comp_run_hintC h7 hcode env snd E p h.1 msup region hd.1 hs.1
    have Q := comp_run_hintC h7 hcode env snd E q h.2 msup region hd.2 hs.2
    exact ⟨fun goal g hi => comp_run_n5LRH h7 hcode env msup p q P Q goal g hi, res_n5RH P.res Q.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n7 p q, h, msup, region, hd, hs => by
    have hc := callCode_of_hintC (ctx := ctx) _ h msup hd
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hd
    simp only [HintSoundC] at hs
    have P := comp_run_hintC h7 hcode env snd E p h.1 msup region hd.1 hs.1
    have Q := comp_run_hintC h7 hcode env snd E q h.2 (some p) region hd.2 hs.2
    exact ⟨fun goal g hi => comp_run_n7CRH env msup p q goal region g (Q.link goal g hi)
        (fun x mono sup hX => ⟨hX.1, hX.2.1, rfl⟩)
        (fun nex g1 e => P.link nex.goal g1 (Q.res goal g g1 nex hi e).2.2.1),
      res_n7RH Q.res P.res, pastAt_code h7 hcode env hc⟩
  | Nomm.n10 a v q, h, msup, region, hd, hs => by
    have hc := callCode_of_hintC (ctx := ctx) _ h msup hd
    simp only [HintOkC, Bool.and_eq_true, bne_iff_ne, ne_eq] at h; simp only [HintCallsC] at hd
    simp only [HintSoundC] at hs
    have V := comp_run_hintC h7 hcode env snd E v h.1.2 msup region hd.1 hs.1
    have Q := comp_run_hintC h7 hcode env snd E q h.2 msup region hd.2 hs.2
    exact ⟨fun goal g hi => comp_run_n10LRH h7 hcode env msup a h.1.1 v q V Q goal g hi,
      res_n10RH h.1.1 V.res Q.res, pastAt_code h7 hcode env hc⟩
  | Nomm.n6 p q r, h, msup, region, hd, hs => by
    have hc := callCode_of_hintC (ctx := ctx) _ h msup hd
    have ha := noAx0_of_hintC _ h
    simp only [HintOkC, Bool.and_eq_true] at h; simp only [HintCallsC] at hd; simp only [Bake.NoAx0] at ha
    have hc' := hc
    simp only [CallCode] at hc'
    simp only [HintSoundC] at hs
    have P := comp_run_hintC h7 hcode env snd E p h.1.1 msup region hd.1 hs.1
    have Q := fun rg => comp_run_hintC h7 hcode env snd E q h.1.2 msup rg hd.2.1 hs.2.1
    have R := fun rg => comp_run_hintC h7 hcode env snd E r h.2 msup rg hd.2.2 hs.2.2
    exact ⟨fun goal g hi => comp_run_n6_allRH h7 hcode env msup p q r region (sixRH_of h7 hcode P hc'.1)
        (sixRH_of h7 hcode (Q region) hc'.2.1) (sixRH_of h7 hcode (R region) hc'.2.2)
        (fun rid => sixRH_of h7 hcode (Q (rid :: region)) hc'.2.1)
        (fun rid => sixRH_of h7 hcode (R (rid :: region)) hc'.2.2) ha.2.1 ha.2.2 goal g hi,
      res_n6_allRH P.res (Q region).res (R region).res (fun rid => (Q (rid :: region)).res)
        (fun rid => (R (rid :: region)).res) ha.2.1 ha.2.2,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n11s tag q body, h, msup, region, hd, hs => by
    have hc := callCode_of_hintC (ctx := ctx) _ h msup hd
    simp only [HintOkC] at h; simp only [HintCallsC] at hd; simp only [HintSoundC] at hs
    have Q := comp_run_hintC h7 hcode env snd E q h msup region hd hs.2
    cases ht : hintStatic tag with
    | false => exact partH_n11s ht body Q (pastAt_code h7 hcode env hc)
    | true => exact partH_n11s_kept h7 ht body Q (hs.1 ht) (pastAt_code h7 hcode env hc)
  | Nomm.n11d tag h q body, hn, msup, region, hd, hs => by
    have hc := callCode_of_hintC (ctx := ctx) _ hn msup hd
    simp only [HintOkC, Bool.and_eq_true] at hn; simp only [HintCallsC] at hd; simp only [HintSoundC] at hs
    have H := comp_run_hintC h7 hcode env snd E h hn.1 msup region hd.1 hs.2.1
    have Q := comp_run_hintC h7 hcode env snd E q hn.2 msup region hd.2 hs.2.2
    cases ht : hintDynamic tag with
    | false => exact partH_n11d_nd h7 ht body Q H (pastAt_code h7 hcode env hc)
    | true => exact partH_n11d_kept h7 ht body Q H (hs.1 ht) (pastAt_code h7 hcode env hc)
  | Nomm.n12 _ _, h, _, _, _, hs => by simp [HintOkC] at h
  | Nomm.mean _ _ _ _ _, h, _, _, _, hs => by simp [HintOkC] at h

end Compiler
end Formalization
