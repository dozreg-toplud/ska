import lemmas.Compiler.CompRunHintD

/-!
# The run link with hints: the class `HintOk` (README Gaps 25)

`HintOk` is `DirOk` (`CompRunRClass.lean`) with the static hint whose tag is
not `hint-static` (`n11s`, every tag but `%bout` and `%xray`: `%spot`,
`%fast`, `%memo`, an unknown one) and the dynamic hint whose tag is not
`hint-dynamic` (`n11d`: `%memo` with an unsafe clue, `%fast`, an unknown
tag; `partH_n11d_nd`, `CompRunHintD.lean`) nested in any way, and every direct call
hint-free.  **`comp_run_hint`**: every member whose direct calls meet
`CallOk` is a `PartH` at `XM E msup` (the link against `runLCH env snd true
msup` on every goal with `GInv`, its result, `+past`), by induction: the
hint-free constructors by the copies of `CompRunHint*.lean`
(`tools/gen/runhintr.py`), the hint by `partH_n11s`, a direct call (hint-free)
by `comp_run_dir` through `runLCH_eq` (`partH_of_partR`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- **The class with hints**: `DirOk` with the dropped static tag, nested in
any way; a direct call is hint-free. -/
def HintOk : Nomm → Bool
  | Nomm.cons p q => HintOk p && HintOk q
  | Nomm.n0 _ => true
  | Nomm.n1 _ => true
  | Nomm.n2 p q Option.none => HintOk p && HintOk q
  | Nomm.n2 p q (some (b, Option.none)) =>
      DirOk (Nomm.n2 p q (some (b, Option.none))) && (Nomm.n2 p q (some (b, Option.none))).noHint
  | Nomm.n3 p => HintOk p
  | Nomm.n4 p => HintOk p
  | Nomm.n5 p q => HintOk p && HintOk q
  | Nomm.n6 p q r => HintOk p && HintOk q && HintOk r
  | Nomm.n7 p q => HintOk p && HintOk q
  | Nomm.n10 a v q => (a != 0 && HintOk v) && HintOk q
  | Nomm.n11s tag q _ => !hintStatic tag && HintOk q
  | Nomm.n11d tag h q _ => (!hintDynamic tag && HintOk h) && HintOk q
  | _ => false

/-- **`CallOk` of every direct call** (`DirCalls` at a call), each at the
`msup` its run gets. -/
def HintCalls (env : CallEnv) (cod ctx : Noun) (E : GenRest → Prop) : Option Nomm → Nomm → Prop
  | ms, Nomm.cons p q => HintCalls env cod ctx E ms p ∧ HintCalls env cod ctx E ms q
  | ms, Nomm.n2 p q Option.none => HintCalls env cod ctx E ms p ∧ HintCalls env cod ctx E ms q
  | ms, Nomm.n2 p q (some i) => DirCalls env cod ctx E ms (Nomm.n2 p q (some i))
  | ms, Nomm.n3 p => HintCalls env cod ctx E ms p
  | ms, Nomm.n4 p => HintCalls env cod ctx E ms p
  | ms, Nomm.n5 p q => HintCalls env cod ctx E ms p ∧ HintCalls env cod ctx E ms q
  | ms, Nomm.n6 p q r =>
      HintCalls env cod ctx E ms p ∧ HintCalls env cod ctx E ms q ∧ HintCalls env cod ctx E ms r
  | ms, Nomm.n7 p q => HintCalls env cod ctx E ms p ∧ HintCalls env cod ctx E (some p) q
  | ms, Nomm.n10 _ v q => HintCalls env cod ctx E ms v ∧ HintCalls env cod ctx E ms q
  | ms, Nomm.n11s _ q _ => HintCalls env cod ctx E ms q
  | ms, Nomm.n11d _ h q _ => HintCalls env cod ctx E ms h ∧ HintCalls env cod ctx E ms q
  | _, _ => True

theorem callCode_of_hint {env : CallEnv} {cod : Noun} {E : GenRest → Prop} :
    ∀ (n : Nomm), HintOk n = true → ∀ (ms : Option Nomm), HintCalls env cod ctx E ms n → CallCode cod env n
  | Nomm.cons p q, h, ms, hd => by
    simp only [HintOk, Bool.and_eq_true] at h; simp only [HintCalls] at hd; simp only [CallCode]
    exact ⟨callCode_of_hint p h.1 ms hd.1, callCode_of_hint q h.2 ms hd.2⟩
  | Nomm.n0 _, _, _, _ => trivial
  | Nomm.n1 _, _, _, _ => trivial
  | Nomm.n2 p q Option.none, h, ms, hd => by
    simp only [HintOk, Bool.and_eq_true] at h; simp only [HintCalls] at hd; simp only [CallCode]
    exact ⟨trivial, callCode_of_hint p h.1 ms hd.1, callCode_of_hint q h.2 ms hd.2⟩
  | Nomm.n2 p q (some (b, Option.none)), h, ms, hd => by
    simp only [HintOk, Bool.and_eq_true] at h; simp only [HintCalls] at hd
    exact callCode_of_dir _ h.1 ms hd
  | Nomm.n2 _ _ (some (_, some _)), h, _, _ => by simp [HintOk] at h
  | Nomm.n3 p, h, ms, hd => by
    simp only [HintOk] at h; simp only [HintCalls] at hd; simp only [CallCode]; exact callCode_of_hint p h ms hd
  | Nomm.n4 p, h, ms, hd => by
    simp only [HintOk] at h; simp only [HintCalls] at hd; simp only [CallCode]; exact callCode_of_hint p h ms hd
  | Nomm.n5 p q, h, ms, hd => by
    simp only [HintOk, Bool.and_eq_true] at h; simp only [HintCalls] at hd; simp only [CallCode]
    exact ⟨callCode_of_hint p h.1 ms hd.1, callCode_of_hint q h.2 ms hd.2⟩
  | Nomm.n7 p q, h, ms, hd => by
    simp only [HintOk, Bool.and_eq_true] at h; simp only [HintCalls] at hd; simp only [CallCode]
    exact ⟨callCode_of_hint p h.1 ms hd.1, callCode_of_hint q h.2 (some p) hd.2⟩
  | Nomm.n10 a v q, h, ms, hd => by
    simp only [HintOk, Bool.and_eq_true] at h; simp only [HintCalls] at hd; simp only [CallCode]
    exact ⟨callCode_of_hint v h.1.2 ms hd.1, callCode_of_hint q h.2 ms hd.2⟩
  | Nomm.n6 p q r, h, ms, hd => by
    simp only [HintOk, Bool.and_eq_true] at h; simp only [HintCalls] at hd; simp only [CallCode]
    exact ⟨callCode_of_hint p h.1.1 ms hd.1, callCode_of_hint q h.1.2 ms hd.2.1, callCode_of_hint r h.2 ms hd.2.2⟩
  | Nomm.n11s _ q _, h, ms, hd => by
    simp only [HintOk, Bool.and_eq_true] at h; simp only [HintCalls] at hd; simp only [CallCode]
    exact callCode_of_hint q h.2 ms hd
  | Nomm.n11d _ h q _, hn, ms, hd => by
    simp only [HintOk, Bool.and_eq_true] at hn; simp only [HintCalls] at hd; simp only [CallCode]
    exact ⟨callCode_of_hint h hn.1.2 ms hd.1, callCode_of_hint q hn.2 ms hd.2⟩
  | Nomm.n12 _ _, h, _, _ => by simp [HintOk] at h
  | Nomm.mean _ _ _ _ _, h, _, _ => by simp [HintOk] at h

theorem noAx0_of_hint : ∀ (n : Nomm), HintOk n = true → Bake.NoAx0 n
  | Nomm.cons p q, h => by
    simp only [HintOk, Bool.and_eq_true] at h; exact ⟨noAx0_of_hint p h.1, noAx0_of_hint q h.2⟩
  | Nomm.n0 _, _ => trivial
  | Nomm.n1 _, _ => trivial
  | Nomm.n2 p q Option.none, h => by
    simp only [HintOk, Bool.and_eq_true] at h; exact ⟨noAx0_of_hint p h.1, noAx0_of_hint q h.2⟩
  | Nomm.n2 p q (some (b, Option.none)), h => by
    simp only [HintOk, Bool.and_eq_true] at h; exact noAx0_of_dir _ h.1
  | Nomm.n2 _ _ (some (_, some _)), h => by simp [HintOk] at h
  | Nomm.n3 p, h => by simp only [HintOk] at h; exact noAx0_of_hint p h
  | Nomm.n4 p, h => by simp only [HintOk] at h; exact noAx0_of_hint p h
  | Nomm.n5 p q, h => by
    simp only [HintOk, Bool.and_eq_true] at h; exact ⟨noAx0_of_hint p h.1, noAx0_of_hint q h.2⟩
  | Nomm.n6 p q r, h => by
    simp only [HintOk, Bool.and_eq_true] at h
    exact ⟨noAx0_of_hint p h.1.1, noAx0_of_hint q h.1.2, noAx0_of_hint r h.2⟩
  | Nomm.n7 p q, h => by
    simp only [HintOk, Bool.and_eq_true] at h; exact ⟨noAx0_of_hint p h.1, noAx0_of_hint q h.2⟩
  | Nomm.n10 a v q, h => by
    simp only [HintOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact ⟨h.1.1, noAx0_of_hint v h.1.2, noAx0_of_hint q h.2⟩
  | Nomm.n11s _ q _, h => by
    simp only [HintOk, Bool.and_eq_true] at h; exact noAx0_of_hint q h.2
  | Nomm.n11d _ h q _, hn => by
    simp only [HintOk, Bool.and_eq_true] at hn; exact ⟨noAx0_of_hint h hn.1.2, noAx0_of_hint q hn.2⟩
  | Nomm.n12 _ _, h => by simp [HintOk] at h
  | Nomm.mean _ _ _ _ _, h => by simp [HintOk] at h

/-- A part of `%6` from its `PartH` and its callees' code entries. -/
theorem sixRH_of (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {msup : Option Nomm} {X : GenRest → Noun → Noun → Prop}
    {n : Nomm} {region : List Nat}
    (N : PartH env snd msup ctx X n region) (hcc : CallCode cod env n) : SixPartsRH env snd msup ctx X n region :=
  ⟨N.link, N.res, pastForkAt_code h7 hcode env hcc⟩

/-- **The run link with hints at `mono` `&`**: every nomm of `HintOk` whose
direct calls meet `CallOk` is a `PartH` at `XM E msup` (link against
`runLCH env snd true msup` on every goal with `GInv`, result, `+past`), every
`snd`, `msup` and region. -/
theorem comp_run_hint (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (E : GenRest → Prop) :
    ∀ (n : Nomm), HintOk n = true → ∀ (msup : Option Nomm) (region : List Nat),
      HintCalls env cod ctx E msup n → PartH env snd msup ctx (XM E msup) n region
  | Nomm.cons p q, h, msup, region, hd => by
    have hc := callCode_of_hint (ctx := ctx) _ h msup hd
    simp only [HintOk, Bool.and_eq_true] at h; simp only [HintCalls] at hd
    have P := comp_run_hint h7 hcode env snd E p h.1 msup region hd.1
    have Q := comp_run_hint h7 hcode env snd E q h.2 msup region hd.2
    exact ⟨fun goal g hi => comp_run_consLRH h7 hcode env msup p q P Q goal g hi, res_consRH P.res Q.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n0 ax, h, msup, region, hd =>
    partH_of_partR rfl (comp_run_dir h7 hcode env E (Nomm.n0 ax) rfl msup region trivial)
  | Nomm.n1 k, h, msup, region, hd =>
    partH_of_partR rfl (comp_run_dir h7 hcode env E (Nomm.n1 k) rfl msup region trivial)
  | Nomm.n2 p q Option.none, h, msup, region, hd => by
    have hc := callCode_of_hint (ctx := ctx) _ h msup hd
    simp only [HintOk, Bool.and_eq_true] at h; simp only [HintCalls] at hd
    have P := comp_run_hint h7 hcode env snd E p h.1 msup region hd.1
    have Q := comp_run_hint h7 hcode env snd E q h.2 msup region hd.2
    exact ⟨fun goal g hi => comp_run_n2LRH h7 hcode env msup p q P Q goal g hi, res_n2RH P.res Q.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n2 p q (some (b, Option.none)), h, msup, region, hd => by
    simp only [HintOk, Bool.and_eq_true] at h; simp only [HintCalls] at hd
    exact partH_of_partR h.2 (comp_run_dir h7 hcode env E _ h.1 msup region hd)
  | Nomm.n2 _ _ (some (_, some _)), h, _, _, _ => by simp [HintOk] at h
  | Nomm.n3 p, h, msup, region, hd => by
    have hc := callCode_of_hint (ctx := ctx) _ h msup hd
    simp only [HintOk] at h; simp only [HintCalls] at hd
    have P := comp_run_hint h7 hcode env snd E p h msup region hd
    exact ⟨fun goal g hi => comp_run_n3LRH h7 env msup p goal region g hi P.link, res_n3RH P.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n4 p, h, msup, region, hd => by
    have hc := callCode_of_hint (ctx := ctx) _ h msup hd
    simp only [HintOk] at h; simp only [HintCalls] at hd
    have P := comp_run_hint h7 hcode env snd E p h msup region hd
    exact ⟨fun goal g hi => comp_run_n4LRH h7 env msup p goal region g hi P.link, res_n4RH P.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n5 p q, h, msup, region, hd => by
    have hc := callCode_of_hint (ctx := ctx) _ h msup hd
    simp only [HintOk, Bool.and_eq_true] at h; simp only [HintCalls] at hd
    have P := comp_run_hint h7 hcode env snd E p h.1 msup region hd.1
    have Q := comp_run_hint h7 hcode env snd E q h.2 msup region hd.2
    exact ⟨fun goal g hi => comp_run_n5LRH h7 hcode env msup p q P Q goal g hi, res_n5RH P.res Q.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n7 p q, h, msup, region, hd => by
    have hc := callCode_of_hint (ctx := ctx) _ h msup hd
    simp only [HintOk, Bool.and_eq_true] at h; simp only [HintCalls] at hd
    have P := comp_run_hint h7 hcode env snd E p h.1 msup region hd.1
    have Q := comp_run_hint h7 hcode env snd E q h.2 (some p) region hd.2
    exact ⟨fun goal g hi => comp_run_n7CRH env msup p q goal region g (Q.link goal g hi)
        (fun x mono sup hX => ⟨hX.1, hX.2.1, rfl⟩)
        (fun nex g1 e => P.link nex.goal g1 (Q.res goal g g1 nex hi e).2.2.1),
      res_n7RH Q.res P.res, pastAt_code h7 hcode env hc⟩
  | Nomm.n10 a v q, h, msup, region, hd => by
    have hc := callCode_of_hint (ctx := ctx) _ h msup hd
    simp only [HintOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h; simp only [HintCalls] at hd
    have V := comp_run_hint h7 hcode env snd E v h.1.2 msup region hd.1
    have Q := comp_run_hint h7 hcode env snd E q h.2 msup region hd.2
    exact ⟨fun goal g hi => comp_run_n10LRH h7 hcode env msup a h.1.1 v q V Q goal g hi,
      res_n10RH h.1.1 V.res Q.res, pastAt_code h7 hcode env hc⟩
  | Nomm.n6 p q r, h, msup, region, hd => by
    have hc := callCode_of_hint (ctx := ctx) _ h msup hd
    have ha := noAx0_of_hint _ h
    simp only [HintOk, Bool.and_eq_true] at h; simp only [HintCalls] at hd; simp only [Bake.NoAx0] at ha
    have hc' := hc
    simp only [CallCode] at hc'
    have P := comp_run_hint h7 hcode env snd E p h.1.1 msup region hd.1
    have Q := fun rg => comp_run_hint h7 hcode env snd E q h.1.2 msup rg hd.2.1
    have R := fun rg => comp_run_hint h7 hcode env snd E r h.2 msup rg hd.2.2
    exact ⟨fun goal g hi => comp_run_n6_allRH h7 hcode env msup p q r region (sixRH_of h7 hcode P hc'.1)
        (sixRH_of h7 hcode (Q region) hc'.2.1) (sixRH_of h7 hcode (R region) hc'.2.2)
        (fun rid => sixRH_of h7 hcode (Q (rid :: region)) hc'.2.1)
        (fun rid => sixRH_of h7 hcode (R (rid :: region)) hc'.2.2) ha.2.1 ha.2.2 goal g hi,
      res_n6_allRH P.res (Q region).res (R region).res (fun rid => (Q (rid :: region)).res)
        (fun rid => (R (rid :: region)).res) ha.2.1 ha.2.2,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n11s tag q body, h, msup, region, hd => by
    have hc := callCode_of_hint (ctx := ctx) _ h msup hd
    simp only [HintOk, Bool.and_eq_true, Bool.not_eq_true'] at h; simp only [HintCalls] at hd
    have Q := comp_run_hint h7 hcode env snd E q h.2 msup region hd
    exact partH_n11s h.1 body Q (pastAt_code h7 hcode env hc)
  | Nomm.n11d tag h q body, hn, msup, region, hd => by
    have hc := callCode_of_hint (ctx := ctx) _ hn msup hd
    simp only [HintOk, Bool.and_eq_true, Bool.not_eq_true'] at hn; simp only [HintCalls] at hd
    have H := comp_run_hint h7 hcode env snd E h hn.1.2 msup region hd.1
    have Q := comp_run_hint h7 hcode env snd E q hn.2 msup region hd.2
    exact partH_n11d_nd h7 hn.1.1 body Q H (pastAt_code h7 hcode env hc)
  | Nomm.n12 _ _, h, _, _, _ => by simp [HintOk] at h
  | Nomm.mean _ _ _ _ _, h, _, _, _ => by simp [HintOk] at h

/-- **The run link with hints on every goal with `GInv`.** -/
theorem comp_run_hintX (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (E : GenRest → Prop) (n : Nomm) (hn : HintOk n = true)
    (msup : Option Nomm) (region : List Nat) (hd : HintCalls env cod ctx E msup n) (goal : CGoalL CSet)
    (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtX (runLCH env snd true msup) ctx (XM E msup) n goal region g :=
  (comp_run_hint h7 hcode env snd E n hn msup region hd).link goal g hi

/-- What a run of the class returns. -/
theorem res_hint (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (E : GenRest → Prop) (n : Nomm) (hn : HintOk n = true)
    (msup : Option Nomm) (region : List Nat) (hd : HintCalls env cod ctx E msup n) :
    ResForR (runLCH env snd true msup) n region :=
  (comp_run_hint h7 hcode env snd E n hn msup region hd).res

/-- **An example**: a static `%spot` around a cons, `[11 %spot [[0 2] [1 k]]]`,
on every goal with `GInv`. -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (snd : Nomm → NeedOrd → Bool) (E : GenRest → Prop) (msup : Option Nomm) (k body : Noun)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtX (runLCH env snd true msup) ctx (XM E msup)
      (Nomm.n11s 0x746f7073 (Nomm.cons (Nomm.n0 2) (Nomm.n1 k)) body) goal region g :=
  comp_run_hintX h7 hcode env snd E _ rfl msup region (by simp [HintCalls]) goal g hi

/-- **An example**: a hint inside a branch of a `%6`, `[6 [0 2] [11 %spot [0
3]] [1 k]]`, on every goal with `GInv`. -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (snd : Nomm → NeedOrd → Bool) (E : GenRest → Prop) (msup : Option Nomm) (k body : Noun)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtX (runLCH env snd true msup) ctx (XM E msup)
      (Nomm.n6 (Nomm.n0 2) (Nomm.n11s 0x746f7073 (Nomm.n0 3) body) (Nomm.n1 k)) goal region g :=
  comp_run_hintX h7 hcode env snd E _ rfl msup region (by simp [HintCalls]) goal g hi

/-- **An example**: a dropped dynamic hint (`%fast`, a clue that computes)
around a cons, inside the subject of a `%7`: `[7 [11 [%fast [4 0 1]] [[0 2]
[1 k]]] [0 3]]`, on every goal with `GInv`. -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (snd : Nomm → NeedOrd → Bool) (E : GenRest → Prop) (msup : Option Nomm) (k body : Noun)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtX (runLCH env snd true msup) ctx (XM E msup)
      (Nomm.n7 (Nomm.n11d 0x74736166 (Nomm.n4 (Nomm.n0 1)) (Nomm.cons (Nomm.n0 2) (Nomm.n1 k)) body) (Nomm.n0 3))
      goal region g :=
  comp_run_hintX h7 hcode env snd E _ rfl msup region (by simp [HintCalls]) goal g hi

end Compiler
end Formalization
