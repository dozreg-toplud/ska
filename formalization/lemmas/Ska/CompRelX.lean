import lemmas.Ska.CompRelTen

/-!
# The relaxed `sem` over `FragX`

README Gaps 12.2.  `OKXR`: what the induction proves of a nomm, the relaxed
`sem` for `%done` (`OKPR`), for every fork-free `%next` whose jump passes no
arguments (`OKNR`) and for every `%pick` whose jumps pass none.  `runX_semR`:
every nomm of `FragX` meets it, by the induction of `runX_ok`
(`CompFragX.lean`), case by case: the leaves (`runOKP_frag_semR`,
`runOKN_frag_semR`), `%6` (`sixP_semR`, `sixNext_semR`), `[4 p]` and
`[3 p]` (`CompRelUnary.lean`), `[7 p q]` with `q` a leaf (`runOKP_n7g_semR`,
`runOKN_n7_semR`), cons (`CompRelCons.lean`), `%5` (`runOKG_n5_semR`),
`%10` (`CompRelTen.lean`) and `[7 [0 axe] q]` (`semPR_from`, `semGR_from`).
The strict relations of the parts come from `runX_ok`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **What the induction over `FragX` proves**: the relaxed `sem` for
`%done`, for fork-free `%next` and for `%pick` with jumps without
arguments. -/
abbrev OKXR (lib : Lib) (nm : Nomm) : Prop :=
  OKPR (Map := Map) lib (CGoal.done : CGoal S) nm ∧ OKNR (S := S) (Map := Map) lib nm ∧
    ∀ z o : Jmp, z.args = [] → o.args = [] → OKPR (Map := Map) lib (CGoal.pick z o : CGoal S) nm

/-- **The relaxed `sem` on `FragX`**, every case. -/
theorem runX_semR (lib : Lib) {nm : Nomm} (hf : FragX (S := S) nm) : OKXR (S := S) (Map := Map) lib nm := by
  induction hf with
  | frag hf =>
    exact ⟨fun hg hj hl _ b0 d0 _ hc h => runOKP_frag_semR lib (hf _) hg hj hl b0 d0 hc h,
      fun hj hth hok hcl _ b0 d0 _ hc h => runOKN_frag_semR lib (hf _) hj hth b0 d0 hc hok hcl h,
      fun z o hz ho => fun hg hj hl _ b0 d0 _ hc h => runOKP_frag_semR lib (hf _) hg hj hl b0 d0 hc h⟩
  | @six c a b hc ha hb ihc iha ihb =>
    have hcp := fragX_pure hc
    have Rc := runX_ok (Map := Map) lib hc
    have Ra := runX_ok (Map := Map) lib ha
    have Rb := runX_ok (Map := Map) lib hb
    exact ⟨sixP_semR lib hcp Rc.2.2 Ra.1 Rb.1 ihc.2.2 iha.1 ihb.1,
      fun hj hth hok hcl hcount b0 d0 hu hcl0 h => sixNext_semR lib hcp
        (fun z o hz ho => Rc.2.2 z o hz ho trivial) Ra.2.1 Rb.2.1 ihc.2.2 iha.2.1 ihb.2.1
        hj hth hok hcl hcount b0 d0 hu hcl0 h,
      fun z o hz ho => sixP_semR lib hcp Rc.2.2 (Ra.2.2 z o hz ho) (Rb.2.2 z o hz ho) ihc.2.2
        (iha.2.2 z o hz ho) (ihb.2.2 z o hz ho)⟩
  | @four p hp ih =>
    have Rp := runX_ok (Map := Map) lib hp
    exact ⟨fun _ _ _ hcount b0 d0 hu hcl0 h =>
        runOKP_n4_semR lib Rp.2.1 ih.2.1 (by simpa only [sixCount] using hcount) b0 d0 hu hcl0 h,
      fun hj _ hok _ hcount b0 d0 hu hcl0 h =>
        runOKN_n4_semR lib Rp.2.1 ih.2.1 hj hok (by simpa only [sixCount] using hcount) b0 d0 hu hcl0 h,
      fun z o _ _ => fun _ hj _ hcount b0 d0 hu hcl0 h =>
        runOKP_n4p_semR lib Rp.2.1 ih.2.1 hj (by simpa only [sixCount] using hcount) b0 d0 hu hcl0 h⟩
  | @three p hp ih =>
    have Rp := runX_ok (Map := Map) lib hp
    exact ⟨fun _ _ _ hcount b0 d0 hu hcl0 h =>
        runOKP_n3_semR lib Rp.2.1 ih.2.1 (by simpa only [sixCount] using hcount) b0 d0 hu hcl0 h,
      fun hj hth hok hcl hcount b0 d0 hu hcl0 h =>
        runOKN_n3_semR lib Rp.2.1 ih.2.1 hj hth hok hcl (by simpa only [sixCount] using hcount) b0 d0 hu hcl0 h,
      fun z o _ _ => fun _ hj _ hcount b0 d0 hu hcl0 h =>
        runOKP_n3p_semR lib Rp.2.1 ih.2.1 hj (by simpa only [sixCount] using hcount) b0 d0 hu hcl0 h⟩
  | @seven p q hq hp ih =>
    have Rp := runX_ok (Map := Map) lib hp
    exact ⟨fun hg hj hl hcount b0 d0 hu hcl0 h => runOKP_n7g_semR lib hg (hq _) Rp.2.1 ih.2.1
        (fun j e => by simp only [GoalJ] at e) hj hl (by simp only [sixCount] at hcount; omega) b0 d0 hu hcl0 h,
      fun hj hth hok hcl hcount b0 d0 hu hcl0 h => runOKN_n7_semR lib (hq _) Rp.2.1 ih.2.1 hj hth hok hcl
        (by simp only [sixCount] at hcount; omega) b0 d0 hu hcl0 h,
      fun z o hz ho => fun hg hj hl hcount b0 d0 hu hcl0 h => runOKP_n7g_semR lib hg (hq _) Rp.2.1 ih.2.1
        (fun j e => by simp only [GoalJ] at e; rcases e with rfl | rfl <;> assumption) hj hl
        (by simp only [sixCount] at hcount; omega) b0 d0 hu hcl0 h⟩
  | @cons p q hp hq ihp ihq =>
    have cp : CleanN S Map p := CleanA.toN (runX_clean hp)
    have cq : CleanN S Map q := CleanA.toN (runX_clean hq)
    have Rp := runX_ok (Map := Map) lib hp
    have Rq := runX_ok (Map := Map) lib hq
    exact ⟨runOKP_consD_semR lib Rp.2.1 Rq.2.1 ihp.2.1 ihq.2.1 cp cq (fragX_pure hp) (fragX_pure hq),
      consN_semRK lib Rp.2.1 Rq.2.1 ihp.2.1 ihq.2.1 cp cq (fragX_pure hp) (fragX_pure hq),
      fun z o _ _ => runOKP_consP_semR lib Rp.2.1 Rq.2.1 ihp.2.1 ihq.2.1 cp cq (fragX_pure hp) (fragX_pure hq) z o⟩
  | @five p q hp hq ihp ihq =>
    have cp : CleanN S Map p := CleanA.toN (runX_clean hp)
    have cq : CleanN S Map q := CleanA.toN (runX_clean hq)
    have hpp := fragX_pure hp
    have Rp := runX_ok (Map := Map) lib hp
    have Rq := runX_ok (Map := Map) lib hq
    exact ⟨fun hg hj _ hcount b0 d0 hu hcl0 h =>
        (runOKG_n5_semR lib Rp.2.1 Rq.2.1 ihp.2.1 ihq.2.1 cp cq hpp (goal := CGoal.done) trivial hj hcount
          b0 d0 hu hcl0 h).toP hg,
      fun hj _ hok _ hcount b0 d0 hu hcl0 h =>
        runOKG_n5_semR lib Rp.2.1 Rq.2.1 ihp.2.1 ihq.2.1 cp cq hpp (goal := CGoal.next _ _) hok hj hcount
          b0 d0 hu hcl0 h,
      fun z o _ _ => fun hg hj _ hcount b0 d0 hu hcl0 h =>
        (runOKG_n5_semR lib Rp.2.1 Rq.2.1 ihp.2.1 ihq.2.1 cp cq hpp (goal := CGoal.pick _ _) trivial hj hcount
          b0 d0 hu hcl0 h).toP hg⟩
  | @ten a v q hv hq ihv ihq =>
    have cv : CleanN S Map v := CleanA.toN (runX_clean hv)
    have cq : CleanN S Map q := CleanA.toN (runX_clean hq)
    have Rv := runX_ok (Map := Map) lib hv
    have Rq := runX_ok (Map := Map) lib hq
    exact ⟨runOKP_n10D_semR lib Rv.2.1 Rq.2.1 ihv.2.1 ihq.2.1 cv cq (fragX_pure hv) (fragX_pure hq),
      runOKN_n10_semR lib Rv.2.1 Rq.2.1 ihv.2.1 ihq.2.1 cv cq (fragX_pure hv) (fragX_pure hq),
      fun z o _ _ => runOKP_n10P_semR lib Rv.2.1 Rq.2.1 ihv.2.1 ihq.2.1 cv cq (fragX_pure hv) (fragX_pure hq) z o⟩
  | @sevenFrom axe q ha hq ihq =>
    exact ⟨fun hg hj hl hcount b0 d0 hu hcl0 h => by
        obtain ⟨nx, laz', h1, hl', rfl⟩ := runL_seven_from ha h
        exact semPR_from (ihq.1 hg hj hl (by simp only [sixCount] at hcount; omega) b0 d0 hu hcl0 h1) hl',
      fun hj hth hok hcl hcount b0 d0 hu hcl0 h => by
        obtain ⟨nx, laz', h1, hl', rfl⟩ := runL_seven_from ha h
        exact semGR_from (ihq.2.1 hj hth hok hcl (by simp only [sixCount] at hcount; omega) b0 d0 hu hcl0 h1) hl',
      fun z o hz ho => fun hg hj hl hcount b0 d0 hu hcl0 h => by
        obtain ⟨nx, laz', h1, hl', rfl⟩ := runL_seven_from ha h
        exact semPR_from (ihq.2.2 z o hz ho hg hj hl (by simp only [sixCount] at hcount; omega) b0 d0 hu hcl0 h1)
          hl'⟩

/-- **The run for `%done` from `gen0` meets the relaxed `sem`**, on
`FragX` with at most 255 `%6`. -/
theorem runX_semR_gen0 (lib : Lib) {nm : Nomm} (hf : FragX (S := S) nm) (hcount : sixCount nm ≤ 255)
    {region : List Nat} {nex : NextL S} {g1 : Gen Map}
    (h : runL nm (CGoalL.done : CGoalL S) region (gen0 : Gen Map) = some (nex, g1)) :
    SemPR (Map := Map) lib nm CGoal.done gen0 g1 nex :=
  (runX_semR lib hf).1 trivial trivial trivial hcount (by simp [gen0]) rfl upBelow_gen0 clear_gen0 h

end Comp
end SkaModel
end Formalization
