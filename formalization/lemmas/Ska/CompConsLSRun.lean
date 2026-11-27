import lemmas.Ska.CompConsLS

/-!
# The cons under a flat lazy goal: `lokS_consP`

README Gaps 12.24.  The cons `[p q]` under `%next L th` with `L` flat:
`+split` of the sure need at the block `o` (`split`, the fork-free arm of
`CompSplit.lean`), then of every bond's need at its own block (`SplitBs`),
the tail, the head, `+copy` of the sure needs (`copy`) and the merge of the
bonds (`MergeBs`); `pairLS_ok` composes them.

* `splitL_flat`, `copyL_flat'`: `+split` and `+copy` of flat needs as the
  fork-free arm followed by the loop over the bonds.
* `splitAt_of_splitBs`: `SplitAt` at every goal entry, from `SplitBs`.
* `lokS_consP`: the cons whose parts are call-free and meet `LOKS` meets
  `LOKS` (no `+past`: both `+past`s are the identity for call-free parts).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`+split` of a flat need**: the fork-free arm on the sure need, then
the loop over the bonds. -/
theorem splitL_flat {L : Lazy S} (hL : Flat L) {th : Jmp} {g0 g'' : Gen Map} {hed tel : Lazy S} {o : Nat}
    (h : splitL ⟨L, th⟩ g0 = some ((hed, tel, o), g'')) :
    ∃ (sh st : Sure S) (gS : Gen Map) (bh bt : List (Nat × Lazy S)),
      Comp.split ⟨L.sure, th⟩ g0 = some ((sh, st, o), gS) ∧ SplitBs L.bond bh bt gS g'' ∧
      hed = mk sh [] (bh.filter fun e => !(lazyEmpty e.2)) ∧ tel = mk st [] (bt.filter fun e => !(lazyEmpty e.2)) := by
  unfold splitL at h
  obtain ⟨o', g1, h1, h⟩ := bind_some h
  rw [emit_apply] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨⟨hd, tl⟩, g2, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  have eL : L = mk L.sure [] L.bond := by rw [← hL.1]; exact (eta L).symm
  rw [eL] at h2
  obtain ⟨sh, st, gS, bh, bt, hs, hb, he⟩ := splitLoop_flat hL.2 h2
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨sh, st, gS, bh, bt, ?_, hb, rfl, rfl⟩
  simp only [Comp.split, bind_apply, emit_apply, Option.bind_some, hs, pure_apply]

/-- **`+copy` of two flat needs**: the fork-free arm on the sure needs,
then the merge of the bonds. -/
theorem copyL_flat' {first : NextL S} {second : Lazy S} (hf1 : Flat first.laz) (hf2 : Flat second)
    {g g' : Gen Map} {nex : NextL S} (h : copyL first second g = some (nex, g')) :
    ∃ (n : Next S) (g3 : Gen Map) (r : List (Nat × Lazy S)),
      copy ⟨first.laz.sure, first.th⟩ second.sure g = some (n, g3) ∧
      MergeBs (index (Map := Map) (fun e : Nat × Lazy S => e.1) second.bond) first.laz.bond r g3 g' ∧
      nex = pairRes n r second.bond first.laz.bond := by
  obtain ⟨eth, hc⟩ := copyL_flat hf1 hf2 h
  obtain ⟨ned, ops, g1, g2, r, h1, h2, hM, el⟩ := copyLazyL_flat hf1.2 hf2.2 hc
  refine ⟨⟨⟨ned, HoonSet.uni first.laz.sure.lok second.sure.lok⟩, jmp0 g.bo⟩, g2, r, ?_, hM, ?_⟩
  · simp only [copy, copyLazy, bind_apply, emit_apply, Option.bind_some, h1, h2, pure_apply]
  · rcases nex with ⟨laz, th'⟩
    simp only at eth el
    subst eth el
    rfl

/-- **`SplitAt` at every goal entry**, from the loop of `+split` over flat
bonds. -/
theorem splitAt_of_splitBs {b bh bt : List (Nat × Lazy S)} (hf : FlatB b) {sh0 st0 : Sure S} {gS g'' : Gen Map}
    (hb : SplitBs b bh bt gS g'') (hd : gS.drop = false) (hn : (b.map Prod.fst).Nodup)
    (hblk : ∀ e ∈ b, ∃ B fin, HoonMap.get gS.blocks e.1 = some ⟨[], B, fin⟩)
    (hreg : ∀ e ∈ b, Distinct e.2.sure.ned ∧ ∀ x, NMem e.2.sure.ned x → x < gS.re)
    (hcl : ∀ e ∈ b, Clean e.2.sure.ned) :
    ∃ PB : Nat → List Pole, Pref gS g'' PB ∧ (∀ k, k ∉ b.map Prod.fst → PB k = []) ∧ FlatB bh ∧ FlatB bt ∧
      bh.map Prod.fst = b.map Prod.fst ∧ bt.map Prod.fst = b.map Prod.fst ∧
      ∀ e ∈ b, ∃ sh st, SplitAt (Map := Map) e (mk sh0 [] (bh.filter fun e => !(lazyEmpty e.2)))
        (mk st0 [] (bt.filter fun e => !(lazyEmpty e.2))) (PB e.1) gS.re g''.re sh st := by
  obtain ⟨eh, et, fh, ft, P, PP, Pout, Pin⟩ := hb.spec hd hn hblk
  have hnh : (bh.map Prod.fst).Nodup := by rw [eh]; exact hn
  have hnt : (bt.map Prod.fst).Nodup := by rw [et]; exact hn
  refine ⟨P, PP, Pout, fh, ft, eh, et, fun e he => ?_⟩
  obtain ⟨s, sh, st, g1, g2, es, mh, mt, l1, l2, dd, bb, sp, pp⟩ := Pin e he
  obtain ⟨B0, fin0, hb0⟩ := hblk e he
  obtain ⟨A, PA, M1, M2, CL, RA, RB, SD⟩ := splitSure_ok sp dd (bb B0 fin0 hb0)
  have hPA : P e.1 = A := pp A PA
  have ess : e.2.sure = s := by rw [es]; rfl
  obtain ⟨dsd, rsd⟩ := hreg e he
  rw [ess] at dsd rsd
  obtain ⟨Dh, Dt, Dht, F, Sm⟩ := SD dsd (fun y hy => by have := rsd y hy; omega)
  have prune : ∀ (bx : List (Nat × Lazy S)) (sx : Sure S), (bx.map Prod.fst).Nodup → (e.1, ofSure sx) ∈ bx →
      (e.1, ofSure sx) ∈ bx.filter (fun e => !(lazyEmpty e.2)) ∨
      (e.1 ∉ (bx.filter fun e => !(lazyEmpty e.2)).map Prod.fst ∧ sx.ned = Need.none ∧ HoonSet.small sx.lok = true) := by
    intro bx sx hnx hm
    cases hle : lazyEmpty (ofSure sx) with
    | false => exact Or.inl (List.mem_filter.mpr ⟨hm, by simp [hle]⟩)
    | true =>
      refine Or.inr ⟨fun hk => ?_, ?_, ?_⟩
      · obtain ⟨e', he', ee⟩ := List.mem_map.mp hk
        obtain ⟨he'1, he'2⟩ := List.mem_filter.mp he'
        have : e' = (e.1, ofSure sx) := eq_of_label hnx he'1 hm ee
        subst this
        simp [hle] at he'2
      · simp [lazyEmpty, ofSure] at hle; exact of_decide_eq_true hle.1
      · simp [lazyEmpty, ofSure] at hle; exact hle.2
  have regsA : RegsIn (fun x => NMem e.2.sure.ned x ∨ (gS.re ≤ x ∧ x < g''.re)) A := by
    have R1 := RA (fun x => x < g''.re → NMem s.ned x ∨ gS.re ≤ x) (fun x hx _ => Or.inl hx)
      (fun x hx _ => Or.inr (by omega))
    have R2 := RB (fun x hx => by have := rsd x hx; omega)
    intro p hp x hx
    have b2 : x < g2.re := R2 p hp x hx
    rcases R1 p hp x hx (by omega) with a | a
    · exact Or.inl (by rw [ess]; exact a)
    · exact Or.inr ⟨a, by omega⟩
  refine ⟨sh, st, ⟨hf e he, ?_, ?_, fun y hy => ?_, fun y hy => ?_, Dh, Dt, Dht, (CL (by rw [← ess]; exact hcl e he)).1,
    (CL (by rw [← ess]; exact hcl e he)).2, ?_, by rw [hPA]; exact regsA, ?_⟩⟩
  · exact prune bh sh hnh mh
  · exact prune bt st hnt mt
  · rw [ess]
    rcases M1 y hy with a | a
    · exact Or.inl a
    · exact Or.inr ⟨by omega, by omega⟩
  · rw [ess]
    rcases M2 y hy with a | a
    · exact Or.inl a
    · exact Or.inr ⟨by omega, by omega⟩
  · rw [ess]; exact F
  · intro lib σ O c gul st' t R a b ha hb'
    rw [hPA, ess]
    exact Sm lib σ O c gul st' t R a b ha hb'

/-- **The cons of two call-free parts under a flat lazy goal** (the run
field of `LOKS`): both `+past`s are the identity, `pairLS_ok` composes the
parts' `RunOKLS`. -/
theorem lokS_consP_run (lib : Lib) (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {fh ft : Noun}
    (hfh : ∃ x y, fh = C x y) (hpp : p.pure = true) (hqp : q.pure = true)
    (Mp : MinkEq lib P fh p) (Mq : MinkEq lib P ft q)
    (Sp : LOKS (S := S) (Map := Map) false lib env P fh p) (Sq : LOKS (S := S) (Map := Map) false lib env P ft q)
    {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hcount : sixCount (Nomm.cons p q) ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (hcl0 : Clear g0) (hcb : CondBelow g0) (h1 : 1 ≤ th.there) (h2 : th.there < g0.bo) (hta : th.args = [])
    (ht : th.there ∉ (entries L).map Prod.fst) (hsd : Distinct L.sure.ned)
    (hsl : ∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B th', HoonMap.get g0.blocks e.1 = some ⟨[], B, Termin.hop th'⟩)
    (hnd : ((entries L).map Prod.fst).Nodup)
    (hed : ∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hfl : Flat L) (hcs : Clean L.sure.ned) (hce : ∀ e ∈ entries L, Clean e.2.sure.ned)
    (hr : runLC env sup (Nomm.cons p q) (CGoalL.next L th) region g0 = some (nex, g1)) :
    (∃ Q, RunOKLS (Map := Map) lib P (C fh ft) L th Q false g0 g1 nex) ∧
      nex.th.there ∉ (entries nex.laz).map Prod.fst ∧ (nex.th = th ∨ g0.bo ≤ nex.th.there) ∧ Flat nex.laz ∧
      (∀ e ∈ entries nex.laz, Clean e.2.sure.ned) := by
  have e : (runLC env sup (Nomm.cons p q) (CGoalL.next L th) region : CM Map (NextL S)) = (do
        let (hed, tel, o) ← splitL ⟨L, th⟩
        let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
        let nex2 ← runLC env sup q (CGoalL.next tel nexh.th) region
        let nex2 ← pastL env.cod nex2 p region
        let nex1 ← runLC env sup p (CGoalL.next nexh.laz nex2.th) region
        copyL nex1 nex2.laz) := rfl
  rw [e] at hr
  obtain ⟨⟨hed, tel, o⟩, g'', hs, hr⟩ := bind_some hr
  simp only at hr
  obtain ⟨nexh, gb, hph, hr⟩ := bind_some hr
  rw [pastL_pure _ _ hqp, pure_apply] at hph
  simp only [Option.some.injEq, Prod.mk.injEq] at hph
  obtain ⟨rfl, rfl⟩ := hph
  obtain ⟨nexq, g1', h3, hr⟩ := bind_some hr
  obtain ⟨nexq', g1'', hp2, hr⟩ := bind_some hr
  rw [pastL_pure _ _ hpp, pure_apply] at hp2
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  obtain ⟨nexp, g2, h4, hcp⟩ := bind_some hr
  have eL := entries_flat hfl
  obtain ⟨sH, sT, gS, bh, bt, hsS, hSB, rfl, rfl⟩ := splitL_flat hfl hs
  -- the sure part (as `consLC_runN`)
  have hok : GoalOK g0 (CGoal.next L.sure th) := ⟨hsd, fun r hr => (hsl r hr).1⟩
  have hkg : ∀ r, NMem L.sure.ned r → HoonMap.get g0.cond r = Option.none := fun r hr => (hsl r hr).2
  obtain ⟨eo, E2, _, Mh, Mt, SP⟩ := split_ok hsS
  obtain ⟨Dh, Dt, Dht, F, B⟩ := SP hok.1 hok.2
  obtain ⟨G2, eo', lt2, _⟩ := split_down hsS h1 h2 d0
  simp only at eo'
  subst eo
  have CS := clean_split hsS hcs
  simp only at CS
  have c2 : gS.cond = g0.cond := (kc_split _).keep _ _ _ hsS
  have d2 : gS.drop = false := E2.2.2.1.trans d0
  have G2U : GrowU g0 gS := G2.toU hu
  have u2 : UpBelow gS := G2U.up hu
  have lt2' : ∀ (n : Need), (∀ y, NMem n y → NMem L.sure.ned y ∨ (g0.re ≤ y ∧ y < gS.re)) →
      ∀ y, NMem n y → y < gS.re := fun n M y hy => by
    rcases M y hy with a | ⟨_, a⟩
    · exact Nat.lt_of_lt_of_le (hok.2 y a) E2.1
    · exact a
  have cl2 : Clear gS := hcl0.growU G2U
  have cf2 : CondFresh g0 gS := condFresh_of_eq E2.1 c2
  have cb2 : CondBelow gS := cf2.below hcb
  have AS : AboveIn (fun r => HoonMap.get g0.cond r = Option.none) g0.bo gS :=
    (keepsA_split (P := fun r => HoonMap.get g0.cond r = Option.none) d0 hkg (jmpIn_nil hta)
      (fun r hr => condBelow_none hcb hr) hsS).1.ab _ (aboveIn_start _ g0)
  have BS : BelowIn g0.bo gS :=
    (keeps_split d0 (fun r hr => hok.2 r hr) (jmpIn_nil hta) hsS).1.bel _ (belowIn_start g0)
  have hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < gS.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < gS.bo → (HoonMap.get gS.blocks k).map (unproxyBlob cf) = HoonMap.get gS.blocks k := by
    intro cf hcf k h0 h1'
    have u0 : ∀ x, x < gS.re → unproxy cf x = unproxy g0.cond x := unproxy_agree (fun k hk => hcf k hk)
    have u1 : ∀ x, HoonMap.get g0.cond x = Option.none → unproxy g0.cond x = id x := fun x hx => unproxy_none hx
    cases hg : HoonMap.get gS.blocks k with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      rw [unproxyBlob, renBlob_congr u0 (BS k b h0 h1' hg), renBlob_congr u1 (AS k b h0 h1' hg), renBlob_id]
  have hblk : ∀ (c : Straight Map), Agree c g0 gS →
      ∀ (σ : Type) (O : Oracle σ) st regs t gul x y, FitsS sH x → FitsS sT y → HoldsN sH.ned regs x →
        HoldsN sT.ned regs y →
          GoalSem lib O c gul st (Keep g0 gS (CGoal.next L.sure th)) regs t (jmp0 g0.bo) (CGoal.next L.sure th)
            (some (C x y)) := by
    intro c hc σ O st' regs t gul x y fx fy hx hy
    refine ⟨fun _ => ?_, fun hn => absurd ((F x y).mpr ⟨fx, fy⟩) hn⟩
    obtain ⟨R', hl, u, e⟩ := B d0 c hc lib σ O st' t regs x y gul hx hy
    exact ⟨R', hl, fun r ⟨_, k⟩ => u r k, e⟩
  have hnot : ∀ x y, ¬ FitsS sH x ∨ ¬ FitsS sT y → ¬ FitsS L.sure (C x y) := fun x y hn hf => by
    rcases hn with a | a
    · exact a ((F x y).mp hf).1
    · exact a ((F x y).mp hf).2
  have Mf := fun {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone} (_ : P s)
      (hm : minkF lib gul n tm s (C fh ft) = some r) => minkF_consG hfh hm
  have Mb := fun {s gul : Noun} {tm : Trace} {rh : Tone} (_ : P s) (hh : Mink lib gul tm s fh rh) =>
    mink_consG_bwd (ft := ft) hfh hh
  -- the bonds
  have hblS : ∀ e ∈ L.bond, ∃ B fin, HoonMap.get gS.blocks e.1 = some ⟨[], B, fin⟩ := fun e he => by
    obtain ⟨hlt, B, th', hb⟩ := hlab e (by rw [eL]; exact he)
    exact ⟨B, _, by rw [E2.2.2.2 _ hlt]; exact hb⟩
  obtain ⟨PB, PBP, PBo, fbh, fbt, ebh, ebt, SPL⟩ := splitAt_of_splitBs (Map := Map) (sh0 := sH) (st0 := sT) hfl.2 hSB
    d2 (by rw [← eL]; exact hnd) hblS
    (fun e he => ⟨(hed e (by rw [eL]; exact he)).1, fun x hx => by
      have := ((hed e (by rw [eL]; exact he)).2 x hx).1; have := E2.1; omega⟩)
    (fun e he => hce e (by rw [eL]; exact he))
  -- the halves
  have fH : Flat (mk sH [] (bh.filter fun e => !(lazyEmpty e.2))) :=
    flat_mk (fun e he => fbh e (List.mem_filter.mp he).1)
  have fT : Flat (mk sT [] (bt.filter fun e => !(lazyEmpty e.2))) :=
    flat_mk (fun e he => fbt e (List.mem_filter.mp he).1)
  have eH := entries_flat fH
  have eT := entries_flat fT
  have hhl : ∀ e ∈ (mk sH [] (bh.filter fun e => !(lazyEmpty e.2))).bond, e.1 ∈ L.bond.map Prod.fst := fun e he => by
    rw [← ebh]; exact List.mem_map_of_mem (List.mem_filter.mp he).1
  have htl : ∀ e ∈ (mk sT [] (bt.filter fun e => !(lazyEmpty e.2))).bond, e.1 ∈ L.bond.map Prod.fst := fun e he => by
    rw [← ebt]; exact List.mem_map_of_mem (List.mem_filter.mp he).1
  have hnL : (L.bond.map Prod.fst).Nodup := by rw [← eL]; exact hnd
  have hhn : ((mk sH [] (bh.filter fun e => !(lazyEmpty e.2))).bond.map Prod.fst).Nodup :=
    (show (bh.map Prod.fst).Nodup by rw [ebh]; exact hnL).sublist (List.Sublist.map _ List.filter_sublist)
  have htn : ((mk sT [] (bt.filter fun e => !(lazyEmpty e.2))).bond.map Prod.fst).Nodup :=
    (show (bt.map Prod.fst).Nodup by rw [ebt]; exact hnL).sublist (List.Sublist.map _ List.filter_sublist)
  have labL : ∀ k, k ∈ L.bond.map Prod.fst → k < g0.bo := fun k hk => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    exact (hlab e (by rw [eL]; exact he)).1
  have halfE : ∀ (half : Bool) e, e ∈ (if half then (mk sH [] (bh.filter fun e => !(lazyEmpty e.2))).bond
      else (mk sT [] (bt.filter fun e => !(lazyEmpty e.2))).bond) → ∃ eb ∈ L.bond, ∃ sh st,
      SplitAt (Map := Map) eb (mk sH [] (bh.filter fun e => !(lazyEmpty e.2))) (mk sT [] (bt.filter fun e => !(lazyEmpty e.2)))
        (PB eb.1) gS.re g''.re sh st ∧ e = (eb.1, ofSure (if half then sh else st)) := by
    intro half e he
    cases half
    · simp only [Bool.false_eq_true, if_false] at he ⊢
      obtain ⟨eb, heb, ee⟩ := List.mem_map.mp (htl e he)
      obtain ⟨sh, st, SA⟩ := SPL eb heb
      rcases SA.int with a | ⟨a, _⟩
      · exact ⟨eb, heb, sh, st, SA, eq_of_label htn he a ee.symm⟩
      · exact absurd (by rw [ee]; exact List.mem_map_of_mem he) a
    · simp only [if_true] at he ⊢
      obtain ⟨eb, heb, ee⟩ := List.mem_map.mp (hhl e he)
      obtain ⟨sh, st, SA⟩ := SPL eb heb
      rcases SA.inh with a | ⟨a, _⟩
      · exact ⟨eb, heb, sh, st, SA, eq_of_label hhn he a ee.symm⟩
      · exact absurd (by rw [ee]; exact List.mem_map_of_mem he) a
  have d'' : g''.drop = false := PBP.drop.trans d2
  have u'' : UpBelow g'' := PBP.upBelow u2
  have cl'' : Clear g'' := PBP.clear cl2
  have cb'' : CondBelow g'' := PBP.condBelow cb2
  have c'' : g''.cond = g0.cond := PBP.cond.trans c2
  have bo'' : g''.bo = gS.bo := PBP.bo
  have re'' : gS.re ≤ g''.re := PBP.re
  have re0 := E2.1
  have nk'' : ∀ x, (NMem L.sure.ned x ∨ (∃ e ∈ L.bond, NMem e.2.sure.ned x) ∨ g0.re ≤ x) →
      HoonMap.get g''.cond x = Option.none := fun x hx => by
    rw [c'']
    rcases hx with a | ⟨e, he, a⟩ | a
    · exact hkg x a
    · exact ((hed e (by rw [eL]; exact he)).2 x a).2
    · exact condBelow_none hcb a
  -- the tail
  have hcq : sixCount q ≤ 255 := by simp only [sixCount] at hcount; omega
  have hcp' : sixCount p ≤ 255 := by simp only [sixCount] at hcount; omega
  obtain ⟨⟨Qt, Rq⟩, jq1, jq2, fq, cqE⟩ := Sq.run (sup := sup) (region := region) (L := mk sT [] (bt.filter fun e => !(lazyEmpty e.2)))
    (th := jmp0 g0.bo) hcq (by omega) d'' u'' cl'' cb''
    (show 1 ≤ (jmp0 g0.bo).there from b0) (show (jmp0 g0.bo).there < g''.bo by simp only [jmp0]; omega) rfl
    (fun hm => by
      rw [eT] at hm
      obtain ⟨e, he, ee⟩ := List.mem_map.mp hm
      have := labL _ (htl e he); simp only [jmp0] at ee; omega)
    Dt (fun x hx => ⟨by have := lt2' _ Mt x hx; omega, nk'' x (by
      rcases Mt x hx with a | a
      · exact Or.inl a
      · exact Or.inr (Or.inr a.1))⟩)
    (fun e he => by
      rw [eT] at he
      obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE false e he
      obtain ⟨hlt, B, th', hb⟩ := hlab eb (by rw [eL]; exact heb)
      exact ⟨by omega, _, th', PBP.blk (by rw [E2.2.2.2 _ hlt]; exact hb)⟩)
    (by rw [eT]; exact htn)
    (fun e he => by
      rw [eT] at he
      obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE false e he
      refine ⟨SA.dt, fun x hx => ?_⟩
      rcases SA.mt x hx with a | a
      · exact ⟨by have := ((hed eb (by rw [eL]; exact heb)).2 x a).1; omega, nk'' x (Or.inr (Or.inl ⟨eb, heb, a⟩))⟩
      · exact ⟨a.2, nk'' x (Or.inr (Or.inr (by omega)))⟩)
    fT CS.2
    (fun e he => by
      rw [eT] at he
      obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE false e he
      exact SA.ct) h3
  -- the head
  have u1 : UpBelow g1' := Rq.grow.up u''
  have cl1 : Clear g1' := cl''.growU Rq.grow
  have cb1 : CondBelow g1' := Rq.cfr.below cb''
  have hq1 := Rq.lo
  have hq2 := Rq.hi
  have rq := Rq.re
  have bq := Rq.bo
  obtain ⟨⟨Qh, Rp⟩, jp1, jp2, fp, cpE⟩ := Sp.run (sup := sup) (region := region) (L := mk sH [] (bh.filter fun e => !(lazyEmpty e.2))) hcp' (by omega)
    (Rq.drop.trans d'') u1 cl1 cb1 hq1 hq2 (nextArgs_nil Rq.ent rfl)
    (fun hm => by
      rw [eH] at hm
      obtain ⟨e, he, ee⟩ := List.mem_map.mp hm
      have := labL _ (hhl e he)
      rcases jq2 with a | a
      · rw [a] at ee; simp only [jmp0] at ee; omega
      · omega)
    Dh (fun x hx => ⟨by have := lt2' _ Mh x hx; omega, by
      rw [Rq.cfr.get_lt (by have := lt2' _ Mh x hx; omega)]
      exact nk'' x (by
        rcases Mh x hx with a | a
        · exact Or.inl a
        · exact Or.inr (Or.inr a.1))⟩)
    (fun e he => by
      rw [eH] at he
      obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE true e he
      obtain ⟨hlt, B, th', hb⟩ := hlab eb (by rw [eL]; exact heb)
      have hb'' : HoonMap.get g''.blocks eb.1 = some ⟨[], PB eb.1 ++ B, Termin.hop th'⟩ :=
        PBP.blk (by rw [E2.2.2.2 _ hlt]; exact hb)
      refine ⟨by omega, ?_⟩
      by_cases hm : eb.1 ∈ (entries (mk sT [] (bt.filter fun e => !(lazyEmpty e.2)))).map Prod.fst
      · obtain ⟨e0, h0, e0e⟩ := List.mem_map.mp hm
        obtain ⟨F0, hF0, -⟩ := Rq.front e0 h0
        rw [← e0e] at hb''
        exact ⟨_, th', by rw [← e0e]; exact hF0 _ _ hb''⟩
      · exact ⟨_, th', by rw [Rq.keep _ (by omega) hm]; exact hb''⟩)
    (by rw [eH]; exact hhn)
    (fun e he => by
      rw [eH] at he
      obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE true e he
      refine ⟨SA.dh, fun x hx => ?_⟩
      rcases SA.mh x hx with a | a
      · have := ((hed eb (by rw [eL]; exact heb)).2 x a).1
        exact ⟨by omega, by rw [Rq.cfr.get_lt (by omega)]; exact nk'' x (Or.inr (Or.inl ⟨eb, heb, a⟩))⟩
      · exact ⟨by omega, by rw [Rq.cfr.get_lt (by omega)]; exact nk'' x (Or.inr (Or.inr (by omega)))⟩)
    fH CS.1
    (fun e he => by
      rw [eH] at he
      obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE true e he
      exact SA.ch) h4
  -- the copy
  obtain ⟨n, g3', r, hc, hM, rfl⟩ := copyL_flat' fp fq hcp
  obtain ⟨R, hth, eth, fR, cR, lR⟩ := pairLS_ok (Fin := fun _ _ _ x y r => r = Tone.zero (C x y))
    (FinB := fun _ _ x y r => r = Tone.zero (C x y)) (hed := mk sH [] (bh.filter fun e => !(lazyEmpty e.2)))
    (tel := mk sT [] (bt.filter fun e => !(lazyEmpty e.2))) Mf Mb (fun _ _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    hfl hnL hkg
    (fun e he => ⟨(hlab e (by rw [eL]; exact he)).1, (hlab e (by rw [eL]; exact he)).2,
      (hed e (by rw [eL]; exact he)).1, (hed e (by rw [eL]; exact he)).2⟩)
    hok E2 G2U c2 hcb Mh Mt Dht PBP PBo fH fT SPL hhl htl hhn htn (Ext.refl g'') (GrowU.refl g'') rfl rfl
    (Or.inl ⟨rfl, rfl, Or.inr (totalC_of_minkEq Mq)⟩) (Or.inr (totalC_of_minkEq Mp))
    Rq Rp fq fp cqE cpE (Sq.clean (L := mk sT [] (bt.filter fun e => !(lazyEmpty e.2))) CS.2 h3)
    (Sp.clean (L := mk sH [] (bh.filter fun e => !(lazyEmpty e.2))) CS.1 h4) hc hM hu d0 hfix
    (fun _ _ _ x y r hn hr => Or.inr ⟨C x y, hr, hnot x y hn⟩)
    (fun _ _ x y hn => ⟨_, rfl, Or.inr ⟨C x y, rfl, hnot x y hn⟩⟩)
    (fun c hc σ Inv ν O n gul hS hF st' regs t tm x y n' r _ hI htr fx fy hx hy hr => by
      subst hr
      exact goalSemC_of_goalSem hI htr _ (some (C x y)) (hblk c hc σ O st' regs t gul x y fx fy hx hy))
    (fun c hc σ Inv ν O gul hS hB st' regs t tm x y hI htr fx fy hx hy res _ =>
      ⟨_, rfl, goalSemC_of_goalSem hI htr _ (some (C x y)) (hblk c hc σ O st' regs t gul x y fx fy hx hy)⟩)
  refine ⟨⟨_, R⟩, fun hm => ?_, Or.inr hth, fR, cR⟩
  obtain ⟨e', he', ee⟩ := List.mem_map.mp hm
  have := lR e' he'
  have hthe : (pairRes n r nexq.laz.bond nexp.laz.bond).th = n.th := rfl
  rw [hthe, eth] at ee
  simp only [jmp0] at ee
  omega

/-! ## The sure part stays clean -/

theorem clean_splitLoop {l : Lazy S} {o : Nat} {g g' : Gen Map} {x : Lazy S × Lazy S}
    (h : splitLoop l o g = some (x, g')) (hc : Clean l.sure.ned) : Clean x.1.sure.ned ∧ Clean x.2.sure.ned := by
  rcases l with ⟨s, f, b⟩
  rw [splitLoop] at h
  obtain ⟨⟨sh, st⟩, g1, h1, h⟩ := bind_some h
  have C1 : Clean sh.ned ∧ Clean st.ned := by
    simp only [splitSure] at h1
    obtain ⟨_, _, h2⟩ := Option.bind_eq_some_iff.mp h1
    obtain ⟨⟨⟨nh, nt⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h4
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
    exact clean_splitNeed h3 hc
  cases hfb : (f.isEmpty && b.isEmpty)
  · simp only [fork_mk, bond_mk, hfb, Bool.false_eq_true, if_false] at h
    obtain ⟨_, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact C1
  · simp only [fork_mk, bond_mk, hfb, if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact C1

theorem clean_copyLazyL {o : Nat} {a b l : Lazy S} {g g' : Gen Map} (h : copyLazyL o a b g = some (l, g'))
    (ha : Clean a.sure.ned) (hb : Clean b.sure.ned) : Clean l.sure.ned := by
  rcases a with ⟨s1, f1, b1⟩
  rw [copyLazyL] at h
  obtain ⟨⟨ned, ops⟩, g1, h1, h⟩ := bind_some h
  obtain ⟨_, _, _, h⟩ := bind_some h
  obtain ⟨_, _, _, h⟩ := bind_some h
  obtain ⟨_, _, _, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact clean_copyNeed _ _ _ _ _ _ h1 ha hb

/-- **The cons of two call-free parts meets `LOKS`.** -/
theorem lokS_consP (lib : Lib) (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {fh ft : Noun}
    (hfh : ∃ x y, fh = C x y) (hpp : p.pure = true) (hqp : q.pure = true)
    (Mp : MinkEq lib P fh p) (Mq : MinkEq lib P ft q)
    (Sp : LOKS (S := S) (Map := Map) false lib env P fh p) (Sq : LOKS (S := S) (Map := Map) false lib env P ft q) :
    LOKS (S := S) (Map := Map) false lib env P (C fh ft) (Nomm.cons p q) := by
  refine ⟨fun {sup L th region g0 g1 nex} hc hr => ?_, fun hcount b0 d0 hu hcl0 hcb h1 h2 hta ht hsd hsl hlab hnd hed
    hfl hcs hce hr => lokS_consP_run lib env hfh hpp hqp Mp Mq Sp Sq hcount b0 d0 hu hcl0 hcb h1 h2 hta ht hsd hsl hlab
      hnd hed hfl hcs hce hr⟩
  have e : (runLC env sup (Nomm.cons p q) (CGoalL.next L th) region : CM Map (NextL S)) = (do
        let (hed, tel, o) ← splitL ⟨L, th⟩
        let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
        let nex2 ← runLC env sup q (CGoalL.next tel nexh.th) region
        let nex2 ← pastL env.cod nex2 p region
        let nex1 ← runLC env sup p (CGoalL.next nexh.laz nex2.th) region
        copyL nex1 nex2.laz) := rfl
  rw [e] at hr
  obtain ⟨⟨hed, tel, o⟩, g'', hs, hr⟩ := bind_some hr
  simp only at hr
  obtain ⟨nexh, gb, hph, hr⟩ := bind_some hr
  rw [pastL_pure _ _ hqp, pure_apply] at hph
  simp only [Option.some.injEq, Prod.mk.injEq] at hph
  obtain ⟨rfl, rfl⟩ := hph
  obtain ⟨nexq, g1', h3, hr⟩ := bind_some hr
  obtain ⟨nexq', g1'', hp2, hr⟩ := bind_some hr
  rw [pastL_pure _ _ hpp, pure_apply] at hp2
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  obtain ⟨nexp, g2, h4, hcp⟩ := bind_some hr
  unfold splitL at hs
  obtain ⟨o', g5, h5, hs⟩ := bind_some hs
  obtain ⟨⟨hd', tl'⟩, g6, h6, hs⟩ := bind_some hs
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hs
  have CS := clean_splitLoop h6 hc
  have cq := Sq.clean CS.2 h3
  have cp := Sp.clean CS.1 h4
  unfold copyL at hcp
  obtain ⟨oc, g7, h7, hcp⟩ := bind_some hcp
  obtain ⟨laz, g8, h8, hcp⟩ := bind_some hcp
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hcp
  obtain ⟨rfl, rfl⟩ := hcp
  exact clean_copyLazyL h8 cp cq

end Comp
end SkaModel
end Formalization
