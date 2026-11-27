import lemmas.Ska.CompPastLS
import lemmas.Ska.CompNCLeaf

/-!
# The cons whose parts may call, under a flat lazy goal: `lokS_cons`

README Gaps 12.25.  `lokS_consP` (`CompConsLSRun.lean`) with parts that may
call.  Each part is call-free with `MinkEq` or hinted (as `UOKC.kind`).
The two `+past`s of the cons:

* behind the tail `q`: when `q` is hinted and the head's need asks
  something, the head's need is parked in a bond at a new block `g''.bo`
  (`hop o`), and the head runs under `mk bunt [] ((g''.bo, ofSure hed.sure)
  :: hed.bond)`, a flat goal with entries, through `LOKS`;
* behind the head `p`: when `p` is hinted and the tail's result asks
  something, `RunOKLS.past` (`CompPastLS.lean`).

`pairLS_ok` composes the parts in all four cases (its hypothesis `hjt`).
When the head's need is parked, the tail's jump must not be that block:
`JNewL` (the jump of a hinted run is a block the run made) is assumed for a
hinted tail.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The jump of a run is a block the run made**, under every lazy goal. -/
def JNewL (env : CallEnv) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    runLC (Map := Map) env sup nm (CGoalL.next L th) region g0 = some (nex, g1) → g0.bo ≤ nex.th.there

theorem lokS_cons_run (lib : Lib) (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {fh ft : Noun}
    (hfh : ∃ x y, fh = C x y)
    (Kp : (p.pure = true ∧ MinkEq lib P fh p) ∨ hinted env.cod p = some true)
    (Kq : (q.pure = true ∧ MinkEq lib P ft q) ∨ hinted env.cod q = some true)
    (Jq : hinted env.cod q = some true → JNewL (S := S) (Map := Map) env q)
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
  obtain ⟨nexq, g1', h3, hr⟩ := bind_some hr
  obtain ⟨nexq', g1'', hp2, hr⟩ := bind_some hr
  obtain ⟨nexp, g2, h4, hcp⟩ := bind_some hr
  -- the two `+past`s
  have pcase : (nexh = ⟨hed, jmp0 o⟩ ∧ gb = g'' ∧ ((∀ x, FitsS hed.sure x) ∨ TotalC lib P ft)) ∨
      (hinted env.cod q = some true ∧
        nexh = ⟨Lazy.mk Sure.bunt [] ((g''.bo, Lazy.mk hed.sure hed.fork []) :: hed.bond), jmp0 g''.bo⟩ ∧
        gb = (g''.emitted ⟨[], [], Termin.hop (jmp0 o)⟩).tagged g''.bo region) := by
    rcases Kq with ⟨qp, Mq⟩ | hq
    · rw [pastL_pure _ _ qp, pure_apply] at hph
      simp only [Option.some.injEq, Prod.mk.injEq] at hph
      exact Or.inl ⟨hph.1.symm, hph.2.symm, Or.inr (totalC_of_minkEq Mq)⟩
    · rcases pastL_hinted hq hph with ⟨x1, x2, en, es, _⟩ | ⟨x1, x2⟩
      · exact Or.inl ⟨x1, x2, Or.inl (fun x => fitsS_trivial en es x)⟩
      · exact Or.inr ⟨hq, x1, x2⟩
  have tcase : (nexq' = nexq ∧ g1'' = g1' ∧ ((∀ s, FitsS nexq.laz.sure s) ∨ TotalC lib P fh)) ∨
      (nexq' = ⟨Lazy.mk Sure.bunt [] ((g1'.bo, Lazy.mk nexq.laz.sure nexq.laz.fork []) :: nexq.laz.bond),
          jmp0 g1'.bo⟩ ∧
        g1'' = (g1'.emitted ⟨[], [], Termin.hop nexq.th⟩).tagged g1'.bo region) := by
    rcases Kp with ⟨pp, Mp⟩ | hp
    · rw [pastL_pure _ _ pp, pure_apply] at hp2
      simp only [Option.some.injEq, Prod.mk.injEq] at hp2
      exact Or.inl ⟨hp2.1.symm, hp2.2.symm, Or.inr (totalC_of_minkEq Mp)⟩
    · rcases pastL_hinted hp hp2 with ⟨x1, x2, en, es, _⟩ | ⟨x1, x2⟩
      · exact Or.inl ⟨x1, x2, Or.inl (fun x => fitsS_trivial en es x)⟩
      · exact Or.inr ⟨x1, x2⟩
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
  -- the head's park, as facts about `gb` and `nexh`
  have PK : Ext g'' gb ∧ GrowU g'' gb ∧ gb.cond = g''.cond ∧ gb.re = g''.re ∧ g''.bo ≤ gb.bo ∧
      gb.drop = false ∧ (∀ k, k < g''.bo → HoonMap.get gb.blocks k = HoonMap.get g''.blocks k) ∧
      1 ≤ nexh.th.there ∧ g0.bo ≤ nexh.th.there ∧ nexh.th.there < gb.bo ∧ nexh.th.args = [] := by
    rcases pcase with ⟨rfl, rfl, _⟩ | ⟨_, rfl, rfl⟩
    · exact ⟨Ext.refl _, GrowU.refl _, rfl, rfl, Nat.le_refl _, d'', fun _ _ => rfl, b0, Nat.le_refl _,
        by simp only [jmp0]; omega, rfl⟩
    · refine ⟨(ext_emit _ _).trans (ext_tagged _ _ _), (growU_emit (b := ⟨[], [], Termin.hop (jmp0 g0.bo)⟩)
        (fun j hj => by simp only [finJumps, List.mem_singleton] at hj; subst hj; simp only [jmp0]; omega) u'').trans
        (growU_tagged _ _ _), by rw [tagged_cond]; rfl, by simp [Gen.emitted], by simp [Gen.emitted],
        by simp [Gen.emitted, d''], fun k hk => ?_, by simp only [jmp0]; omega, by simp only [jmp0]; omega,
        by simp [jmp0, Gen.emitted], rfl⟩
      simp only [tagged_blocks, Gen.emitted, d'', Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
      rw [if_neg (by omega)]
  obtain ⟨hgb, hgbU, hgbc, hgbre, bgb, dgb, kgb, j1, j0, j2, ja⟩ := PK
  have ugb : UpBelow gb := hgbU.up u''
  have clgb : Clear gb := cl''.growU hgbU
  have cbgb : CondBelow gb := (condFresh_of_eq (by omega) hgbc).below cb''
  have HG : (nexh.th = jmp0 g0.bo ∧ nexh.laz = (mk sH [] (bh.filter fun e => !(lazyEmpty e.2))) ∧
        ((∀ x, FitsS (mk sH [] (bh.filter fun e => !(lazyEmpty e.2))).sure x) ∨ TotalC lib P ft)) ∨
      (nexh.th = jmp0 g''.bo ∧
        nexh.laz = Lazy.mk Sure.bunt [] ((g''.bo, ofSure (mk sH [] (bh.filter fun e => !(lazyEmpty e.2))).sure) :: (mk sH [] (bh.filter fun e => !(lazyEmpty e.2))).bond) ∧
        g''.bo < gb.bo ∧ HoonMap.get gb.blocks g''.bo = some ⟨[], [], Termin.hop (jmp0 g0.bo)⟩ ∧
        hinted env.cod q = some true) := by
    rcases pcase with ⟨rfl, rfl, hf⟩ | ⟨hq, rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl, hf⟩
    · refine Or.inr ⟨rfl, rfl, by simp [Gen.emitted], ?_, hq⟩
      simp only [tagged_blocks, Gen.emitted, d'', Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  -- the tail
  have hcq : sixCount q ≤ 255 := by simp only [sixCount] at hcount; omega
  have hcp' : sixCount p ≤ 255 := by simp only [sixCount] at hcount; omega
  obtain ⟨⟨Qt, Rq⟩, jq1, jq2, fq, cqE⟩ := Sq.run (sup := sup) (region := region) (L := (mk sT [] (bt.filter fun e => !(lazyEmpty e.2))))
    (th := nexh.th) hcq (by omega) dgb ugb clgb cbgb j1 j2 ja
    (fun hm => by
      rw [eT] at hm
      obtain ⟨e, he, ee⟩ := List.mem_map.mp hm
      have := labL _ (htl e he); omega)
    Dt (fun x hx => ⟨by have := lt2' _ Mt x hx; omega, by rw [hgbc]; exact nk'' x (by
      rcases Mt x hx with a | a
      · exact Or.inl a
      · exact Or.inr (Or.inr a.1))⟩)
    (fun e he => by
      rw [eT] at he
      obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE false e he
      obtain ⟨hlt, B, th', hb⟩ := hlab eb (by rw [eL]; exact heb)
      exact ⟨by omega, _, th', by rw [kgb _ (by omega)]; exact PBP.blk (by rw [E2.2.2.2 _ hlt]; exact hb)⟩)
    (by rw [eT]; exact htn)
    (fun e he => by
      rw [eT] at he
      obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE false e he
      refine ⟨SA.dt, fun x hx => ?_⟩
      rw [hgbc]
      rcases SA.mt x hx with a | a
      · exact ⟨by have := ((hed eb (by rw [eL]; exact heb)).2 x a).1; omega, nk'' x (Or.inr (Or.inl ⟨eb, heb, a⟩))⟩
      · exact ⟨by omega, nk'' x (Or.inr (Or.inr (by omega)))⟩)
    fT CS.2
    (fun e he => by
      rw [eT] at he
      obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE false e he
      exact SA.ct) h3
  have bq0 := Rq.bo
  -- the tail with its `+past`
  have Rq' : RunOKLS (Map := Map) lib P ft (mk sT [] (bt.filter fun e => !(lazyEmpty e.2))) nexh.th Qt false gb g1'' nexq' := by
    rcases tcase with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl⟩
    · exact Rq
    · exact Rq.past (fun r hr => by have := lt2' _ Mt r hr; omega) (fun e he => by
        rw [eT] at he; have := labL _ (htl e he); omega) ja (Rq.drop.trans dgb) (Rq.grow.up ugb) region
  have fq' : Flat nexq'.laz ∧ (∀ e ∈ entries nexq'.laz, Clean e.2.sure.ned) ∧ Clean nexq'.laz.sure.ned ∧
      ((∀ s, FitsS nexq'.laz.sure s) ∨ TotalC lib P fh) := by
    rcases tcase with ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl⟩
    · exact ⟨fq, cqE, Sq.clean (L := (mk sT [] (bt.filter fun e => !(lazyEmpty e.2)))) CS.2 h3, hf⟩
    · have fl : Flat (Lazy.mk (Sure.bunt : Sure S) [] ((g1'.bo, Lazy.mk nexq.laz.sure nexq.laz.fork []) ::
          nexq.laz.bond)) := flat_mk (fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · show Lazy.mk nexq.laz.sure nexq.laz.fork [] = ofSure nexq.laz.sure
          rw [fq.1]; rfl
        · exact fq.2 e he)
      refine ⟨fl, fun e he => ?_, trivial, Or.inl (fun s => fitsS_bunt s)⟩
      rw [entries_flat fl] at he
      rcases List.mem_cons.mp he with rfl | he
      · exact Sq.clean (L := (mk sT [] (bt.filter fun e => !(lazyEmpty e.2)))) CS.2 h3
      · exact cqE e (by rw [entries_flat fq]; exact he)
  have JT : nexq'.th.there ∉ (entries nexh.laz).map Prod.fst ∧ g0.bo ≤ nexq'.th.there := by
    have tq : g0.bo ≤ nexq'.th.there ∧
        (hinted env.cod q = some true → gb.bo ≤ nexq'.th.there) := by
      rcases tcase with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl⟩
      · refine ⟨?_, fun hq => Jq hq h3⟩
        rcases jq2 with a | a
        · rw [a]; exact j0
        · omega
      · simp only [jmp0]; exact ⟨by omega, fun _ => by omega⟩
    refine ⟨fun hm => ?_, tq.1⟩
    obtain ⟨e, he, ee⟩ := List.mem_map.mp hm
    have fLh : Flat nexh.laz := by
      rcases HG with ⟨-, e1, -⟩ | ⟨-, e1, -⟩ <;> rw [e1]
      · exact fH
      · exact flat_mk (fun e he => by
          rcases List.mem_cons.mp he with rfl | he
          · rfl
          · exact fbh e (List.mem_filter.mp he).1)
    rw [entries_flat fLh] at he
    rcases HG with ⟨-, e1, -⟩ | ⟨-, e1, e3, -, hq⟩
    · rw [e1] at he; have := labL _ (hhl e he); have := tq.1; omega
    · rw [e1] at he
      rcases List.mem_cons.mp he with rfl | he
      · have := tq.2 hq; simp at ee; omega
      · have := labL _ (hhl e he); have := tq.1; omega
  -- the head's goal
  have fLh : Flat nexh.laz := by
    rcases HG with ⟨-, e1, -⟩ | ⟨-, e1, -⟩ <;> rw [e1]
    · exact fH
    · exact flat_mk (fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · rfl
        · exact fbh e (List.mem_filter.mp he).1)
  have eLh := entries_flat fLh
  have mH : ∀ e ∈ entries nexh.laz, e ∈ entries (mk sH [] (bh.filter fun e => !(lazyEmpty e.2))) ∨
      (e = (g''.bo, ofSure sH) ∧ g''.bo < gb.bo ∧
        HoonMap.get gb.blocks g''.bo = some ⟨[], [], Termin.hop (jmp0 g0.bo)⟩) := fun e he => by
    rw [eLh] at he
    rcases HG with ⟨-, e1, -⟩ | ⟨-, e1, e2, e3, -⟩
    · rw [e1] at he; exact Or.inl (by rw [eH]; exact he)
    · rw [e1] at he
      rcases List.mem_cons.mp he with rfl | he
      · exact Or.inr ⟨rfl, e2, e3⟩
      · exact Or.inl (by rw [eH]; exact he)
  have sLh : nexh.laz.sure = sH ∨ nexh.laz.sure = Sure.bunt := by
    rcases HG with ⟨-, e1, -⟩ | ⟨-, e1, -⟩ <;> rw [e1]
    · exact Or.inl rfl
    · exact Or.inr rfl
  have nLh : ((entries nexh.laz).map Prod.fst).Nodup := by
    rw [eLh]
    rcases HG with ⟨-, e1, -⟩ | ⟨-, e1, -⟩ <;> rw [e1]
    · exact hhn
    · refine List.nodup_cons.mpr ⟨fun hm => ?_, hhn⟩
      obtain ⟨e, he, ee⟩ := List.mem_map.mp hm
      have ee' : e.1 = g''.bo := ee
      have := labL _ (hhl e he); omega
  have cLh : Clean nexh.laz.sure.ned := by
    rcases sLh with e | e <;> rw [e]
    · exact CS.1
    · trivial
  -- the head
  have u1 : UpBelow g1'' := Rq'.grow.up ugb
  have cl1 : Clear g1'' := clgb.growU Rq'.grow
  have cb1 : CondBelow g1'' := Rq'.cfr.below cbgb
  have hq1 := Rq'.lo
  have hq2 := Rq'.hi
  have rq := Rq'.re
  have bq := Rq'.bo
  have regH : ∀ x, NMem sH.ned x → x < g1''.re ∧ HoonMap.get g1''.cond x = Option.none := fun x hx =>
    ⟨by have := lt2' _ Mh x hx; omega, by
      rw [Rq'.cfr.get_lt (by have := lt2' _ Mh x hx; omega), hgbc]
      exact nk'' x (by
        rcases Mh x hx with a | a
        · exact Or.inl a
        · exact Or.inr (Or.inr a.1))⟩
  obtain ⟨⟨Qh, Rp⟩, jp1, jp2, fp, cpE⟩ := Sp.run (sup := sup) (region := region) (L := nexh.laz) hcp' (by omega)
    (Rq'.drop.trans dgb) u1 cl1 cb1 hq1 hq2 (nextArgs_nil Rq'.ent ja) JT.1
    (by rcases sLh with e | e <;> rw [e]
        · exact Dh
        · trivial)
    (fun x hx => by
      rcases sLh with e | e <;> rw [e] at hx
      · exact regH x hx
      · simp [Sure.bunt, NMem] at hx)
    (fun e he => by
      rcases mH e he with he | ⟨rfl, lt, hb⟩
      · rw [eH] at he
        obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE true e he
        obtain ⟨hlt, B, th', hb⟩ := hlab eb (by rw [eL]; exact heb)
        have hb'' : HoonMap.get gb.blocks eb.1 = some ⟨[], PB eb.1 ++ B, Termin.hop th'⟩ := by
          rw [kgb _ (by omega)]; exact PBP.blk (by rw [E2.2.2.2 _ hlt]; exact hb)
        refine ⟨by omega, ?_⟩
        by_cases hm : eb.1 ∈ (entries (mk sT [] (bt.filter fun e => !(lazyEmpty e.2)))).map Prod.fst
        · obtain ⟨e0, h0, e0e⟩ := List.mem_map.mp hm
          obtain ⟨F0, hF0, -⟩ := Rq'.front e0 h0
          rw [← e0e] at hb''
          exact ⟨_, th', by rw [← e0e]; exact hF0 _ _ hb''⟩
        · exact ⟨_, th', by rw [Rq'.keep _ (by omega) hm]; exact hb''⟩
      · refine ⟨by omega, [], jmp0 g0.bo, ?_⟩
        rw [Rq'.keep _ lt (fun hm => by
          rw [eT] at hm
          obtain ⟨e, he, ee⟩ := List.mem_map.mp hm
          have := labL _ (htl e he); omega)]
        exact hb)
    nLh
    (fun e he => by
      rcases mH e he with he | ⟨rfl, -, -⟩
      · rw [eH] at he
        obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE true e he
        refine ⟨SA.dh, fun x hx => ?_⟩
        rcases SA.mh x hx with a | a
        · have := ((hed eb (by rw [eL]; exact heb)).2 x a).1
          exact ⟨by omega, by rw [Rq'.cfr.get_lt (by omega), hgbc]; exact nk'' x (Or.inr (Or.inl ⟨eb, heb, a⟩))⟩
        · exact ⟨by omega, by rw [Rq'.cfr.get_lt (by omega), hgbc]; exact nk'' x (Or.inr (Or.inr (by omega)))⟩
      · exact ⟨Dh, regH⟩)
    fLh cLh
    (fun e he => by
      rcases mH e he with he | ⟨rfl, -, -⟩
      · rw [eH] at he
        obtain ⟨eb, heb, sh, st, SA, rfl⟩ := halfE true e he
        exact SA.ch
      · exact CS.1) h4
  -- the copy
  obtain ⟨n, g3', r, hc, hM, rfl⟩ := copyL_flat' fp fq'.1 hcp
  obtain ⟨R, hth, eth, fR, cR, lR⟩ := pairLS_ok (Fin := fun _ _ _ x y r => r = Tone.zero (C x y))
    (FinB := fun _ _ x y r => r = Tone.zero (C x y)) (hed := mk sH [] (bh.filter fun e => !(lazyEmpty e.2)))
    (tel := mk sT [] (bt.filter fun e => !(lazyEmpty e.2))) Mf Mb (fun _ _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    hfl hnL hkg
    (fun e he => ⟨(hlab e (by rw [eL]; exact he)).1, (hlab e (by rw [eL]; exact he)).2,
      (hed e (by rw [eL]; exact he)).1, (hed e (by rw [eL]; exact he)).2⟩)
    hok E2 G2U c2 hcb Mh Mt Dht PBP PBo fH fT SPL hhl htl hhn htn hgb hgbU hgbc hgbre
    (HG.imp id (fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)) fq'.2.2.2
    Rq' Rp fq'.1 fp fq'.2.1 cpE fq'.2.2.1 (Sp.clean (L := nexh.laz) cLh h4) hc hM hu d0 hfix
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
  have hthe : (pairRes n r nexq'.laz.bond nexp.laz.bond).th = n.th := rfl
  rw [hthe, eth] at ee
  simp only [jmp0] at ee
  omega

/-! ## The sure part stays clean -/


/-- **The cons whose parts may call meets `LOKS`**: each part call-free with
`MinkEq` or hinted, with `LOKS`, and `JNewL` of a hinted tail. -/
theorem lokS_cons (lib : Lib) (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {fh ft : Noun}
    (hfh : ∃ x y, fh = C x y)
    (Kp : (p.pure = true ∧ MinkEq lib P fh p) ∨ hinted env.cod p = some true)
    (Kq : (q.pure = true ∧ MinkEq lib P ft q) ∨ hinted env.cod q = some true)
    (Jq : hinted env.cod q = some true → JNewL (S := S) (Map := Map) env q)
    (Sp : LOKS (S := S) (Map := Map) false lib env P fh p) (Sq : LOKS (S := S) (Map := Map) false lib env P ft q) :
    LOKS (S := S) (Map := Map) false lib env P (C fh ft) (Nomm.cons p q) := by
  refine ⟨fun {sup L th region g0 g1 nex} hc hr => ?_, fun hcount b0 d0 hu hcl0 hcb h1 h2 hta ht hsd hsl hlab hnd hed
    hfl hcs hce hr => lokS_cons_run lib env hfh Kp Kq Jq Sp Sq hcount b0 d0 hu hcl0 hcb h1 h2 hta ht hsd hsl hlab
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
  obtain ⟨nexq, g1', h3, hr⟩ := bind_some hr
  obtain ⟨nexq', g1'', hp2, hr⟩ := bind_some hr
  obtain ⟨nexp, g2, h4, hcp⟩ := bind_some hr
  unfold splitL at hs
  obtain ⟨o', g5, h5, hs⟩ := bind_some hs
  obtain ⟨⟨hd', tl'⟩, g6, h6, hs⟩ := bind_some hs
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hs
  have CS := clean_splitLoop h6 hc
  -- the head's goal: `hed` or the bunt of `+past`
  have ch : Clean nexh.laz.sure.ned := by
    rcases Kq with ⟨qp, -⟩ | hq
    · rw [pastL_pure _ _ qp, pure_apply] at hph
      simp only [Option.some.injEq, Prod.mk.injEq] at hph
      rw [← hph.1]; exact CS.1
    · rcases pastL_hinted hq hph with ⟨x1, -⟩ | ⟨x1, -⟩
      · rw [x1]; exact CS.1
      · rw [x1]; trivial
  have cq := Sq.clean CS.2 h3
  have cq' : Clean nexq'.laz.sure.ned := by
    rcases Kp with ⟨pp, -⟩ | hp
    · rw [pastL_pure _ _ pp, pure_apply] at hp2
      simp only [Option.some.injEq, Prod.mk.injEq] at hp2
      rw [← hp2.1]; exact cq
    · rcases pastL_hinted hp hp2 with ⟨x1, -⟩ | ⟨x1, -⟩
      · rw [x1]; exact cq
      · rw [x1]; trivial
  have cp := Sp.clean ch h4
  unfold copyL at hcp
  obtain ⟨oc, g7, h7, hcp⟩ := bind_some hcp
  obtain ⟨laz, g8, h8, hcp⟩ := bind_some hcp
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hcp
  obtain ⟨rfl, rfl⟩ := hcp
  exact clean_copyLazyL h8 cp cq'


/-! ## `[0 0]` -/

/-- **`[0 0]` meets `LOKS`**: the block of `+bomb` crashes, no op at any
goal entry, no product (`frontS_false`). -/
theorem lokS_n00 (lib : Lib) (env : CallEnv) {P : Noun → Prop} {f : Noun}
    (M : MinkEq lib P f (Nomm.n0 0)) : LOKS (S := S) (Map := Map) false lib env P f (Nomm.n0 0) := by
  refine ⟨(lokc_n00 (S := S) (Map := Map) lib env M).clean, fun {sup L th region g0 g1 nex} _ b0 d0 hu hcl hcb
    h1 h2 hta ht hsd hsl hlab hnd hed hfl _ hce hr => ?_⟩
  rw [runLC_eq env _ rfl, runL_n00_next] at hr
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  have e0 : entries (ofSure (Sure.bunt : Sure S)) = [] := entries_ofSure _
  have RB := ((runOKL_n00 (Map := Map) lib (L := L) (th := th) b0 d0 hu (fun e he => (hlab e he).1)
    (fun _ => A 0)).toLC M).toB (P := P)
  have FS : FrontsS (Map := Map) (pureWit (Nomm.n0 0) (fun _ => Need.none) (fun _ => A 0)) false g0
      (g0.emitted ⟨[], [], Termin.bom (some th.there)⟩) L ⟨ofSure Sure.bunt, jmp0 g0.bo⟩ := by
    intro e he
    have hlt := (hlab e he).1
    refine ⟨[], fun B fin hb => ?_, fun cf hcf => Or.inr ⟨(by rw [e0]; exact fun h => (by cases h)), ?_⟩⟩
    · simp only [Gen.emitted, d0, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put, List.nil_append]
      rw [if_neg (by omega)]; exact hb
    · exact frontS_false (fun s v d w hq => by
        obtain ⟨hv, _, _⟩ := hq
        rw [pureEval_n00] at hv; cases hv)
  refine ⟨⟨_, { toRunOKLB := RB, fs := FS }⟩, (by rw [e0]; exact fun h => (by cases h)), Or.inr (Nat.le_refl _),
    ⟨rfl, fun e he => (by cases he)⟩, fun e he => (by rw [e0] at he; cases he)⟩

end Comp
end SkaModel
end Formalization
