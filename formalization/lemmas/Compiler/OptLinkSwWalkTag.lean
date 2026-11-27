import lemmas.Compiler.OptLinkSwNex

/-!
# `+switch-chains`: a tagged chain in the walk

```hoon
  ?:  (gte (lent cs) 4)
    ?>  ?=(^ cs)
    =/  s=@uvre  s.i.cs
    =/  d=@uvre  d.i.cs
    =/  top=@uwoo  y.i.cs
    =/  mis=@uwoo  miss:(rear `(list test)`cs)
    =/  ids=(list @uwoo)
      %+  weld  (turn t.cs |=(t=test y.t))
      (turn (snip `(list test)`cs) |=(t=test miss.t))
    =.  done  (~(gas in done) ids)
    =.  out  (roll ids |=([o=@uwoo acc=_out] (~(del by acc) o)))
    =/  cas=(list case)
      (cases (turn `(list test)`cs |=(t=test [c hit r]:t)))
    =/  node  (tree cas d mis ids out)
    =.  out  out.node
    =.  out  (~(put by out) top [~ [[%hed s d] body.node] fin.node])
    =/  b=blob  (~(got by blocks) i.topo)
    =.  out  (~(put by out) i.topo b(fin [%clq s [~ top] [~ mis]]))
    $(topo t.topo)
```

The branch runs on `[cs walk]` (`swWTag`), in three steps, each stated as
the subject it leaves: `wt_ids` (`s`, `d`, `top`, `mis`, `ids`: the subject
`wtS`), `wt_r` (`done`, `out` and `cas`), `wt_fin` (the tree, the two
`+put:by` and the next turn of the walk).  `sw_wtag`: **where `switchTag`
returns `(out', done')`, the branch is the next turn of the walk on `out'`
and a set related to `done'`**.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The model's values -/

/-- `mis`: the miss of the last test. -/
def tagMis (t0 : Opt.STest) (tl : List Opt.STest) : Nat := ((t0 :: tl).getLast (List.cons_ne_nil _ _)).miss

/-- `ids`: the yes sides of the tests but the first, then the misses but the last. -/
def tagIds (t0 : Opt.STest) (tl : List Opt.STest) : List Nat :=
  tl.map Opt.STest.y ++ (t0 :: tl).dropLast.map Opt.STest.miss

/-- The case of a test. -/
def toCase (t : Opt.STest) : Opt.SCase := ⟨t.c, t.hit, t.r⟩

/-- The subject after `ids`: `[ids [mis [top [d [s [cs walk]]]]]]`. -/
def wtS (t0 : Opt.STest) (tl : List Opt.STest) (WK : Noun) : Noun :=
  C (listNoun A (tagIds t0 tl)) (C (A (tagMis t0 tl)) (C (A t0.y) (C (A t0.d) (C (A t0.s)
    (C (listNoun stestN (t0 :: tl)) WK)))))

/-! ## `ids` -/

theorem wt_ids (BL T0 TOPO REV USES OUTN DONE NEX : Noun) (t0 : Opt.STest) (tl : List Opt.STest) :
    nock (C (listNoun stestN (t0 :: tl)) (swWk BL T0 TOPO REV USES OUTN DONE NEX)) swWTag
      = nock (wtS t0 tl (swWk BL T0 TOPO REV USES OUTN DONE NEX)) swWTR := by
  have hL := optC_layer2
  have hrear : nock (C rear.battery (C (listN ((t0 :: tl).map stestN)) layer2)) rear.battery
      = some (stestN ((t0 :: tl).getLast (List.cons_ne_nil _ _))) := by
    rw [rear_gate layer2 _ (by simp), List.getLast_map]
  have hsnip : nock (C snip.battery (C (listN ((t0 :: tl).map stestN)) layer2)) snip.battery
      = some (listN ((t0 :: tl).dropLast.map stestN)) := by
    rw [snip_gate, List.map_dropLast]
  have hty : ∀ (BS X : Noun), nock (C turn.battery (C (C (listN (tl.map stestN))
      (C (C (A 0) (A 222)) (C BS X))) layer2)) turn.battery = some (listN ((tl.map Opt.STest.y).map A)) := by
    intro BS X
    rw [turn_gate layer2 homoIn_layer2 _ BS X (fun x => (slot? 62 x).getD (A 0)) _ (fun x hx => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
      simp [nock_exec, stestN]), List.map_map, List.map_map]
    congr 3
  have htm : ∀ (BS X : Noun), nock (C turn.battery (C (C (listN ((t0 :: tl).dropLast.map stestN))
      (C (C (A 0) (A 110)) (C BS X))) layer2)) turn.battery
      = some (listN (((t0 :: tl).dropLast.map Opt.STest.miss).map A)) := by
    intro BS X
    rw [turn_gate layer2 homoIn_layer2 _ BS X (fun x => (slot? 30 x).getD (A 0)) _ (fun x hx => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
      simp [nock_exec, stestN]), List.map_map, List.map_map]
    congr 3
  have hweld : nock (C weld.battery (C (C (listN ((tl.map Opt.STest.y).map A))
      (listN (((t0 :: tl).dropLast.map Opt.STest.miss).map A))) layer2)) weld.battery
      = some (listNoun A (tagIds t0 tl)) := by
    rw [weld_gate_list, tagIds, listNoun_map_listN, List.map_append]
  have hcs : listNoun stestN (t0 :: tl) = listN ((t0 :: tl).map stestN) := listNoun_map_listN _ _
  unfold wtS tagMis
  rw [hcs]
  generalize (t0 :: tl).getLast (List.cons_ne_nil _ _) = LT at hrear ⊢
  generalize (t0 :: tl).dropLast = DL at hsnip htm hweld
  simp only [List.map_map] at hty htm hweld
  unfold swWk swSp swK9 swK8 swK7 swK6 swK5 swK4 swS8 swS7 swS6 swS5 swS4 swS3 swG
  generalize optC = OC at hL
  conv => lhs; arg 2; unfold swWTag
  simp only [List.map_cons, listN_cons, stestN] at hrear hsnip
  simp only [List.map_cons, listN_cons]
  simp [nock_exec, swWTIds, hL, rear.arm_at, rear_arm, hrear, snip.arm_at, snip_arm, hsnip, turn.arm_at, turn_arm,
    hty, htm, weld.arm_at, weld_arm, hweld, homoIn_layer2, homo_arm, stestN, tagMis]

/-! ## `done`, `out`, `cas` -/

/-- The gate that deletes a label from `out`. -/
theorem wt_delg (BL T0 TOPO REV USES OUTN DONE NEX : Noun) (t0 : Opt.STest) (tl : List Opt.STest) (o : Nat)
    (m : TreapMap mugF Blob) :
    nock (C swWTDelG (C (C (A o) (HoonMap.toNoun Blob.toNoun m))
      (wtS t0 tl (swWk BL T0 TOPO REV USES OUTN DONE NEX)))) swWTDelG
      = some (HoonMap.toNoun Blob.toNoun (HoonMap.del m o)) := by
  have hL := optC_layer2
  have hd := del_gate (mug := mugF) layer2 gorIn_morIn_layer2 (A o) _ _ (delF_hoonMap Blob.toNoun m o)
  unfold wtS swWk swSp swK9 swK8 swK7 swK6 swK5 swK4 swS8 swS7 swS6 swS5 swS4 swS3 swG
  generalize optC = OC at hL
  simp [nock_exec, swWTDelG, hL, by.arm_at, by_arm, by.del.arm_at, del_arm, hd]

theorem wt_r (BL T0 TOPO REV USES : Noun) (out : TreapMap mugF Blob) (DONE NEX : Noun) (done : List Nat)
    (hD : SawRel DONE done) (t0 : Opt.STest) (tl : List Opt.STest) (cas : List Opt.SCase)
    (hc : Opt.casesOf ((t0 :: tl).map toCase) = some cas) :
    ∃ DONE', SawRel DONE' (tagIds t0 tl ++ done) ∧
      nock (wtS t0 tl (swWk BL T0 TOPO REV USES (HoonMap.toNoun Blob.toNoun out) DONE NEX)) swWTR
        = nock (C (listNoun scaseN cas) (wtS t0 tl (swWk BL T0 TOPO REV USES
            (HoonMap.toNoun Blob.toNoun ((tagIds t0 tl).foldl HoonMap.del out)) DONE' NEX))) swWTFin := by
  obtain ⟨D', hg, hD'⟩ := saw_gas hD (tagIds t0 tl)
  refine ⟨D', hD', ?_⟩
  have hroll := roll_gate_list A (HoonMap.toNoun Blob.toNoun) (fun o m => some (HoonMap.del m o)) layer2 swWTDelG
    (A 0) (wtS t0 tl (swWk BL T0 TOPO REV USES (HoonMap.toNoun Blob.toNoun out) D' NEX)) (tagIds t0 tl) out
    (fun o _ m => by rw [wt_delg]; rfl)
  rw [foldlM_some, ← listNoun_map_listN] at hroll
  simp only [Option.map_some] at hroll
  have hcs := sw_cases BL T0 REV USES _ cas hc
  have hturn : ∀ (X : Noun), nock (C turn.battery (C (C (listNoun stestN (t0 :: tl))
      (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (A 0) (A 127))))))
        (C (C (A 0) (C (A 0) swTRBunt)) X))) layer2)) turn.battery
      = some (listNoun scaseN ((t0 :: tl).map toCase)) := by
    intro X
    rw [listNoun_map_listN stestN]
    rw [turn_gate layer2 homoIn_layer2 _ _ X (fun x => C ((slot? 6 x).getD (A 0))
      (C ((slot? 14 x).getD (A 0)) ((slot? 127 x).getD (A 0)))) _ (fun x hx => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
      simp [nock_exec, stestN]), List.map_map, listNoun_map_listN, List.map_map]
    congr 3
  have hL := optC_layer2
  unfold wtS at *
  unfold swWk swSp swK9 swK8 swK7 swK6 swK5 swK4 swS8 swS7 swS6 swS5 swS4 swS3 swG at *
  generalize optC = OC at hL hroll hcs
  generalize (t0 :: tl).map toCase = CL at hturn hcs
  conv => lhs; arg 2; unfold swWTR
  simp [nock_exec, swWTDel, swWTCas, hL, in.arm_at, in_arm, in.gas.arm_at, gas_in_arm, hg, roll.arm_at, roll_arm,
    hroll, turn.arm_at, turn_arm, homoIn_layer2, homo_arm, hturn, hcs]

/-! ## The tree, the head, the next turn -/

theorem wt_fin (bl : TreapMap mugF Blob) (T0 REV USES : Noun) (o : Nat) (rest : List Nat) (t0 : Opt.STest)
    (tl : List Opt.STest) (cas : List Opt.SCase) (out1 : TreapMap mugF Blob) (DONE NEX : Noun) (fuel : Nat)
    (nb : List Pole) (nf : Termin) (ids' : List Nat) (nout : TreapMap mugF Blob)
    (ht : Opt.stree t0.d (tagMis t0 tl) fuel cas (tagIds t0 tl) out1 = some (nb, nf, ids', nout))
    (b : Blob) (hb : HoonMap.get bl o = some b) :
    nock (C (listNoun scaseN cas) (wtS t0 tl (swWk (HoonMap.toNoun Blob.toNoun bl) T0 (listNoun A (o :: rest)) REV
      USES (HoonMap.toNoun Blob.toNoun out1) DONE NEX))) swWTFin
      = nock (swWk (HoonMap.toNoun Blob.toNoun bl) T0 (listNoun A rest) REV USES
          (HoonMap.toNoun Blob.toNoun (HoonMap.put (HoonMap.put nout t0.y ⟨[], Pole.hed t0.s t0.d :: nb, nf⟩) o
            { b with fin := Termin.clq t0.s ⟨[], t0.y⟩ ⟨[], tagMis t0 tl⟩ })) DONE NEX) swWalk := by
  have htr := sw_tree (HoonMap.toNoun Blob.toNoun bl) T0 REV USES t0.d (tagMis t0 tl) fuel cas (tagIds t0 tl) out1
    _ ht
  have hp1 := blocks_put nout t0.y ⟨[], Pole.hed t0.s t0.d :: nb, nf⟩
  have hp2 := blocks_put (HoonMap.put nout t0.y ⟨[], Pole.hed t0.s t0.d :: nb, nf⟩) o
    { b with fin := Termin.clq t0.s ⟨[], t0.y⟩ ⟨[], tagMis t0 tl⟩ }
  have hg := blocks_got bl o
  rw [hb] at hg
  have hL := optC_layer2
  obtain ⟨par, body, fin⟩ := b
  have hclq : (Termin.clq t0.s ⟨[], t0.y⟩ ⟨[], tagMis t0 tl⟩).toNoun
      = C (A Tag.clq) (C (A t0.s) (C (C (A 0) (A t0.y)) (C (A 0) (A (tagMis t0 tl))))) := rfl
  simp only [Blob.toNoun, listNoun, Pole.toNoun, hclq, Option.map_some, Tag.hed, Tag.clq] at hp1 hp2 hg
  unfold swTrG swTrN at htr
  unfold wtS swWk swSp swK9 swK8 swK7 swK6 swK5 swK4 swS8 swS7 swS6 swS5 swS4 swS3 swG at *
  generalize optC = OC at hL htr
  generalize HoonMap.toNoun Blob.toNoun bl = BL at hg htr ⊢
  generalize HoonMap.toNoun Blob.toNoun (HoonMap.put nout t0.y ⟨[], Pole.hed t0.s t0.d :: nb, nf⟩) = O2 at hp1 hp2
  conv => lhs; arg 2; unfold swWTFin
  simp [nock_exec, htr, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, hp1, hp2, by.got.arm_at, got_arm, hg,
    listNoun, Tag.hed, Tag.clq]

/-! ## The branch -/

/-- **A tagged chain in the walk**: where `switchTag` returns `(out', done')`,
the branch on `[cs walk]` is the next turn of the walk on the rest of `topo`,
`out'` and a set related to `done'`. -/
theorem sw_wtag (bl : TreapMap mugF Blob) (rev : TreapMap mugF (List Nat)) (T0 USES : Noun)
    (fuel o : Nat) (rest : List Nat) (out : TreapMap mugF Blob) (done : List Nat) (DONE NEX : Noun)
    (hD : SawRel DONE done) (cs : List Opt.STest) (out' : TreapMap mugF Blob) (done' : List Nat)
    (h : Opt.switchTag bl out fuel o cs done = some (out', done')) :
    ∃ DONE', SawRel DONE' done' ∧
      nock (C (listNoun stestN cs) (swWk (HoonMap.toNoun Blob.toNoun bl) T0 (listNoun A (o :: rest)) (jarN rev) USES
        (HoonMap.toNoun Blob.toNoun out) DONE NEX)) swWTag
        = nock (swWk (HoonMap.toNoun Blob.toNoun bl) T0 (listNoun A rest) (jarN rev) USES
            (HoonMap.toNoun Blob.toNoun out') DONE' NEX) swWalk := by
  match cs with
  | [] => simp [Opt.switchTag] at h
  | t0 :: tl =>
    simp only [Opt.switchTag] at h
    obtain ⟨cas, hc, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨nb, nf, ids', nout⟩, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, h⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hc' : Opt.casesOf ((t0 :: tl).map toCase) = some cas := hc
    obtain ⟨D', hD', hr⟩ := wt_r (HoonMap.toNoun Blob.toNoun bl) T0 (listNoun A (o :: rest)) (jarN rev) USES out
      DONE NEX done hD t0 tl cas hc'
    refine ⟨D', hD', ?_⟩
    rw [wt_ids, hr]
    exact wt_fin bl T0 (jarN rev) USES o rest t0 tl cas _ D' NEX fuel nb nf ids' nout ht b hb

end Compiler
end Formalization
