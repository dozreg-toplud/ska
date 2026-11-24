import lemmas.Compiler.OptLinkSwWalkTag

/-!
# `+switch-chains`: a plain chain in the walk

```hoon
  =/  ps=(list [p=@uwoo t=plain])  (plains-of i.topo)
  ?:  (lth (lent ps) 4)  $(topo t.topo)
  ?>  ?=(^ ps)
  =/  d=@uvre  d.t.i.ps
  =/  mis=@uwoo  miss.t:(rear `(list [p=@uwoo t=plain])`ps)
  =/  old=(list @uwoo)  (turn t.ps |=([p=@uwoo *] p))
  =.  done  (~(gas in done) old)
  =.  out  (roll old |=([o=@uwoo acc=_out] (~(del by acc) o)))
  =/  cas=(list case)
    (cases (turn `(list [p=@uwoo t=plain])`ps |=([* t=plain] [c hit r]:t)))
  =/  ned=@ud  (sub (mul 2 (lent cas)) 2)
  =^  ids=(list @uwoo)  nex
    =/  ids=(list @uwoo)  (scag ned old)
    |-  ^-  [(list @uwoo) @uwoo]
    ?:  (gte (lent ids) ned)  [ids nex]
    $(ids [nex ids], nex `@uwoo`+(nex))
  =/  node  (tree cas d mis ids out)
  =.  out  out.node
  =/  b=blob  (~(got by blocks) i.topo)
  =/  bod=(list pole)
    %+  skip  body.b
    |=(op=pole &(?=([%imm *] op) =(d.op r.t.i.ps)))
  =.  out  (~(put by out) i.topo [par.b (weld bod body.node) fin.node])
  $(topo t.topo)
```

The branch after `?>` (`swWPB`, on `[ps [cs walk]]`) in four steps, each
stated as the subject it leaves: `wp_old` (`d`, `mis`, `old`: the subject
`wpS1`), `wp_r` (`done`, `out`, `cas`, `ned`), `wp_ids` (the trap of the new
labels, `freshIds`, and `nex` put back in the walk), `wp_node` (the tree,
the head, the next turn).  `sw_wplain`: **where `switchPlain` returns
`(out', done', nex')`, the branch is the next turn of the walk on `out'`, a
set related to `done'` and `nex'`**.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The model's values -/

/-- `mis`: the miss of the last test. -/
def plMis (p0 : Nat × Opt.SPlain) (pl : List (Nat × Opt.SPlain)) : Nat :=
  ((p0 :: pl).getLast (List.cons_ne_nil _ _)).2.miss

/-- The case of a plain test. -/
def toCaseP (t : Nat × Opt.SPlain) : Opt.SCase := ⟨t.2.c, t.2.hit, t.2.r⟩

/-- The subject after `old`: `[old [mis [d [ps [cs walk]]]]]`. -/
def wpS1 (p0 : Nat × Opt.SPlain) (pl : List (Nat × Opt.SPlain)) (CS WK : Noun) : Noun :=
  C (listNoun A (pl.map Prod.fst)) (C (A (plMis p0 pl)) (C (A p0.2.d) (C (listNoun spN (p0 :: pl)) (C CS WK))))

/-! ## `d`, `mis`, `old` -/

theorem wp_old (BL T0 TOPO REV USES OUTN DONE NEX CS : Noun) (p0 : Nat × Opt.SPlain)
    (pl : List (Nat × Opt.SPlain)) :
    nock (C (listNoun spN (p0 :: pl)) (C CS (swWk BL T0 TOPO REV USES OUTN DONE NEX))) swWPB
      = nock (wpS1 p0 pl CS (swWk BL T0 TOPO REV USES OUTN DONE NEX)) swWPR := by
  have hL := optC_layer2
  have hrear : nock (C rear.battery (C (listN ((p0 :: pl).map spN)) layer2)) rear.battery
      = some (spN ((p0 :: pl).getLast (List.cons_ne_nil _ _))) := by
    rw [rear_gate layer2 _ (by simp), List.getLast_map]
  have hturn : ∀ (X : Noun), nock (C turn.battery (C (C (listN (pl.map spN))
      (C (C (A 0) (A 12)) (C (C (A 0) (A 0)) X))) layer2)) turn.battery = some (listN ((pl.map Prod.fst).map A)) := by
    intro X
    rw [turn_gate layer2 homoIn_layer2 _ _ X (fun x => (slot? 2 x).getD (A 0)) _ (fun x hx => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
      simp [nock_exec, spN]), List.map_map, List.map_map]
    congr 3
  have hcs : listNoun spN (p0 :: pl) = listN ((p0 :: pl).map spN) := listNoun_map_listN _ _
  have hold : listNoun A (pl.map Prod.fst) = listN ((pl.map Prod.fst).map A) := listNoun_map_listN _ _
  unfold wpS1 plMis
  rw [hcs, hold]
  generalize (p0 :: pl).getLast (List.cons_ne_nil _ _) = LT at hrear ⊢
  simp only [List.map_cons, listN_cons, spN, splainN] at hrear
  simp only [List.map_cons, listN_cons]
  unfold swWk swSp swK9 swK8 swK7 swK6 swK5 swK4 swS8 swS7 swS6 swS5 swS4 swS3 swG
  generalize optC = OC at hL
  generalize (pl.map Prod.fst).map A = OL at hturn ⊢
  conv => lhs; arg 2; unfold swWPB
  simp [nock_exec, hL, rear.arm_at, rear_arm, hrear, turn.arm_at, turn_arm, hturn, homoIn_layer2, homo_arm,
    spN, splainN]

/-! ## `done`, `out`, `cas`, `ned` -/

theorem wp_delg (BL T0 TOPO REV USES OUTN DONE NEX CS : Noun) (p0 : Nat × Opt.SPlain)
    (pl : List (Nat × Opt.SPlain)) (o : Nat) (m : TreapMap mugF Blob) :
    nock (C swWPDelG (C (C (A o) (HoonMap.toNoun Blob.toNoun m))
      (wpS1 p0 pl CS (swWk BL T0 TOPO REV USES OUTN DONE NEX)))) swWPDelG
      = some (HoonMap.toNoun Blob.toNoun (HoonMap.del m o)) := by
  have hL := optC_layer2
  have hd := del_gate (mug := mugF) layer2 gorIn_morIn_layer2 (A o) _ _ (delF_hoonMap Blob.toNoun m o)
  unfold wpS1 swWk swSp swK9 swK8 swK7 swK6 swK5 swK4 swS8 swS7 swS6 swS5 swS4 swS3 swG
  generalize optC = OC at hL
  simp [nock_exec, swWPDelG, hL, by.arm_at, by_arm, by.del.arm_at, del_arm, hd]

theorem wp_r (BL T0 TOPO REV USES : Noun) (out : TreapMap mugF Blob) (DONE NEX CS : Noun) (done : List Nat)
    (hD : SawRel DONE done) (p0 : Nat × Opt.SPlain) (pl : List (Nat × Opt.SPlain)) (cas : List Opt.SCase)
    (hc : Opt.casesOf ((p0 :: pl).map toCaseP) = some cas) (hne : cas ≠ []) :
    ∃ DONE', SawRel DONE' (pl.map Prod.fst ++ done) ∧
      nock (wpS1 p0 pl CS (swWk BL T0 TOPO REV USES (HoonMap.toNoun Blob.toNoun out) DONE NEX)) swWPR
        = nock (C (A (2 * cas.length - 2)) (C (listNoun scaseN cas) (wpS1 p0 pl CS (swWk BL T0 TOPO REV USES
            (HoonMap.toNoun Blob.toNoun ((pl.map Prod.fst).foldl HoonMap.del out)) DONE' NEX)))) swWPFin := by
  obtain ⟨D', hg, hD'⟩ := saw_gas hD (pl.map Prod.fst)
  refine ⟨D', hD', ?_⟩
  have hroll := roll_gate_list A (HoonMap.toNoun Blob.toNoun) (fun o m => some (HoonMap.del m o)) layer2 swWPDelG
    (A 0) (wpS1 p0 pl CS (swWk BL T0 TOPO REV USES (HoonMap.toNoun Blob.toNoun out) D' NEX)) (pl.map Prod.fst) out
    (fun o _ m => by rw [wp_delg]; rfl)
  rw [foldlM_some, ← listNoun_map_listN] at hroll
  simp only [Option.map_some] at hroll
  have hcs := sw_cases BL T0 REV USES _ cas hc
  have hturn : ∀ (X : Noun), nock (C turn.battery (C (C (listNoun spN (p0 :: pl))
      (C (C (A 7) (C (C (A 0) (A 13)) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (A 0) (A 31))))))
        (C (C (A 0) swTRBunt) X))) layer2)) turn.battery
      = some (listNoun scaseN ((p0 :: pl).map toCaseP)) := by
    intro X
    rw [listNoun_map_listN spN]
    rw [turn_gate layer2 homoIn_layer2 _ _ X (fun x => C ((slot? 6 ((slot? 3 x).getD (A 0))).getD (A 0))
      (C ((slot? 14 ((slot? 3 x).getD (A 0))).getD (A 0))
        ((slot? 31 ((slot? 3 x).getD (A 0))).getD (A 0)))) _ (fun x hx => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
      simp [nock_exec, spN, splainN]), List.map_map, listNoun_map_listN, List.map_map]
    congr 3
  have hlen := lent_gate layer2 (cas.map scaseN)
  rw [← listNoun_map_listN, List.length_map] at hlen
  have hmul := mul_gate layer1 arith_layer1.1 2 cas.length
  have hsub := sub_gate layer1 decIn_layer1 2 (2 * cas.length) (by
    cases cas with
    | nil => exact absurd rfl hne
    | cons _ _ => simp; omega)
  have hL := optC_layer2
  have hL1 := optC_layer1
  unfold wpS1 at *
  unfold swWk swSp swK9 swK8 swK7 swK6 swK5 swK4 swS8 swS7 swS6 swS5 swS4 swS3 swG at *
  generalize optC = OC at hL hL1 hroll hcs
  generalize (p0 :: pl).map toCaseP = CL at hturn hcs
  conv => lhs; arg 2; unfold swWPR
  simp [nock_exec, swWPDel, swWPCas, swWPNed, hL, hL1, in.arm_at, in_arm, in.gas.arm_at, gas_in_arm, hg,
    roll.arm_at, roll_arm, hroll, turn.arm_at, turn_arm, homoIn_layer2, homo_arm, hturn, hcs, lent.arm_at, lent_arm,
    hlen, mul.arm_at, mul_arm, hmul, sub.arm_at, sub_arm, hsub]

/-! ## The new labels -/

theorem wp_idt (BL T0 TOPO REV USES OUTN DONE CS : Noun) (p0 : Nat × Opt.SPlain) (pl : List (Nat × Opt.SPlain))
    (ned : Nat) (CASN : Noun) : ∀ (f : Nat) (ids : List Nat) (nex : Nat), ned ≤ ids.length + f →
    nock (C swWPIdT (C (listNoun A ids) (C (A ned) (C CASN (wpS1 p0 pl CS
      (swWk BL T0 TOPO REV USES OUTN DONE (A nex))))))) swWPIdT
      = some (C (listNoun A (Opt.freshIds f ids ned nex).1) (A (Opt.freshIds f ids ned nex).2)) := by
  have hL := optC_layer2
  have hL1 := optC_layer1
  intro f
  induction f with
  | zero =>
    intro ids nex hle
    have hlen := lent_gate layer2 (ids.map A)
    rw [← listNoun_map_listN, List.length_map] at hlen
    have hg := gte_gate layer1 gteIn_layer1 ids.length ned
    unfold wpS1 swWk swSp swK9 swK8 swK7 swK6 swK5 swK4 swS8 swS7 swS6 swS5 swS4 swS3 swG
    generalize optC = OC at hL hL1
    conv => lhs; arg 2; unfold swWPIdT
    have hle' : ned ≤ ids.length := by omega
    simp [nock_exec, hL, hL1, lent.arm_at, lent_arm, hlen, gte.arm_at, gte_arm, hg, hle', loob, Opt.freshIds]
  | succ f ih =>
    intro ids nex hle
    have hlen := lent_gate layer2 (ids.map A)
    rw [← listNoun_map_listN, List.length_map] at hlen
    have hg := gte_gate layer1 gteIn_layer1 ids.length ned
    by_cases hc : ned ≤ ids.length
    · unfold wpS1 swWk swSp swK9 swK8 swK7 swK6 swK5 swK4 swS8 swS7 swS6 swS5 swS4 swS3 swG
      generalize optC = OC at hL hL1
      conv => lhs; arg 2; unfold swWPIdT
      simp [nock_exec, hL, hL1, lent.arm_at, lent_arm, hlen, gte.arm_at, gte_arm, hg, hc, loob, Opt.freshIds]
    · have ih' := ih (nex :: ids) (nex + 1) (by simp; omega)
      have hf : Opt.freshIds (f + 1) ids ned nex = Opt.freshIds f (nex :: ids) ned (nex + 1) := by
        simp only [Opt.freshIds]; rw [if_neg (by omega)]
      rw [hf]
      unfold wpS1 swWk swSp swK9 swK8 swK7 swK6 swK5 swK4 swS8 swS7 swS6 swS5 swS4 swS3 swG at *
      simp only [listNoun] at ih'
      generalize optC = OC at hL hL1 ih'
      generalize Opt.freshIds f (nex :: ids) ned (nex + 1) = R at ih' ⊢
      conv => lhs; arg 2; unfold swWPIdT
      simp [nock_exec, hL, hL1, lent.arm_at, lent_arm, hlen, gte.arm_at, gte_arm, hg, hc, loob, ih', listNoun]

theorem wp_ids (BL T0 TOPO REV USES OUTN DONE CS : Noun) (p0 : Nat × Opt.SPlain) (pl : List (Nat × Opt.SPlain))
    (ned nex : Nat) (CASN : Noun) :
    nock (C (A ned) (C CASN (wpS1 p0 pl CS (swWk BL T0 TOPO REV USES OUTN DONE (A nex))))) swWPFin
      = nock (C (listNoun A (Opt.freshIds (ned + 1) ((pl.map Prod.fst).take ned) ned nex).1) (C (A ned) (C CASN
          (wpS1 p0 pl CS (swWk BL T0 TOPO REV USES OUTN DONE
            (A (Opt.freshIds (ned + 1) ((pl.map Prod.fst).take ned) ned nex).2)))))) swWPNode := by
  have hidt := wp_idt BL T0 TOPO REV USES OUTN DONE CS p0 pl ned CASN (ned + 1) ((pl.map Prod.fst).take ned) nex
    (by omega)
  have hscag := scag_gate layer2 decIn_below_layer2 ned ((pl.map Prod.fst).map A)
  rw [← List.map_take, ← listNoun_map_listN, ← listNoun_map_listN] at hscag
  have hL := optC_layer2
  unfold wpS1 swWk swSp swK9 swK8 swK7 swK6 swK5 swK4 swS8 swS7 swS6 swS5 swS4 swS3 swG at *
  generalize optC = OC at hL hidt
  generalize Opt.freshIds (ned + 1) ((pl.map Prod.fst).take ned) ned nex = R at hidt ⊢
  generalize (pl.map Prod.fst).take ned = TK at hidt hscag
  conv => lhs; arg 2; unfold swWPFin
  simp [nock_exec, hL, scag.arm_at, scag_arm, hscag, hidt]

/-! ## The tree, the head, the next turn -/

/-- The `%imm` ops into `r`, the ops the `+skip` drops. -/
def immTo (r : Nat) : Pole → Bool
  | Pole.imm _ dd => decide (dd = r)
  | _ => false

/-- `+skip` with the test of a plain chain, restated from `skip_gate_map`
(`Compiler/CompPruneLink.lean`). -/
theorem sw_skip_gate_map {α : Type} (E : α → Noun) (c bp bs bc : Noun) (p : α → Bool) (l : List α)
    (hf : ∀ a ∈ l, nock (C bp (C (E a) bc)) bp = some (loob (p a))) :
    nock (C skip.battery (C (C (listN (l.map E)) (C bp (C bs bc))) c)) skip.battery
      = some (listN ((l.filter fun a => !p a).map E)) := by
  classical
  let p' : Noun → Bool := fun x => match l.find? (fun a => decide (E a = x)) with
    | some a => p a
    | none => false
  have hp : ∀ a ∈ l, p' (E a) = p a := by
    intro a ha
    have hfa := hf a ha
    cases e : l.find? (fun b => decide (E b = E a)) with
    | none =>
      exfalso
      have := List.find?_eq_none.1 e a ha
      simp at this
    | some b =>
      have hb := List.mem_of_find?_eq_some e
      have hbe : E b = E a := by simpa using List.find?_some e
      have hfb := hf b hb
      rw [hbe, hfa] at hfb
      have : p a = p b := by
        cases h1 : p a <;> cases h2 : p b <;> simp_all [loob]
      simp only [p', e, this]
  rw [skip_gate c bp bs bc p' (l.map E) (fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    rw [hp a ha]; exact hf a ha)]
  congr 2
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro a ha
  simp [hp a ha]

/-- The test of the `+skip`: an `%imm` into the register of the first test. -/
theorem wp_skg (r : Nat) (op : Pole) (BS X : Noun) (hX : slot? 0x7f9f X = some (A r)) :
    nock (C swWPSkG (C op.toNoun (C BS X))) swWPSkG = some (loob (immTo r op)) := by
  unfold swWPSkG
  have h2 : slot? 0x3ff9f (C swWPSkG (C op.toNoun (C BS X))) = some (A r) := by
    simp [nock_exec, hX]
  cases op with
  | imm n dd =>
    by_cases e : dd = r
    · subst e; simp [nock_exec, Pole.toNoun, immTo, loob, eqCode, Tag.imm, h2, hX]
    · simp [nock_exec, Pole.toNoun, immTo, loob, eqCode, Tag.imm, h2, e, hX]
  | _ => simp [nock_exec, Pole.toNoun, immTo, loob, eqCode, Tag.imm, Tag.mov, Tag.inc, Tag.con, Tag.hed, Tag.tal, Tag.cel, Tag.lob, Tag.equ, Tag.hsp, Tag.hse,
      Tag.hdp, Tag.hde, Tag.hmp, Tag.hme, Tag.hcp, Tag.hce, Tag.spy, Tag.nok, Tag.cal, Tag.caf, Tag.cam, Tag.csl,
      Tag.csf, Tag.csm]

end Compiler
end Formalization
