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

end Compiler
end Formalization
