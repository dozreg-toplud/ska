import lemmas.Compiler.OptLinkSwCases

/-!
# `+switch-chains`: the gate `tree`

```hoon
  =/  tree
    |=  $:  cas=(list case)
            d=@uvre
            mis=@uwoo
            ids=(list @uwoo)
            out=(map @uwoo blob-out)
        ==
    ^-  [body=(list pole) fin=termin-out ids=(list @uwoo) out=(map @uwoo blob-out)]
    ?>  ?=(^ cas)
    ?:  ?=(~ t.cas)
      :*  ~[[%imm c.i.cas r.i.cas]]
          [%eqq d r.i.cas [~ hit.i.cas] [~ mis]]
          ids
          out
      ==
    =/  all=(list case)  cas
    =/  haf=@ud  (div (lent all) 2)
    =/  hi=(list case)  (slag haf all)
    ?>  ?=(^ hi)
    ?>  ?=([* * *] ids)
    =/  [l-id=@uwoo r-id=@uwoo]  [i.ids i.t.ids]
    =/  l  $(cas (scag haf all), ids t.t.ids)
    =.  out.l  (~(put by out.l) l-id [~ body.l fin.l])
    =/  r  $(cas hi, ids ids.l, out out.l)
    =.  out.r  (~(put by out.r) r-id [~ body.r fin.r])
    [~ [%lti c.i.hi d [~ l-id] [~ r-id]] ids.r out.r]
```

`sw_tree`: **where `stree` returns `(body, fin, ids, out)`, the gate returns
their nouns**, by induction on the fuel.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The noun of what `tree` returns: `[body fin ids out]`. -/
def swTrN (r : List Pole × Termin × List Nat × TreapMap mugF Blob) : Noun :=
  C (listNoun Pole.toNoun r.1) (C r.2.1.toNoun (C (listNoun A r.2.2.1) (HoonMap.toNoun Blob.toNoun r.2.2.2)))

/-- The subject of the gate `tree`. -/
def swTrG (cas : List Opt.SCase) (d mis : Nat) (ids : List Nat) (out : TreapMap mugF Blob)
    (BL TOPO REV USES : Noun) : Noun :=
  C swTRB (C (C (listNoun scaseN cas) (C (A d) (C (A mis) (C (listNoun A ids) (HoonMap.toNoun Blob.toNoun out)))))
    (swS8 BL TOPO REV USES))

theorem dvrIn_layer1 : DvrIn layer1 := arith_layer1.2.2.2.2.2.2.2.2.2.1

theorem blocks_put (bl : TreapMap mugF Blob) (o : Nat) (b : Blob) :
    nock (C by.put.battery (C (C (A o) b.toNoun) (C by.battery (C (HoonMap.toNoun Blob.toNoun bl) layer2))))
      by.put.battery = some (HoonMap.toNoun Blob.toNoun (HoonMap.put bl o b)) :=
  put_gate (mug := mugF) layer2 gorIn_morIn_layer2 _ _ _ _ (putF_hoonMap Blob.toNoun bl o b)

theorem drop_half_cons {α : Type} (x y : α) (t : List α) :
    ∃ h hs, (x :: y :: t).drop ((x :: y :: t).length / 2) = h :: hs := by
  have hlt : (x :: y :: t).length / 2 < (x :: y :: t).length := by simp; omega
  cases e : (x :: y :: t).drop ((x :: y :: t).length / 2) with
  | nil =>
    have := congrArg List.length e
    simp only [List.length_drop, List.length_nil] at this
    omega
  | cons h hs => exact ⟨h, hs, rfl⟩

/-- **The gate `tree`**: where `stree` returns, the gate returns the nouns of
the body and end of the root, the labels left and the blocks. -/
theorem sw_tree (BL TOPO REV USES : Noun) (d mis : Nat) :
    ∀ (fuel : Nat) (cas : List Opt.SCase) (ids : List Nat) (out : TreapMap mugF Blob) r,
    Opt.stree d mis fuel cas ids out = some r →
    nock (swTrG cas d mis ids out BL TOPO REV USES) swTRB = some (swTrN r) := by
  have hL := optC_layer2
  have hL1 := optC_layer1
  intro fuel
  induction fuel with
  | zero => intro cas ids out r h; simp [Opt.stree] at h
  | succ n ih =>
    intro cas ids out r h
    match cas with
    | [] => simp [Opt.stree] at h
    | [x] =>
      simp only [Opt.stree, Option.some.injEq] at h
      subst h
      unfold swTrG
      conv => lhs; arg 2; unfold swTRB
      simp [nock_exec, swTRLeaf, listNoun, scaseN, swTrN, Pole.toNoun, Termin.toNoun, Jmp.toNoun, Tag.imm, Tag.eqq]
    | x :: y :: t =>
      obtain ⟨h0, hs, hhi⟩ := drop_half_cons x y t
      simp only [Opt.stree] at h
      rw [hhi] at h
      match ids with
      | [] => simp at h
      | [_] => simp at h
      | lid :: rid :: rest =>
        simp only at h
        obtain ⟨⟨lb, lf, lids, lout⟩, hl, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨⟨rb, rf, rids, rout⟩, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        have ihl := ih _ _ _ _ hl
        have ihr := ih _ _ _ _ hr
        have hlen := lent_gate layer2 ((x :: y :: t).map scaseN)
        have hdiv := div_gate layer1 dvrIn_layer1 (x :: y :: t).length 2 (by omega)
        have hslag := slag_gate layer2 decIn_below_layer2 ((x :: y :: t).length / 2) ((x :: y :: t).map scaseN)
        have hscag := scag_gate layer2 decIn_below_layer2 ((x :: y :: t).length / 2) ((x :: y :: t).map scaseN)
        have hpl := blocks_put lout lid ⟨[], lb, lf⟩
        have hpr := blocks_put rout rid ⟨[], rb, rf⟩
        rw [← List.map_drop, hhi] at hslag
        rw [← List.map_take] at hscag
        simp only [List.length_map] at hlen
        generalize (x :: y :: t).length = L at hlen hdiv hslag hscag ihl
        simp only [← listNoun_map_listN] at hscag hlen hslag
        unfold swTrG swTrN at *
        simp only [listNoun, scaseN] at hlen hslag hscag ihl ihr
        unfold swS8 swS7 swS6 swS5 swS4 swS3 swG at *
        generalize optC = OC at hL hL1 ihl ihr
        conv => lhs; arg 2; unfold swTRB
        simp only [Blob.toNoun, listNoun] at hpl hpr
        have hlti : (Termin.lti h0.c d ⟨[], lid⟩ ⟨[], rid⟩).toNoun
            = C (A Tag.lti) (C (A h0.c) (C (A d) (C (C (A 0) (A lid)) (C (A 0) (A rid))))) := rfl
        simp [nock_exec, swTRSplit, swTRRec, listNoun, scaseN, hL, hL1, lent.arm_at, lent_arm, hlen,
          div.arm_at, div_arm, hdiv, slag.arm_at, slag_arm, hslag, scag.arm_at, scag_arm, hscag, ihl, ihr,
          by.arm_at, by_arm, by.put.arm_at, put_arm, hpl, hpr, hlti, Tag.lti]

end Compiler
end Formalization
