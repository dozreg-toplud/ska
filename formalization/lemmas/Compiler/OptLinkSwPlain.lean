import lemmas.Compiler.OptLinkSwChain

/-!
# `+switch-chains`: the gates `plain-of` and `plains-of`

```hoon
  =/  plain-of
    |=  p=@uwoo
    ^-  (unit plain)
    =/  b=blob  (~(got by blocks) p)
    ?.  ?=([%eqq * * [~ *] [~ *]] fin.b)  ~
    =/  m=(unit [n=* d=@uvre])
      =/  bod=(list pole)  body.b
      |-  ^-  (unit [n=* d=@uvre])
      ?~  bod  ~
      ?:  ?&  ?=([%imm *] i.bod)
              |(=(d.i.bod l.fin.b) =(d.i.bod r.fin.b))
          ==
        `[n d]:i.bod
      $(bod t.bod)
    ?~  m  ~
    =/  c=*  n.u.m
    ?.  ?=(@ c)  ~
    ?.  (lth c (bex 31))  ~
    ?:  =(l.fin.b r.fin.b)  ~
    ?.  =(2 (~(gut by uses) d.u.m 0))  ~
    =/  d=@uvre  ?:(=(d.u.m l.fin.b) r.fin.b l.fin.b)
    `[d c there.z.fin.b there.o.fin.b d.u.m]
  =/  plains-of
    |=  p=@uwoo
    ^-  (list [p=@uwoo t=plain])
    =/  t=(unit plain)  (plain-of p)
    ?~  t  ~
    :-  [p u.t]
    =/  nb=blob  (~(got by blocks) miss.u.t)
    ?.  ?=(~ par.nb)  ~
    ?.  ?=([[%imm *] ~] body.nb)  ~
    ?.  =(~[p] (~(get ja rev) miss.u.t))  ~
    =/  t2=(unit plain)  (plain-of miss.u.t)
    ?~  t2  ~
    ?.  =(d.u.t2 d.u.t)  ~
    $(p miss.u.t)
```

* `po_mt`: the trap of `m` is `immInto`.
* `po_c`: `plain-of` from `?~  m` is `poC`.
* `sw_plain`: **the gate `plain-of` is `plainOf`**, crashes included
  (`plainOf_eq` restates the model by `poC`).
* `sw_plains`: **where `plainsOf fuel` returns `ps`, the gate `plains-of`
  returns the noun of `ps`**.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The model, step by step -/

/-- `plain-of` from `?~  m`. -/
def poC (u : Nat → Nat) (l r hit miss : Nat) : Option (Noun × Nat) → Option Opt.SPlain
  | none => none
  | some (mn, md) =>
    match Opt.smallAtom mn with
    | none => none
    | some c => if l = r then none else if u md ≠ 2 then none else some ⟨if md = l then r else l, c, hit, miss, md⟩

/-- `plainOf` by the steps. -/
theorem plainOf_eq (bl : TreapMap mugF Blob) (p : Nat) :
    Opt.plainOf bl p = (HoonMap.get bl p).bind (fun b => match eqqNA b.fin with
      | none => some none
      | some (l, r, hit, miss) => some (poC (Opt.usesOf bl) l r hit miss (Opt.immInto l r b.body))) := by
  unfold Opt.plainOf
  cases HoonMap.get bl p with
  | none => rfl
  | some b =>
    simp only [Option.bind_some]
    obtain ⟨par, body, fin⟩ := b
    match fin with
    | .clq .. | .brn .. | .brz .. | .hop .. | .jmp .. | .jmf .. | .jsp .. | .jsf .. | .don .. | .bom ..
    | .lti .. => rfl
    | .eqq l r ⟨_ :: _, hit⟩ o2 => rfl
    | .eqq l r ⟨[], hit⟩ ⟨_ :: _, n'⟩ => rfl
    | .eqq l r ⟨[], hit⟩ ⟨[], miss⟩ =>
      simp only [eqqNA]
      cases Opt.immInto l r body with
      | none => rfl
      | some m =>
        obtain ⟨mn, md⟩ := m
        simp only [poC]
        cases Opt.smallAtom mn with
        | none => rfl
        | some c =>
          simp only
          by_cases e1 : l = r
          · simp [e1]
          · by_cases e2 : Opt.usesOf bl md = 2
            · simp [e1, e2]
            · simp [e1, e2]

/-! ## The subjects -/

/-- The subject of the gate `plain-of`: `[swPOB [p S5]]`. -/
def poG (p : Nat) (BL TOPO REV USES : Noun) : Noun := C swPOB (C (A p) (swS5 BL TOPO REV USES))

/-! ## The trap of `m` -/

theorem po_mt (l r : Nat) (z o : Jmp) (BP G : Noun) : ∀ (body : List Pole) (BB : Noun),
    nock (C swPOMT (C (listNoun Pole.toNoun body) (C (C BP (C BB (Termin.eqq l r z o).toNoun)) G))) swPOMT
      = some (mN (Opt.immInto l r body)) := by
  intro body
  induction body with
  | nil =>
    intro BB
    conv => lhs; arg 2; unfold swPOMT
    simp [nock_exec, listNoun, mN, unitNoun, Opt.immInto]
  | cons op rest ih =>
    intro BB
    have ih' := ih BB
    conv => lhs; arg 2; unfold swPOMT
    cases op with
    | imm n d =>
      by_cases e1 : d = l
      · subst e1
        simp [nock_exec, listNoun, mN, unitNoun, Opt.immInto, Pole.toNoun, Termin.toNoun, eqCode, Tag.imm]
      · by_cases e2 : d = r
        · subst e2
          simp [nock_exec, listNoun, mN, unitNoun, Opt.immInto, Pole.toNoun, Termin.toNoun, eqCode, Tag.imm, e1]
        · simp only [Termin.toNoun] at ih'
          simp [nock_exec, listNoun, mN, unitNoun, Opt.immInto, Pole.toNoun, Termin.toNoun, eqCode, Tag.imm, e1, e2,
            ih']
    | _ =>
      simp only [Termin.toNoun] at ih'
      simp [nock_exec, listNoun, mN, unitNoun, Opt.immInto, Pole.toNoun, Termin.toNoun, eqCode, ih', Tag.imm, Tag.mov, Tag.inc, Tag.con, Tag.hed, Tag.tal, Tag.cel, Tag.lob, Tag.equ, Tag.hsp, Tag.hse,
        Tag.hdp, Tag.hde, Tag.hmp, Tag.hme, Tag.hcp, Tag.hce, Tag.spy, Tag.nok, Tag.cal, Tag.caf, Tag.cam, Tag.csl,
        Tag.csf, Tag.csm]

/-! ## From `?~  m` -/

theorem po_c (bl : TreapMap mugF Blob) (TOPO REV USES : Noun) (hU : UsesRel USES (Opt.usesOf bl))
    (p l r hit miss : Nat) (BP BB : Noun) (m : Option (Noun × Nat)) :
    nock (C (mN m) (C (C BP (C BB (Termin.eqq l r ⟨[], hit⟩ ⟨[], miss⟩).toNoun))
      (poG p (HoonMap.toNoun Blob.toNoun bl) TOPO REV USES))) swPOC
      = some (unitNoun splainN (poC (Opt.usesOf bl) l r hit miss m)) := by
  have hL := optC_layer2
  have hL1 := optC_layer1
  unfold poG swS5 swS4 swS3 swG
  cases m with
  | none => simp [nock_exec, swPOC, mN, unitNoun, poC]
  | some mm =>
    obtain ⟨mn, md⟩ := mm
    have hg := uses_gut hU md
    generalize optC = OC at hL hL1
    generalize HoonMap.toNoun Blob.toNoun bl = BL
    generalize Opt.usesOf bl = u at hg
    cases mn with
    | cell a b => simp [nock_exec, swPOC, mN, unitNoun, poC, Opt.smallAtom]
    | atom c =>
      have hlt := lth_gate layer1 decIn_layer1 c (2 ^ 31)
      have hbx := bex_gate layer2 mulIn_below_layer2 31
      by_cases hc : c < 2 ^ 31
      · by_cases e1 : l = r
        · subst e1
          simp [nock_exec, swPOC, mN, unitNoun, poC, Opt.smallAtom, hc, hL, hL1, lth.arm_at, lth_arm, hlt,
            bex.arm_at, bex_arm, hbx, loob, Termin.toNoun]
        · by_cases e2 : u md = 2
          · by_cases e3 : md = l
            · subst e3
              simp [nock_exec, swPOC, mN, unitNoun, poC, Opt.smallAtom, hc, hL, hL1, lth.arm_at, lth_arm, hlt,
                bex.arm_at, bex_arm, hbx, loob, Termin.toNoun, Jmp.toNoun, e1, e2, by.arm_at, by_arm, by.gut.arm_at,
                gut_arm, hg, splainN]
            · simp [nock_exec, swPOC, mN, unitNoun, poC, Opt.smallAtom, hc, hL, hL1, lth.arm_at, lth_arm, hlt,
                bex.arm_at, bex_arm, hbx, loob, Termin.toNoun, Jmp.toNoun, e1, e2, e3, by.arm_at, by_arm,
                by.gut.arm_at, gut_arm, hg, splainN]
          · simp [nock_exec, swPOC, mN, unitNoun, poC, Opt.smallAtom, hc, hL, hL1, lth.arm_at, lth_arm, hlt,
              bex.arm_at, bex_arm, hbx, loob, Termin.toNoun, Jmp.toNoun, e1, e2, Ne.symm e2, by.arm_at, by_arm,
              by.gut.arm_at, gut_arm, hg]
      · simp [nock_exec, swPOC, mN, unitNoun, poC, Opt.smallAtom, hc, hL, hL1, lth.arm_at, lth_arm, hlt,
          bex.arm_at, bex_arm, hbx, loob]

/-! ## The gate `plain-of` -/

/-- **The gate `plain-of`** on the noun of a label: the noun of `plainOf`,
and a crash where the model crashes. -/
theorem sw_plain (bl : TreapMap mugF Blob) (TOPO REV USES : Noun) (hU : UsesRel USES (Opt.usesOf bl)) (p : Nat) :
    nock (poG p (HoonMap.toNoun Blob.toNoun bl) TOPO REV USES) swPOB
      = (Opt.plainOf bl p).map (unitNoun splainN) := by
  rw [plainOf_eq]
  have hg := blocks_got bl p
  have hL := optC_layer2
  cases hb : HoonMap.get bl p with
  | none =>
    rw [hb] at hg
    unfold poG swS5 swS4 swS3 swG
    generalize optC = OC at hL
    generalize HoonMap.toNoun Blob.toNoun bl = BL at hg
    conv => lhs; arg 2; unfold swPOB
    simp [nock_exec, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg]
  | some b =>
    rw [hb] at hg
    obtain ⟨par, body, fin⟩ := b
    have he := to_eqq fin (listNoun A par) (listNoun Pole.toNoun body)
      (poG p (HoonMap.toNoun Blob.toNoun bl) TOPO REV USES)
    simp only [Option.map_some, Blob.toNoun] at hg
    cases hq : eqqNA fin with
    | none =>
      rw [hq] at he
      unfold poG swS5 swS4 swS3 swG at *
      generalize optC = OC at hL he
      generalize HoonMap.toNoun Blob.toNoun bl = BL at hg he
      conv => lhs; arg 2; unfold swPOB
      simp [nock_exec, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg, he, loob, unitNoun, hq]
    | some q =>
      obtain ⟨l, r, hit, miss⟩ := q
      have ht := eqqNA_some hq
      subst ht
      rw [hq] at he
      have hm := po_mt l r ⟨[], hit⟩ ⟨[], miss⟩ (listNoun A par) (poG p (HoonMap.toNoun Blob.toNoun bl) TOPO REV USES)
        body (listNoun Pole.toNoun body)
      have hc := po_c bl TOPO REV USES hU p l r hit miss (listNoun A par) (listNoun Pole.toNoun body)
        (Opt.immInto l r body)
      unfold poG swS5 swS4 swS3 swG at *
      generalize optC = OC at hL he hm hc
      generalize HoonMap.toNoun Blob.toNoun bl = BL at hg he hm hc
      conv => lhs; arg 2; unfold swPOB
      simp [nock_exec, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg, he, loob, hm, hc, eqqNA]

/-! ## The gate `plains-of` -/

/-- A body of one `%imm`. -/
def oneImm : List Pole → Bool
  | [Pole.imm _ _] => true
  | _ => false

theorem ps_shape (body : List Pole) (P F X : Noun) :
    nock (C (C P (C (listNoun Pole.toNoun body) F)) X) swPSShape = some (loob (oneImm body)) := by
  unfold swPSShape
  cases body with
  | nil => simp [nock_exec, listNoun, oneImm, loob]
  | cons op rest =>
    cases rest with
    | nil => cases op <;> simp [nock_exec, listNoun, oneImm, loob, Pole.toNoun, eqCode, Tag.imm, Tag.mov, Tag.inc, Tag.con, Tag.hed, Tag.tal, Tag.cel, Tag.lob, Tag.equ, Tag.hsp, Tag.hse,
      Tag.hdp, Tag.hde, Tag.hmp, Tag.hme, Tag.hcp, Tag.hce, Tag.spy, Tag.nok, Tag.cal, Tag.caf, Tag.cam, Tag.csl,
      Tag.csf, Tag.csm]
    | cons op2 rest =>
      cases op <;> simp [nock_exec, listNoun, oneImm, loob, Pole.toNoun, eqCode, Tag.imm, Tag.mov, Tag.inc, Tag.con, Tag.hed, Tag.tal, Tag.cel, Tag.lob, Tag.equ, Tag.hsp, Tag.hse,
      Tag.hdp, Tag.hde, Tag.hmp, Tag.hme, Tag.hcp, Tag.hce, Tag.spy, Tag.nok, Tag.cal, Tag.caf, Tag.cam, Tag.csl,
      Tag.csf, Tag.csm]

theorem oneImm_true {body : List Pole} (h : oneImm body = true) : ∃ n d, body = [Pole.imm n d] := by
  cases body with
  | nil => cases h
  | cons op rest =>
    cases rest with
    | nil =>
      cases op with
      | imm n d => exact ⟨n, d, rfl⟩
      | _ => cases h
    | cons op2 rest => cases op <;> cases h

theorem oneImm_false {body : List Pole} (h : ∀ n d, body = [Pole.imm n d] → False) : oneImm body = false := by
  cases body with
  | nil => rfl
  | cons op rest =>
    cases rest with
    | nil =>
      cases op with
      | imm n d => exact absurd rfl (h n d)
      | _ => rfl
    | cons op2 rest => cases op <;> rfl

/-- **The gate `plains-of`**: where `plainsOf fuel` returns `ps`, the gate on
the noun of `p` returns the noun of `ps`. -/
theorem sw_plains (bl : TreapMap mugF Blob) (rev : TreapMap mugF (List Nat)) (TOPO USES : Noun)
    (hU : UsesRel USES (Opt.usesOf bl)) :
    ∀ (fuel p : Nat) (ps : List (Nat × Opt.SPlain)), Opt.plainsOf bl rev fuel p = some ps →
    nock (C swPSB (C (A p) (swS6 (HoonMap.toNoun Blob.toNoun bl) TOPO (jarN rev) USES))) swPSB
      = some (listNoun spN ps) := by
  intro fuel
  induction fuel with
  | zero => intro p ps h; simp [Opt.plainsOf] at h
  | succ k ih =>
    intro p ps h
    simp only [Opt.plainsOf] at h
    obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
    have hT := sw_plain bl TOPO (jarN rev) USES hU p
    rw [ht] at hT
    have hL := optC_layer2
    cases t with
    | none =>
      simp only [Option.some.injEq] at h
      subst h
      unfold poG at hT
      unfold swS6
      generalize swS5 _ _ _ _ = S5 at hT ⊢
      conv => lhs; arg 2; unfold swPSB
      simp [nock_exec, hT, unitNoun, listNoun]
    | some t =>
      obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨nb, hnb, hrest⟩ := Option.bind_eq_some_iff.mp hrest
      have hg := blocks_got bl t.miss
      rw [hnb] at hg
      obtain ⟨npar, nbody, nfin⟩ := nb
      simp only [Option.map_some, Blob.toNoun] at hg
      have hj := jar_get rev t.miss
      unfold poG at hT
      by_cases hc1 : npar = []
      · subst hc1
        have hsh := ps_shape nbody (A 0) nfin.toNoun
        simp only [ne_eq, not_true_eq_false, if_false] at hrest
        by_cases hbo : oneImm nbody = true
        · obtain ⟨n, d, rfl⟩ := oneImm_true hbo
          simp only at hrest
          simp only [oneImm, listNoun] at hsh
          by_cases hc2 : Opt.getJa rev t.miss = [p]
          · simp only [hc2, ne_eq, not_true_eq_false, if_false] at hrest
            rw [hc2] at hj
            obtain ⟨t2, ht2, hrest⟩ := Option.bind_eq_some_iff.mp hrest
            have hT2 := sw_plain bl TOPO (jarN rev) USES hU t.miss
            rw [ht2] at hT2
            unfold poG at hT2
            cases t2 with
            | none =>
              simp only [Option.some.injEq] at hrest
              subst hrest
              unfold swS6 swS5 swS4 swS3 swG at *
              generalize optC = OC at hL hT hT2
              generalize HoonMap.toNoun Blob.toNoun bl = BL at hg hT hT2 hsh
              conv => lhs; arg 2; unfold swPSB
              simp [nock_exec, hT, hT2, unitNoun, listNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg,
                ja.arm_at, ja_arm, ja.get.arm_at, ju_get_arm, hj, splainN, spN, eqCode, hsh, loob]
            | some t2 =>
              by_cases hs : t2.d = t.d
              · simp only [hs, ne_eq, not_true_eq_false, if_false] at hrest
                have ih' := ih t.miss rest hrest
                unfold swS6 swS5 swS4 swS3 swG at *
                generalize optC = OC at hL hT hT2 ih'
                generalize HoonMap.toNoun Blob.toNoun bl = BL at hg hT hT2 ih' hsh
                conv => lhs; arg 2; unfold swPSB
                simp [nock_exec, hT, hT2, unitNoun, listNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg,
                  ja.arm_at, ja_arm, ja.get.arm_at, ju_get_arm, hj, splainN, spN, eqCode, hs, ih', hsh, loob]
              · simp only [hs, ne_eq, not_false_eq_true, if_true, Option.some.injEq] at hrest
                subst hrest
                unfold swS6 swS5 swS4 swS3 swG at *
                generalize optC = OC at hL hT hT2
                generalize HoonMap.toNoun Blob.toNoun bl = BL at hg hT hT2 hsh
                conv => lhs; arg 2; unfold swPSB
                simp [nock_exec, hT, hT2, unitNoun, listNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg,
                  ja.arm_at, ja_arm, ja.get.arm_at, ju_get_arm, hj, splainN, spN, eqCode, hs, hsh, loob]
          · simp only [hc2, ne_eq, not_false_eq_true, if_true, Option.some.injEq] at hrest
            subst hrest
            unfold swS6 swS5 swS4 swS3 swG at *
            generalize optC = OC at hL hT
            generalize HoonMap.toNoun Blob.toNoun bl = BL at hg hT hsh
            conv => lhs; arg 2; unfold swPSB
            simp [nock_exec, hT, unitNoun, listNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg,
              ja.arm_at, ja_arm, ja.get.arm_at, ju_get_arm, hj, splainN, spN, eqCode, hsh, loob, pair_eq_listNoun, hc2]
        · have hbo' : oneImm nbody = false := by simpa using hbo
          have hr0 : rest = [] := by
            split at hrest
            · simp_all [oneImm]
            · simp only [Option.some.injEq] at hrest; exact hrest.symm
          subst hr0
          rw [hbo'] at hsh
          unfold swS6 swS5 swS4 swS3 swG at *
          generalize optC = OC at hL hT
          generalize HoonMap.toNoun Blob.toNoun bl = BL at hg hT hsh
          conv => lhs; arg 2; unfold swPSB
          simp [nock_exec, hT, unitNoun, listNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg, splainN, spN,
            eqCode, hsh, loob]
      · simp only [ne_eq, hc1, not_false_eq_true, if_true, Option.some.injEq] at hrest
        subst hrest
        unfold swS6 swS5 swS4 swS3 swG at *
        generalize optC = OC at hL hT
        generalize HoonMap.toNoun Blob.toNoun bl = BL at hg hT
        conv => lhs; arg 2; unfold swPSB
        simp [nock_exec, hT, unitNoun, listNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg, splainN, spN,
          eqCode, listNoun_nil_iff, hc1]

end Compiler
end Formalization
