import lemmas.Compiler.EvalConv
import lemmas.Compiler.MockPill
import lemmas.Pill.Arm.Eval_rend
import lemmas.Pill.Arm.Eval_mook

/-!
# `+eval-rend` and `+eval-mook`

`+eval-rend` renders one frame of the interpreter's trace: a `%meac` frame by
`(soft tank)`, a `%meaf` frame by a call of the bell it names (a `%dire` poke
and `+eval-blob` on the callee's block `0`, with neither trace nor scry gate),
and any other frame by the pill's `+mook` on a trace of that frame alone.
`+eval-mook` cuts a long trace as `+mook` does and renders it from the last
frame on.

Both directions are proved against `evalRend` and `evalMook` of
`Ska/Interp.lean`, at a level `m` that is both the depth of the calls and the
fuel of `+mink`.  The pill's side of the call is `+eval-blob` in full
(`eval_blob_to_model`, from `interp_ge`).

## The bell of a `%meaf` frame

The Hoon pokes with the raw noun `-.dat`, and the model decodes it with
`Bell.ofNoun?`.  `Bell.ofNoun?` is `+validate-bell` (with `Cape.ofNoun?` for
`+validate-cape`): both accept a noun `[[cape data] fol]` whose cape has only
`&` and `|` at its leaves and whose formula is a cell, and both rebuild the same
noun from its parts.  So on what `+validate-bell` accepts, `Bell.ofNoun?`
inverts `Bell.toNoun` (`bell_ofNoun_toNoun`), and the raw poke is the poke of
the ovum `[%dire a |]`.  The line `=+(=(n out) out)` of the three validators
computes the equality and drops it: it asserts nothing, and needs not, since
the rebuilt noun is the input whenever the validator returns.  Where
`Bell.ofNoun?` is `none` the model crashes, and the converse needs the pill's
poke to crash too (`PokeDireBad`), which is a fact about the Nock of
`+validate-ovum` that is not proved here.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

theorem cape_ofNoun_toNoun : ∀ {n : Noun} {c : Cape}, Cape.ofNoun? n = some c → c.toNoun = n
  | Noun.atom 0, c, h => by simp [Cape.ofNoun?] at h; subst h; rfl
  | Noun.atom 1, c, h => by simp [Cape.ofNoun?] at h; subst h; rfl
  | Noun.atom (_ + 2), c, h => by simp [Cape.ofNoun?] at h
  | Noun.cell x y, c, h => by
    simp only [Cape.ofNoun?, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨cx, hx, cy, hy, rfl⟩ := h
    simp [Cape.toNoun, cape_ofNoun_toNoun hx, cape_ofNoun_toNoun hy]

/-- On what `+validate-bell` accepts, `Bell.ofNoun?` inverts `Bell.toNoun`. -/
theorem bell_ofNoun_toNoun {n : Noun} {a : Bell} (h : Bell.ofNoun? n = some a) : a.toNoun = n := by
  match n, h with
  | Noun.cell (Noun.cell c d) (Noun.cell f g), h =>
    simp only [Bell.ofNoun?, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨c', hc, rfl⟩ := h
    simp [Bell.toNoun, Sock.toNoun, cape_ofNoun_toNoun hc]

/-- The gate of `+eval-rend` slammed on the frame `[tag dat]` in `icore cr`. -/
abbrev rendS (cr : Noun) (tag : Nat) (dat : Noun) : Noun :=
  C eval_rend.battery (C (C (A tag) dat) (icore cr))

theorem mookF_one (lib : Lib) (k : Nat) (fr : Frame) :
    mookF lib k (Tone.two [fr]) = (rendF lib k fr).map fun t => Toon.two [t] := by
  cases h : rendF lib k fr <;> simp [mookF, skip, List.mapM_cons, h]

set_option maxHeartbeats 4000000 in
theorem eval_rend_mook_some (cr : Noun) (hc : CorIn cr) (tag : Nat) (dat t : Noun)
    (h1 : tag ≠ Tag.meac) (h2 : tag ≠ Tag.meaf)
    (hm : nock (C mook.battery (C (Tone.two [(tag, dat)]).toNoun layer4)) mook.battery
      = some (Toon.two [t]).toNoun) :
    nock (rendS cr tag dat) eval_rend.battery = some (C t cr) := by
  have hl4 : slot? (read.layer2.axis / 4) (icore cr) = some layer4 := hc.2.1
  simp only [read.layer2.axis, icore, Nat.reduceDiv, nock_exec] at hl4
  have h1' : ¬ A 0x6361656d = A tag := by simpa [Tag.meac, eq_comm] using h1
  have h2' : ¬ A 0x6661656d = A tag := by simpa [Tag.meaf, eq_comm] using h2
  simp only [Tone.toNoun, Toon.toNoun, listNoun, Frame.toNoun, id] at hm
  nock_open eval_rend.battery
  simp [nock_exec, h1', h2', hl4, mook.arm_at, mook_arm, hm]

set_option maxHeartbeats 4000000 in
theorem eval_rend_mook_none (cr : Noun) (hc : CorIn cr) (tag : Nat) (dat : Noun)
    (h1 : tag ≠ Tag.meac) (h2 : tag ≠ Tag.meaf)
    (hm : nock (C mook.battery (C (Tone.two [(tag, dat)]).toNoun layer4)) mook.battery = none) :
    nock (rendS cr tag dat) eval_rend.battery = none := by
  have hl4 : slot? (read.layer2.axis / 4) (icore cr) = some layer4 := hc.2.1
  simp only [read.layer2.axis, icore, Nat.reduceDiv, nock_exec] at hl4
  have h1' : ¬ A 0x6361656d = A tag := by simpa [Tag.meac, eq_comm] using h1
  have h2' : ¬ A 0x6661656d = A tag := by simpa [Tag.meaf, eq_comm] using h2
  simp only [Tone.toNoun, listNoun, Frame.toNoun] at hm
  nock_open eval_rend.battery
  simp [nock_exec, h1', h2', hl4, mook.arm_at, mook_arm, hm]

set_option maxHeartbeats 4000000 in
/-- A `%meac` frame: `(soft tank)` of its datum, `leaf+"mook.mean"` if it is no
tank. -/
theorem eval_rend_meac (lib : Lib) (hst : SoftTankIs lib layer4) (cr : Noun) (hc : CorIn cr)
    (dat : Noun) :
    nock (rendS cr Tag.meac dat) eval_rend.battery = some (C (rendProduct lib dat) cr) := by
  have hl4 : slot? (read.layer2.axis / 4) (icore cr) = some layer4 := hc.2.1
  have hl2 : slot? read.layer2.axis (icore cr) = some layer2 := hc.1
  simp only [read.layer2.axis, icore, Nat.reduceDiv, nock_exec] at hl4 hl2
  have hs := hst layer2 mook.layer2.arm_at dat
  cases e : lib.softTank dat
  all_goals
    rw [e] at hs
    nock_open eval_rend.battery
    simp [nock_exec, Tag.meac, hl4, hl2, soft.arm_at, tank.arm_at, hs, rendProduct, e, unitN,
      leafMookMean, tape, listNoun, Tag.leaf]


/-- The pill's `(list)` of layer 1, slammed on `n`: `;;((list) n)`.  The
formula pulls the arm `+list` (axis 1407) of layer 1, kicks it, and slams the
mold on `n`; the subject is `[n layer1]`. -/
def listMoldF : Noun :=
  C (A 8) (C (C (A 7) (C (C (A 9) (C (A 1407) (C (A 0) (A 3)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))
    (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))

/-- What `;;((list) n)` computes: the noun when it is a list, a crash
otherwise.  Not proved: `+list` of layer 1 has no generated name. -/
def ListMoldIs : Prop := ∀ n, nock (C n layer1) listMoldF = (nounList? n).map (listNoun id)

set_option maxHeartbeats 4000000 in
/-- The loop of `%meaf` that puts the values `vs` in registers `r, r+1, ...`
of `out`. -/
theorem eval_rend_loop (cr : Noun) (hc : CorIn cr) (P D : Noun) :
    ∀ (vs : List Noun) (r : Nat) (out : TreapMap mugF (Option Noun)),
    nock (C eval_rend.loop (C (A r) (C (HoonMap.toNoun (unitNoun id) out) (C P (C (listNoun id vs)
        (C eval_rend.battery (C D (icore cr)))))))) eval_rend.loop
      = some (HoonMap.toNoun (unitNoun id) (regsFrom r vs out)) := by
  have hl2 : slot? read.layer2.axis (icore cr) = some layer2 := hc.1
  simp only [read.layer2.axis, icore, nock_exec] at hl2
  obtain ⟨hgor, hmor⟩ := gorIn_morIn_layer2
  intro vs
  induction vs with
  | nil =>
    intro r out
    nock_open eval_rend.loop
    simp [nock_exec, listNoun, regsFrom]
  | cons v vs ih =>
    intro r out
    have hput := putF_hoonMap (unitNoun id) out r (some v)
    simp only [unitNoun, id_eq] at hput
    nock_open eval_rend.loop
    simp [nock_exec, listNoun, hl2, by.arm_at, by_arm, by.put.arm_at, put_arm,
      put_gate layer2 ⟨hgor, hmor⟩ _ _ _ _ hput, ih, regsFrom]

/-- The pill's poke crashes on a `%dire` ovum whose bell `+validate-bell`
rejects.  A fact about the Nock of `+validate-ovum`, not proved here. -/
def PokeDireBad (cr : Noun) : Prop :=
  ∀ n mono, Bell.ofNoun? n = none → pokeN cr (C (A Tag.dire) (C n (flag mono))) = none


set_option maxHeartbeats 8000000 in
/-- A `%meaf` frame that the model renders, the pill renders the same: the
list of arguments, the poke `%dire` of the bell, the arguments in registers,
`+eval-blob` on block `0` of the callee, and `(soft tank)` of its product or
`leaf+"####"`. -/
theorem eval_rend_meaf_le (lib : Lib) (hslam : SlamIsNock lib)
    (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
    (hpk : ∀ cr, CorIn cr → PokeIs pk cr) (hst : SoftTankIs lib layer4) (hlist : ListMoldIs)
    (cr : Noun) (hc : CorIn cr) (m : Nat) (hd tl : Noun) (r : Noun × Noun)
    (h : evalRend lib (SkaModel.interp lib pk m) m cr (Tag.meaf, C hd tl) = some r) :
    nock (rendS cr Tag.meaf (C hd tl)) eval_rend.battery = some (C r.1 r.2) ∧ CorIn r.2 := by
  have hne : ¬ Tag.meaf = Tag.meac := by decide
  simp only [evalRend, hne, if_false, if_true, Option.bind_eq_some_iff] at h
  obtain ⟨vs, e1, a, e2, ⟨ton, cr''⟩, e3, h⟩ := h
  have ha := bell_ofNoun_toNoun e2
  subst ha
  obtain ⟨Ob, hOb, e3'⟩ := interp_call_le lib hslam pk hpk m _ _ _ _ _ _ _ e3
  obtain ⟨b, c, new, cr', b0, e4, e5, e6⟩ := callBody_some e3'
  have hc' := (hpk cr hc).2 _ _ e4 (nh_dire _ _)
  obtain ⟨hB, hC⟩ := hOb cr' hc' _ _ _ _ _ _ _ e6
  have hl4 : slot? (read.layer2.axis / 4) (icore cr) = some layer4 := hc.2.1
  have hl2 : slot? read.layer2.axis (icore cr) = some layer2 := hc.1
  have hl1 := slot_tail_of hc.1 layer2_layer1
  simp only [read.layer2.axis, icore, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, nock_exec]
    at hl4 hl2 hl1
  have hl4' : slot? (read.layer2.axis / 4) (icore cr') = some layer4 := hc'.2.1
  have hl2' : slot? read.layer2.axis (icore cr') = some layer2 := hc'.1
  have hl4'' : slot? (read.layer2.axis / 4) (icore cr'') = some layer4 := hC.2.1
  have hl2'' : slot? read.layer2.axis (icore cr'') = some layer2 := hC.1
  simp only [read.layer2.axis, icore, Nat.reduceDiv, nock_exec] at hl4' hl2' hl4'' hl2''
  have hlm := hlist tl
  simp [listMoldF, nock_exec, e1] at hlm
  have hp := (hpk cr hc).1 (Ovum.dire a false) (nh_dire _ _)
  simp only [pokeN, Ska.axPoke, Ovum.toNoun, flag, Bool.false_eq_true, if_false, Tag.dire, e4,
    Option.map_some] at hp
  have hloop := eval_rend_loop cr' hc' (SkaModel.Prod.toNoun (SkaModel.Prod.ir b c new))
    (C (A Tag.meaf) (C a.toNoun tl)) vs 0 HoonMap.empty
  rw [show regsFrom 0 vs HoonMap.empty = regsOf vs from rfl] at hloop
  simp only [SkaModel.Prod.toNoun, Tag.ir, Tag.meaf, icore, HoonMap.toNoun_empty, Straight.toNoun]
    at hloop
  have hg := getF_hoonMap Blob.toNoun c.blocks 0
  rw [e5] at hg
  simp only [unitNoun] at hg
  generalize hbn : b0.toNoun = bn at hg
  simp only [blobS, icore, Straight.toNoun, argsN, listNoun, hbn, resN] at hB
  have hnd : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  have hsm := hst layer2 mook.layer2.arm_at
  refine ⟨?_, ?_⟩
  · rcases ton with q | q | q
    · cases e7 : lib.softTank q
      all_goals
        have hs := hsm q
        rw [e7] at hs
        simp only [Option.some.injEq] at h
        subst h
        nock_open eval_rend.battery
        simp [nock_exec, Tag.meaf, hl1, hlm, hp, SkaModel.Prod.toNoun, Tag.ir,
          hloop, Straight.toNoun, hl2', by.arm_at, by_arm, by.got.arm_at, got_arm,
          got_gate layer2 hnd _ _ _ hg, eval_blob.arm, hB, Tone.toNoun, hl4'', hl2'', soft.arm_at,
          tank.arm_at, hs, rendProduct, e7, unitN, leafMookMean, tape, listNoun, Tag.leaf]
    all_goals
      simp only [Option.some.injEq] at h
      subst h
      nock_open eval_rend.battery
      simp [nock_exec, Tag.meaf, hl1, hlm, hp, SkaModel.Prod.toNoun, Tag.ir,
        hloop, Straight.toNoun, hl2', by.arm_at, by_arm, by.got.arm_at, got_arm,
        got_gate layer2 hnd _ _ _ hg, eval_blob.arm, hB, Tone.toNoun, leafHash, tape, listNoun,
        Tag.leaf]
  · rcases ton with q | q | q <;> simp only [Option.some.injEq] at h <;> subst h <;> exact hC


/-- What the pill's `+eval-blob` returns, the model returns from some level
on. -/
theorem eval_blob_to_model (lib : Lib) (hslam : SlamIsNock lib)
    (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
    (hpk : ∀ cr, CorIn cr → PokeIs pk cr) (cr : Noun) (hc : CorIn cr) (regs : TreapMap mugF (Option Noun))
    (trace : Trace) (b : Blob) (s : Straight (TreapMap mugF)) (params : List (Option Nat))
    (scry x : Noun) (h : nock (blobS cr regs trace b s params scry) eval_blob.battery = some x) :
    ∃ r, x = resN r ∧ CorIn r.2 ∧
      Ev (fun m => execBlob lib (SkaModel.interp lib pk m) s scry cr regs trace b params) r := by
  obtain ⟨k, hk⟩ := iterN_complete h
  obtain ⟨r, hr⟩ := (interp_ge lib hslam pk hpk k).2.1 cr hc regs trace b s params scry x hk
  obtain ⟨rfl, hc'⟩ := blob_val lib hslam pk hpk hc hr hk
  exact ⟨r, rfl, hc', hr⟩

set_option maxHeartbeats 8000000 in
/-- What the pill renders of a `%meaf` frame, the model renders from some
level on. -/
theorem eval_rend_meaf_ge (lib : Lib) (hslam : SlamIsNock lib)
    (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
    (hpk : ∀ cr, CorIn cr → PokeIs pk cr) (hlist : ListMoldIs) (cr : Noun) (hc : CorIn cr)
    (hbad : PokeDireBad cr) (dat x : Noun)
    (h : nock (rendS cr Tag.meaf dat) eval_rend.battery = some x) :
    ∃ v, Ev (fun m => evalRend lib (SkaModel.interp lib pk m) m cr (Tag.meaf, dat)) v := by
  have hne : ¬ Tag.meaf = Tag.meac := by decide
  have hl4 : slot? (read.layer2.axis / 4) (icore cr) = some layer4 := hc.2.1
  have hl2 : slot? read.layer2.axis (icore cr) = some layer2 := hc.1
  have hl1 := slot_tail_of hc.1 layer2_layer1
  simp only [read.layer2.axis, icore, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, nock_exec]
    at hl4 hl2 hl1
  conv at h => { lhs; arg 2; unfold eval_rend.battery }
  rcases dat with da | ⟨hd, tl⟩
  · exfalso
    simp [nock_exec, Tag.meaf] at h
  have hlm := hlist tl
  simp [listMoldF, nock_exec] at hlm
  cases e1 : nounList? tl with
  | none =>
    exfalso
    rw [e1] at hlm
    simp [nock_exec, Tag.meaf, hl1, hlm] at h
  | some vs =>
  rw [e1] at hlm
  simp [nock_exec, Tag.meaf, hl1, hlm] at h
  cases e2 : Bell.ofNoun? hd with
  | none =>
    exfalso
    have hw := hbad hd false e2
    simp only [pokeN, Ska.axPoke, flag, Bool.false_eq_true, if_false, Tag.dire] at hw
    simp [hw] at h
  | some a =>
  have ha := bell_ofNoun_toNoun e2
  subst ha
  have hp := (hpk cr hc).1 (Ovum.dire a false) (nh_dire _ _)
  simp only [pokeN, Ska.axPoke, Ovum.toNoun, flag, Bool.false_eq_true, if_false, Tag.dire] at hp
  cases e4 : pk cr (Ovum.dire a false) with
  | none =>
    exfalso
    rw [e4] at hp
    simp [hp] at h
  | some pr =>
  obtain ⟨p, cr'⟩ := pr
  rw [e4, Option.map_some] at hp
  simp [hp] at h
  have hc' := (hpk cr hc).2 _ _ e4 (nh_dire _ _)
  have hl2' : slot? read.layer2.axis (icore cr') = some layer2 := hc'.1
  simp only [read.layer2.axis, icore, nock_exec] at hl2'
  rcases p with _ | ⟨b, c, new⟩ | ps
  · simp [SkaModel.Prod.toNoun, nock_exec] at h
  rotate_left
  · simp [SkaModel.Prod.toNoun, nock_exec, Tag.drop] at h
  have hloop := eval_rend_loop cr' hc' (SkaModel.Prod.toNoun (SkaModel.Prod.ir b c new))
    (C (A Tag.meaf) (C a.toNoun tl)) vs 0 HoonMap.empty
  rw [show regsFrom 0 vs HoonMap.empty = regsOf vs from rfl] at hloop
  simp only [SkaModel.Prod.toNoun, Tag.ir, Tag.meaf, icore, HoonMap.toNoun_empty, Straight.toNoun]
    at hloop
  have hnd : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  have hg := getF_hoonMap Blob.toNoun c.blocks 0
  cases e5 : HoonMap.get c.blocks 0 with
  | none =>
    exfalso
    rw [e5] at hg
    simp [SkaModel.Prod.toNoun, nock_exec, Tag.ir, hloop, Straight.toNoun, hl2', by.arm_at, by_arm,
      by.got.arm_at, got_arm, got_gate_nil layer2 hnd _ _ hg] at h
  | some b0 =>
  rw [e5] at hg
  simp only [unitNoun] at hg
  generalize hbn : b0.toNoun = bn at hg
  cases eB : nock (blobS cr' (regsOf vs) [] b0 c [] (A 0)) eval_blob.battery with
  | none =>
    exfalso
    simp only [blobS, icore, Straight.toNoun, argsN, listNoun, hbn] at eB
    simp [SkaModel.Prod.toNoun, nock_exec, Tag.ir, hloop, Straight.toNoun, hl2', by.arm_at, by_arm,
      by.got.arm_at, got_arm, got_gate layer2 hnd _ _ _ hg, eval_blob.arm, eB] at h
  | some y =>
  obtain ⟨⟨ton, cr''⟩, -, -, m0, hm⟩ :=
    eval_blob_to_model lib hslam pk hpk cr' hc' _ _ _ _ _ _ _ eB
  apply ev_of (m0 + 1)
  · intro m hm'
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [evalRend, hne, if_false, if_true, e1, e2, Option.bind_some, SkaModel.interp,
      callBody, e4, execEntry, e5, hm m' (by omega)]
    exact rfl
  · cases ton <;> simp


/-- What the model renders of a frame at level `m`, the pill's `+eval-rend`
renders, and it returns a core that keeps layers 2 and 4. -/
theorem eval_rend_le (lib : Lib) (hslam : SlamIsNock lib)
    (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
    (hpk : ∀ cr, CorIn cr → PokeIs pk cr) (hrb : RendBaseIs lib layer4)
    (hst : SoftTankIs lib layer4) (hm : SkipMsgIs lib layer4) (hlist : ListMoldIs)
    (cr : Noun) (hc : CorIn cr) (m : Nat) (fr : Frame) (r : Noun × Noun)
    (h : evalRend lib (SkaModel.interp lib pk m) m cr fr = some r) :
    nock (rendS cr fr.1 fr.2) eval_rend.battery = some (C r.1 r.2) ∧ CorIn r.2 := by
  obtain ⟨tag, dat⟩ := fr
  by_cases h1 : tag = Tag.meac
  · subst h1
    simp only [evalRend, if_true, Option.some.injEq] at h
    subst h
    exact ⟨eval_rend_meac lib hst cr hc dat, hc⟩
  by_cases h2 : tag = Tag.meaf
  · subst h2
    rcases dat with da | ⟨hd, tl⟩
    · have hne : ¬ Tag.meaf = Tag.meac := by decide
      simp [evalRend, hne] at h
    exact eval_rend_meaf_le lib hslam pk hpk hst hlist cr hc m hd tl r h
  simp only [evalRend, h1, h2, if_false, Option.map_eq_some_iff] at h
  obtain ⟨t, ht, rfl⟩ := h
  refine ⟨eval_rend_mook_some cr hc tag dat t h1 h2 ?_, hc⟩
  exact (mook_pill_iff lib hslam hrb hst hm _ _).2 ⟨m, _, by rw [mookF_one, ht]; rfl, rfl⟩

/-- What the pill's `+eval-rend` renders, the model renders from some level
on. -/
theorem eval_rend_ge (lib : Lib) (hslam : SlamIsNock lib)
    (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
    (hpk : ∀ cr, CorIn cr → PokeIs pk cr) (hrb : RendBaseIs lib layer4)
    (hst : SoftTankIs lib layer4) (hm : SkipMsgIs lib layer4) (hlist : ListMoldIs)
    (cr : Noun) (hc : CorIn cr) (hbad : PokeDireBad cr) (fr : Frame) (x : Noun)
    (h : nock (rendS cr fr.1 fr.2) eval_rend.battery = some x) :
    ∃ v, Ev (fun m => evalRend lib (SkaModel.interp lib pk m) m cr fr) v := by
  obtain ⟨tag, dat⟩ := fr
  by_cases h1 : tag = Tag.meac
  · subst h1
    exact ⟨(rendProduct lib dat, cr), 0, fun m _ => by simp [evalRend]⟩
  by_cases h2 : tag = Tag.meaf
  · subst h2
    exact eval_rend_meaf_ge lib hslam pk hpk hlist cr hc hbad dat x h
  cases e : nock (C mook.battery (C (Tone.two [(tag, dat)]).toNoun layer4)) mook.battery with
  | none =>
    rw [eval_rend_mook_none cr hc tag dat h1 h2 e] at h
    simp at h
  | some y =>
    obtain ⟨k, toon, hk, -⟩ := (mook_pill_iff lib hslam hrb hst hm _ _).1 e
    rw [mookF_one, Option.map_eq_some_iff] at hk
    obtain ⟨t, ht, -⟩ := hk
    refine ⟨(t, cr), k, fun m hm' => ?_⟩
    simp [evalRend, h1, h2, rendF_le lib hm' _ t ht]


/-! ## `+eval-mook` -/

/-- The subject of the loop of `+eval-mook`: the tanks so far, the frames
left, the length of the trace, and the gate on `ton` in `icore cr`. -/
abbrev mookLoopS (out : List Noun) (l : Trace) (yel ton cr : Noun) : Noun :=
  C eval_mook.loop2 (C (listNoun id out) (C (listNoun Frame.toNoun l)
    (C yel (C eval_mook.battery (C ton (icore cr))))))

set_option maxHeartbeats 4000000 in
/-- What the model's loop of `+eval-mook` returns at level `m`, the pill's loop
returns. -/
theorem eval_mook_loop_le (lib : Lib) (hslam : SlamIsNock lib)
    (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
    (hpk : ∀ cr, CorIn cr → PokeIs pk cr) (hrb : RendBaseIs lib layer4)
    (hst : SoftTankIs lib layer4) (hm : SkipMsgIs lib layer4) (hlist : ListMoldIs)
    (m : Nat) (yel ton : Noun) :
    ∀ (l : Trace) (out : List Noun) (cr : Noun), CorIn cr → ∀ r,
      evalMookLoop lib (SkaModel.interp lib pk m) m cr l out = some r →
      nock (mookLoopS out l yel ton cr) eval_mook.loop2 = some (C (C (A 2) (listNoun id r.1)) r.2) ∧
        CorIn r.2 := by
  intro l
  induction l with
  | nil =>
    intro out cr hc r h
    simp only [evalMookLoop, Option.some.injEq] at h
    subst h
    refine ⟨?_, hc⟩
    nock_open eval_mook.loop2
    simp [nock_exec, listNoun]
  | cons fr rest ih =>
    intro out cr hc r h
    simp only [evalMookLoop, Option.bind_eq_some_iff] at h
    obtain ⟨⟨tank, cr'⟩, e1, h⟩ := h
    obtain ⟨hR, hc'⟩ := eval_rend_le lib hslam pk hpk hrb hst hm hlist cr hc m fr _ e1
    obtain ⟨hI, hC⟩ := ih (tank :: out) cr' hc' r h
    refine ⟨?_, hC⟩
    have harm := eval_rend.arm_at cr
    simp only [eval_rend.axis] at harm
    simp only [mookLoopS, icore, listNoun, id] at hI
    nock_open eval_mook.loop2
    simp [nock_exec, listNoun, Frame.toNoun, harm, eval_rend.arm, hR, hI]


set_option maxHeartbeats 4000000 in
/-- What the pill's loop of `+eval-mook` returns, the model's loop returns from
some level on. -/
theorem eval_mook_loop_ge (lib : Lib) (hslam : SlamIsNock lib)
    (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
    (hpk : ∀ cr, CorIn cr → PokeIs pk cr) (hrb : RendBaseIs lib layer4)
    (hst : SoftTankIs lib layer4) (hm : SkipMsgIs lib layer4) (hlist : ListMoldIs)
    (hbad : ∀ cr, CorIn cr → PokeDireBad cr) (yel ton : Noun) :
    ∀ (l : Trace) (out : List Noun) (cr : Noun), CorIn cr → ∀ x,
      nock (mookLoopS out l yel ton cr) eval_mook.loop2 = some x →
      ∃ v, Ev (fun m => evalMookLoop lib (SkaModel.interp lib pk m) m cr l out) v := by
  intro l
  induction l with
  | nil => intro out cr _ _ _; exact ⟨(out, cr), 0, fun m _ => by simp [evalMookLoop]⟩
  | cons fr rest ih =>
    intro out cr hc x h
    have harm := eval_rend.arm_at cr
    simp only [eval_rend.axis] at harm
    cases e : nock (rendS cr fr.1 fr.2) eval_rend.battery with
    | none =>
      exfalso
      simp only [rendS, icore] at e
      conv at h => { lhs; arg 2; unfold eval_mook.loop2 }
      simp [nock_exec, listNoun, Frame.toNoun, harm, eval_rend.arm, e] at h
    | some y =>
    obtain ⟨⟨tank, cr'⟩, m1, hm1⟩ :=
      eval_rend_ge lib hslam pk hpk hrb hst hm hlist cr hc (hbad cr hc) fr y e
    obtain ⟨hR, hc'⟩ := eval_rend_le lib hslam pk hpk hrb hst hm hlist cr hc m1 fr _ (hm1 m1 (Nat.le_refl _))
    rw [hR, Option.some.injEq] at e
    subst e
    simp only [rendS, icore] at hR
    have h' : nock (mookLoopS (tank :: out) rest yel ton cr') eval_mook.loop2 = some x := by
      rw [← h]
      simp only [mookLoopS, icore]
      conv => { rhs; arg 2; unfold eval_mook.loop2 }
      simp [nock_exec, listNoun, Frame.toNoun, harm, eval_rend.arm, hR]
    obtain ⟨v, m2, hm2⟩ := ih (tank :: out) cr' hc' x h'
    refine ⟨v, max m1 m2, fun m hm' => ?_⟩
    simp [evalMookLoop, hm1 m (by omega), hm2 m (by omega)]


/-- The cord of the `%lose` frame that `+eval-mook` puts in a long trace,
`(crip "[skipped {(scow %ud (sub yel 1.024))} frames]")`, as the formula
that computes it on the subject `[yel gate]`. -/
def mookMsgF : Noun :=
  (C (A 8) (C (C (A 9) (C (A 40414) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 1) eval_mook.loop1) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))) (C (A 0) (A 2))))))))

/-- The cord of `+eval-mook` is `Lib.skipMsg`, as `SkipMsgIs` says of the cord
of `+mook`.  Not proved: `+scow` and `+crip` are not. -/
def EvalMookMsgIs (lib : Lib) : Prop :=
  ∀ (yel : Nat) (ton cr : Noun), CorIn cr → 1024 < yel →
    nock (C (A yel) (C eval_mook.battery (C ton (icore cr)))) mookMsgF = some (lib.skipMsg (yel - 1024))

theorem appendN_cons_listN (l l' : List Noun) (x : Noun) :
    appendN l (C x (listN l')) = listN (l ++ x :: l') := by
  rw [← listN_cons, appendN_listN]

/-- The gate of `+eval-mook` slammed on a tone in `icore cr`. -/
abbrev mookS (cr : Noun) (ton : Tone) : Noun := C eval_mook.battery (C ton.toNoun (icore cr))

set_option maxHeartbeats 8000000 in
/-- What the model's `evalMook` returns at level `m`, the pill's `+eval-mook`
returns. -/
theorem eval_mook_le (lib : Lib) (hslam : SlamIsNock lib)
    (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
    (hpk : ∀ cr, CorIn cr → PokeIs pk cr) (hrb : RendBaseIs lib layer4)
    (hst : SoftTankIs lib layer4) (hm : SkipMsgIs lib layer4) (hlist : ListMoldIs)
    (hmsg : EvalMookMsgIs lib) (cr : Noun) (hc : CorIn cr) (m : Nat) (ton : Tone) (r : Toon × Noun)
    (h : evalMook lib (SkaModel.interp lib pk m) m cr ton = some r) :
    nock (mookS cr ton) eval_mook.battery = some (C r.1.toNoun r.2) ∧ CorIn r.2 := by
  rcases ton with p | p | tr
  · simp only [evalMook, Option.some.injEq] at h
    subst h
    refine ⟨?_, hc⟩
    nock_open eval_mook.battery
    simp [nock_exec, Tone.toNoun, Toon.toNoun]
  · simp only [evalMook, Option.some.injEq] at h
    subst h
    refine ⟨?_, hc⟩
    nock_open eval_mook.battery
    simp [nock_exec, Tone.toNoun, Toon.toNoun]
  simp only [evalMook, Option.map_eq_some_iff] at h
  obtain ⟨⟨out, cr'⟩, e1, rfl⟩ := h
  obtain ⟨hL, hC⟩ := eval_mook_loop_le lib hslam pk hpk hrb hst hm hlist m (A tr.length)
    (Tone.two tr).toNoun _ [] cr hc _ e1
  refine ⟨?_, hC⟩
  have hl2 : slot? read.layer2.axis (icore cr) = some layer2 := hc.1
  have hl1 := slot_tail_of hc.1 layer2_layer1
  simp only [read.layer2.axis, icore, Nat.reduceMul, Nat.reduceAdd, nock_exec] at hl2 hl1
  obtain ⟨_, hsub, _, _, _, _, hgth, _⟩ := Hoon.arith_layer1
  have hdec : Below DecIn layer2 := hsub.2
  simp only [mookLoopS, icore, listNoun_eq_listN, List.map_reverse, Tone.toNoun] at hL
  have hmsg' := hmsg tr.length (Tone.two tr).toNoun cr hc
  simp only [Tone.toNoun, icore, listNoun_eq_listN] at hmsg'
  simp only [mookS, Tone.toNoun, icore, listNoun_eq_listN]
  nock_open eval_mook.battery
  by_cases hlen : 1024 < tr.length
  · have hmsg'' := hmsg' hlen
    simp [mookMsgF, nock_exec] at hmsg''
    simp [nock_exec, hl2, hl1, lent.arm_at, weld.arm_at,
      scag.arm_at, slag.arm_at, flop.arm_at, hgth, hsub, lent_arm, lent_gate, gth_arm,
      gth_gate _ hgth.2, weld_arm, weld_gate, scag_arm, scag_gate _ hdec, slag_arm,
      slag_gate _ hdec, sub_arm, sub_gate _ hsub.2 512 tr.length (by omega), hlen, hmsg'',
      flop_arm]
    simp only [skip, hlen, if_true] at hL
    rw [← listN_cons, appendN_listN]
    simpa [flop_gate _ homoIn_layer2, Toon.toNoun, listNoun_eq_listN, Frame.toNoun, Tag.lose] using hL
  · simp [nock_exec, hl2, hl1, lent.arm_at, flop.arm_at, hgth,
      lent_arm, lent_gate, gth_arm, gth_gate _ hgth.2, hlen, flop_arm,
      flop_gate _ homoIn_layer2]
    simp only [skip, hlen, if_false] at hL
    simpa [Toon.toNoun, listNoun_eq_listN] using hL


set_option maxHeartbeats 8000000 in
/-- What the pill's `+eval-mook` returns, the model's `evalMook` returns from
some level on. -/
theorem eval_mook_ge (lib : Lib) (hslam : SlamIsNock lib)
    (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
    (hpk : ∀ cr, CorIn cr → PokeIs pk cr) (hrb : RendBaseIs lib layer4)
    (hst : SoftTankIs lib layer4) (hm : SkipMsgIs lib layer4) (hlist : ListMoldIs)
    (hmsg : EvalMookMsgIs lib) (hbad : ∀ cr, CorIn cr → PokeDireBad cr) (cr : Noun)
    (hc : CorIn cr) (ton : Tone) (x : Noun) (h : nock (mookS cr ton) eval_mook.battery = some x) :
    ∃ v, Ev (fun m => evalMook lib (SkaModel.interp lib pk m) m cr ton) v := by
  rcases ton with p | p | tr
  · exact ⟨(Toon.zero p, cr), 0, fun m _ => rfl⟩
  · exact ⟨(Toon.one p, cr), 0, fun m _ => rfl⟩
  have hl2 : slot? read.layer2.axis (icore cr) = some layer2 := hc.1
  have hl1 := slot_tail_of hc.1 layer2_layer1
  simp only [read.layer2.axis, icore, Nat.reduceMul, Nat.reduceAdd, nock_exec] at hl2 hl1
  obtain ⟨_, hsub, _, _, _, _, hgth, _⟩ := Hoon.arith_layer1
  have hdec : Below DecIn layer2 := hsub.2
  have hmsg' := hmsg tr.length (Tone.two tr).toNoun cr hc
  simp only [Tone.toNoun, icore, listNoun_eq_listN] at hmsg'
  simp only [mookS, Tone.toNoun, icore, listNoun_eq_listN] at h
  conv at h => { lhs; arg 2; unfold eval_mook.battery }
  have hL : nock (mookLoopS [] (skip lib (fun m => (Tag.lose, m)) tr).reverse (A tr.length)
      (Tone.two tr).toNoun cr) eval_mook.loop2 = some x := by
    rw [← h]
    simp only [mookLoopS, Tone.toNoun, icore, listNoun_eq_listN]
    by_cases hlen : 1024 < tr.length
    · have hmsg'' := hmsg' hlen
      simp [mookMsgF, nock_exec] at hmsg''
      simp [nock_exec, hl2, hl1, lent.arm_at, weld.arm_at, scag.arm_at, slag.arm_at, flop.arm_at,
        hgth, hsub, lent_arm, lent_gate, gth_arm, gth_gate _ hgth.2, weld_arm, weld_gate, scag_arm,
        scag_gate _ hdec, slag_arm, slag_gate _ hdec, sub_arm,
        sub_gate _ hsub.2 512 tr.length (by omega), hlen, hmsg'', flop_arm,
        flop_gate _ homoIn_layer2, appendN_cons_listN, skip, Frame.toNoun, Tag.lose]
    · simp [nock_exec, hl2, hl1, lent.arm_at, flop.arm_at, hgth, lent_arm, lent_gate, gth_arm,
        gth_gate _ hgth.2, hlen, flop_arm, flop_gate _ homoIn_layer2, skip]
  obtain ⟨⟨out, cr'⟩, m0, hm0⟩ :=
    eval_mook_loop_ge lib hslam pk hpk hrb hst hm hlist hbad _ _ _ [] cr hc x hL
  exact ⟨(Toon.two out, cr'), m0, fun m hm' => by simp [evalMook, hm0 m hm']⟩


/-- The pill's `+eval-mook` returns `x` exactly when the model's `evalMook`
returns, at some level, a toon and a core that `x` encodes. -/
theorem eval_mook_iff (lib : Lib) (hslam : SlamIsNock lib)
    (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
    (hpk : ∀ cr, CorIn cr → PokeIs pk cr) (hrb : RendBaseIs lib layer4)
    (hst : SoftTankIs lib layer4) (hm : SkipMsgIs lib layer4) (hlist : ListMoldIs)
    (hmsg : EvalMookMsgIs lib) (hbad : ∀ cr, CorIn cr → PokeDireBad cr) (cr : Noun)
    (hc : CorIn cr) (ton : Tone) (x : Noun) :
    nock (mookS cr ton) eval_mook.battery = some x ↔
      ∃ toon cr' m, x = C toon.toNoun cr' ∧
        evalMook lib (SkaModel.interp lib pk m) m cr ton = some (toon, cr') := by
  constructor
  · intro h
    obtain ⟨⟨toon, cr'⟩, m0, hm0⟩ := eval_mook_ge lib hslam pk hpk hrb hst hm hlist hmsg hbad cr hc ton x h
    have hl := (eval_mook_le lib hslam pk hpk hrb hst hm hlist hmsg cr hc m0 ton _
      (hm0 m0 (Nat.le_refl _))).1
    rw [h, Option.some.injEq] at hl
    exact ⟨toon, cr', m0, hl, hm0 m0 (Nat.le_refl _)⟩
  · rintro ⟨toon, cr', m, rfl, e⟩
    exact (eval_mook_le lib hslam pk hpk hrb hst hm hlist hmsg cr hc m ton _ e).1

end Compiler
end Formalization
