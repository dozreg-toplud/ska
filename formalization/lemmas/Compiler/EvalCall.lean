import lemmas.Compiler.EvalPole
import lemmas.Pill.Arm.Eval_blob
import lemmas.Pill.Arm.Eval_top
import lemmas.Compiler.TreapList
import lemmas.Ska.Interp

/-!
# The ops of `+eval-pole` that leave the function

`%nok` slams `+eval-top`, the calls poke the compiler with `%dire` and run the
callee with `+eval-blob`.  Here what `+eval-top` and `+eval-blob` compute is a
parameter: an oracle of `Interp.lean` whose answers are what the pill's gates
return on the same nouns.  The compiler's state is the noun `cr` of the
compiler's core, the tail of the interpreter core `icore cr`; each call
returns a new one, which the gate installs (`10 [31 0 5]`) before it goes on.

What the arms read through `cr` is layer 2 at `read.layer2.axis` of the
interpreter core (`CorIn`): the oracles must return cores that keep it.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

/-- The interpreter core with the compiler's core `cr` as its tail. -/
abbrev icore (cr : Noun) : Noun := C interp.battery cr

/-- What the interpreter's arms read through the compiler's core: layer 2. -/
def CorIn (cr : Noun) : Prop := slot? read.layer2.axis (icore cr) = some layer2

theorem regsIn_icore {cr : Noun} (h : CorIn cr) : RegsIn mugF (icore cr) :=
  ⟨layer2, h, by.arm_at, need.arm_at, someIn_layer2, gorIn_morIn_layer2.1, gorIn_morIn_layer2.2⟩


theorem evalPoleIn_icore {cr : Noun} (h : CorIn cr) : EvalPoleIn (icore cr) := by
  refine ⟨?_, ?_, ?_, regsIn_icore h⟩
  · have := move.arm_at; rw [interp_eq] at this; simpa [move.axis, nock_exec] using this
  · have := read.arm_at; rw [interp_eq] at this; simpa [read.axis, nock_exec] using this
  · have := store.arm_at; rw [interp_eq] at this; simpa [store.axis, nock_exec] using this

/-- The product of `+eval-pole` with the compiler's core it ends with. -/
def poleOutS (r : Tone × TreapMap mugF Noun × Trace × Noun) : Noun :=
  C r.1.toNoun (C (HoonMap.toNoun id r.2.1) (C (listNoun Frame.toNoun r.2.2.1) r.2.2.2))

/-- The noun of a result of `+eval-top` or `+eval-blob`: `[tone cor]`. -/
def resN (r : Tone × Noun) : Noun := C r.1.toNoun r.2

/-- The sample of `+eval-pole`, in its context `icore cr`. -/
abbrev poleS (cr : Noun) (pole : Pole) (regs : TreapMap mugF Noun) (trace : Trace) (scry : Noun) :
    Noun :=
  C eval_pole.battery (C (C pole.toNoun
    (C (C (HoonMap.toNoun id regs) (listNoun Frame.toNoun trace)) scry)) (icore cr))

/-- The gate of `+eval-top` slammed on `[[u f] scry]` in `icore cr`. -/
abbrev topS (cr u f scry : Noun) : Noun :=
  C eval_top.battery (C (C (C u f) scry) (icore cr))

@[nock_exec] theorem eval_top_arm (c : Noun) :
    nock c eval_top.arm = some (C eval_top.battery (C (C (C (A 0) (A 0)) (A 0)) c)) := by
  nock_open eval_top.arm; simp only [nock_exec]

theorem weld_listNoun (c : Noun) (l l' : Trace) :
    nock (C weld.battery (C (C (listNoun Frame.toNoun l) (listNoun Frame.toNoun l')) c))
      weld.battery = some (listNoun Frame.toNoun (l ++ l')) := by
  rw [listNoun_eq_listN, listNoun_eq_listN, weld_gate_list, listNoun_eq_listN, List.map_append]

set_option maxHeartbeats 4000000 in
/-- `+eval-pole` on `%nok`: `+eval-top` on the two registers, whose tone is
stored, ends the block or has the trace welded on. -/
theorem eval_pole_nok (cr : Noun) (hc : CorIn cr) (lib : Lib) (O : Oracle Noun) (scry : Noun)
    (u f d : Nat) (regs : TreapMap mugF Noun) (trace : Trace)
    (htop : ∀ vu vf, nock (topS cr vu vf scry) eval_top.battery = (O.nok cr vu vf scry).map resN)
    (hgood : ∀ vu vf r, O.nok cr vu vf scry = some r → CorIn r.2) :
    nock (poleS cr (Pole.nok u f d) regs trace scry) eval_pole.battery
      = (execPole lib O scry cr (Pole.nok u f d) regs trace).map poleOutS := by
  have hpi := evalPoleIn_icore hc
  obtain ⟨_, hrd, _, hrc⟩ := hpi
  have hld := eval_pole_load (icore cr) hrd hrc regs
  have htarm := eval_top.arm_at cr
  simp only [eval_top.axis] at htarm
  cases e1 : SkaModel.read u regs with
  | none =>
    nock_open eval_pole.battery
    simp [nock_exec, Pole.toNoun, Tag.nok, hld, e1, execPole, htarm]
  | some vu =>
  cases e2 : SkaModel.read f regs with
  | none =>
    nock_open eval_pole.battery
    simp [nock_exec, Pole.toNoun, Tag.nok, hld, e1, e2, execPole, htarm]
  | some vf =>
  have ht := htop vu vf
  cases e3 : O.nok cr vu vf scry with
  | none =>
    rw [e3] at ht
    nock_open eval_pole.battery
    simp [nock_exec, Pole.toNoun, Tag.nok, hld, e1, e2, e3, execPole, htarm, ht]
  | some r =>
    obtain ⟨ton, cr'⟩ := r
    have hc' := hgood vu vf _ e3
    rw [e3] at ht
    have hsm := store_model (icore cr') (regsIn_icore hc')
    have hl2 : slot? read.layer2.axis (icore cr') = some layer2 := hc'
    simp only [read.layer2.axis, icore, nock_exec] at hl2
    rcases ton with p | b | tr
    · nock_open eval_pole.battery
      simp [nock_exec, Pole.toNoun, Tag.nok, hld, e1, e2, e3, execPole, htarm, ht, resN,
        Tone.toNoun, hsm, poleOutS, store_arm]
    · nock_open eval_pole.battery
      simp [nock_exec, Pole.toNoun, Tag.nok, hld, e1, e2, e3, execPole, htarm, ht, resN,
        Tone.toNoun, poleOutS]
    · nock_open eval_pole.battery
      simp [nock_exec, Pole.toNoun, Tag.nok, hld, e1, e2, e3, execPole, htarm, ht, resN,
        Tone.toNoun, poleOutS, hl2, weld.arm_at, weld_arm, weld_listNoun]

/-! ## The calls -/

/-- The axis of `+poke` in the compiler's core, `axPoke` of `core/Statement.lean`
(which cannot be imported here: it is a module over the plain `core/Pill.lean`). -/
abbrev poke.axis : Nat := 23

/-- `(poke ovo)` on the compiler's core `cr`, as the interpreter's arms run it:
pull the arm at `poke.axis`, put the sample in, kick. -/
def pokeN (cr ovo : Noun) : Option Noun :=
  ((slot? poke.axis cr).bind fun a => nock cr a).bind fun g =>
    (edit? 6 ovo g).bind fun g' => (slot? 2 g').bind fun f => nock g' f

/-- The poke of `cr` is the model `pk` on every ovum, and every core it returns
keeps what the interpreter reads through it. -/
def PokeIs (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun)) (cr : Noun) : Prop :=
  (∀ ov, pokeN cr ov.toNoun = (pk cr ov).map fun r => C r.1.toNoun r.2) ∧
    ∀ ov r, pk cr ov = some r → CorIn r.2

/-- The gate of `+eval-blob` on `[[regs trace] b s params scry]` in `icore cr`. -/
abbrev blobS (cr : Noun) (regs : TreapMap mugF Noun) (trace : Trace) (b : Blob)
    (s : Straight (TreapMap mugF)) (params : List (Option Nat)) (scry : Noun) : Noun :=
  C eval_blob.battery (C (C (C (HoonMap.toNoun id regs) (listNoun Frame.toNoun trace))
    (C b.toNoun (C s.toNoun (C (argsN params) scry)))) (icore cr))

/-- `+eval-blob` is the model `execBlob` with the oracle `O`, on every core
that keeps what the interpreter reads, and returns such cores. -/
def BlobIs (lib : Lib) (O : Oracle Noun) : Prop :=
  ∀ cr, CorIn cr → ∀ regs trace b s params scry,
    nock (blobS cr regs trace b s params scry) eval_blob.battery
      = (execBlob lib O s scry cr regs trace b params).map resN ∧
    ∀ r, execBlob lib O s scry cr regs trace b params = some r → CorIn r.2

theorem regsFrom_toNoun_put (r : Nat) (v : Noun) (vs : List Noun) (out : TreapMap mugF Noun) :
    regsFrom (r + 1) vs (HoonMap.put out r v) = regsFrom r (v :: vs) out := rfl

set_option maxHeartbeats 4000000 in
/-- The loop of `%cal` that puts the values of the registers `v` in the
registers `r, r+1, ...` of `out`, reading them through `+read` of `regs`. -/
theorem eval_pole_loop (cr : Noun) (hc : CorIn cr) (p an : Noun) (d : Nat) (regs : TreapMap mugF Noun)
    (tn scry : Noun) :
    ∀ (v : List Nat) (r : Nat) (out : TreapMap mugF Noun),
    nock (C eval_pole.loop (C (A r) (C (HoonMap.toNoun id out) (C p (C eval_pole.battery
        (C (C (C (A Tag.cal) (C an (C (listNoun A v) (A d)))) (C (C (HoonMap.toNoun id regs) tn) scry))
          (icore cr))))))) eval_pole.loop
      = (v.mapM (SkaModel.read · regs)).map fun vs => HoonMap.toNoun id (regsFrom r vs out) := by
  have hpi := evalPoleIn_icore hc
  obtain ⟨_, hrd, _, hrc⟩ := hpi
  have hld := eval_pole_load (icore cr) hrd hrc regs
  have hl2 : slot? read.layer2.axis (icore cr) = some layer2 := hc
  simp only [read.layer2.axis, icore, nock_exec] at hl2
  obtain ⟨hgor, hmor⟩ := gorIn_morIn_layer2
  intro v
  induction v with
  | nil =>
    intro r out
    nock_open eval_pole.loop
    simp [nock_exec, listNoun, regsFrom]
  | cons x v ih =>
    intro r out
    cases e : SkaModel.read x regs with
    | none =>
      nock_open eval_pole.loop
      simp [nock_exec, listNoun, hld, e]
    | some vx =>
      have hput := putF_hoonMap id out r vx
      simp only [id_eq] at hput
      nock_open eval_pole.loop
      simp [nock_exec, listNoun, hld, e, hl2, by.arm_at, by_arm, by.put.arm_at, put_arm,
        put_gate layer2 ⟨hgor, hmor⟩ _ _ _ _ hput, ih, List.mapM_cons]
      cases List.mapM (fun x => SkaModel.read x regs) v <;> simp [regsFrom]

/-- What `+eval-pole` reads through a core after a call: layer 2, as facts in
the form the executor leaves them. -/
theorem corIn_facts {cr : Noun} (hc : CorIn cr) :
    (∀ r v (regs : TreapMap mugF Noun),
      nock (C store.battery (C (C (A r) (C v (HoonMap.toNoun id regs))) (icore cr))) store.battery
        = some (HoonMap.toNoun id (SkaModel.store r v regs))) ∧
    slot? read.layer2.axis (icore cr) = some layer2 :=
  ⟨store_model (icore cr) (regsIn_icore hc), hc⟩

set_option maxHeartbeats 8000000 in
/-- `+eval-pole` on `%cal`: poke `%dire`, put the arguments in registers
`0 ..`, run block `0` of the callee with `+eval-blob`, and store the product. -/
theorem eval_pole_cal (cr : Noun) (hc : CorIn cr) (lib : Lib)
    (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun)) (hpk : PokeIs pk cr)
    (O : Oracle Noun) (hO : BlobIs lib O) (nk : Noun → Noun → Noun → Noun → Option (Tone × Noun))
    (scry : Noun) (a : Bell) (v : List Nat) (d : Nat) (regs : TreapMap mugF Noun) (trace : Trace) :
    nock (poleS cr (Pole.cal a v d) regs trace scry) eval_pole.battery
      = (execPole lib ⟨callBody lib pk O, nk⟩ scry cr (Pole.cal a v d) regs trace).map poleOutS := by
  obtain ⟨hpkN, hpkG⟩ := hpk
  have hp := hpkN (Ovum.dire a false)
  simp only [pokeN, poke.axis, Ovum.toNoun, flag, Bool.false_eq_true, if_false, Tag.dire] at hp
  cases e1 : pk cr (Ovum.dire a false) with
  | none =>
    rw [e1] at hp
    nock_open eval_pole.battery
    simp [nock_exec, Pole.toNoun, Tag.cal, Tag.nok, Tag.dire, hp, execPole, callBody, e1]
  | some r =>
  obtain ⟨p, cr'⟩ := r
  have hc' := hpkG _ _ e1
  rw [e1] at hp
  have hpi := evalPoleIn_icore hc'
  obtain ⟨_, hrd, _, hrc⟩ := hpi
  have hl2 : slot? read.layer2.axis (icore cr') = some layer2 := hc'
  simp only [read.layer2.axis, icore, nock_exec] at hl2
  have hneed : NeedIn layer2 := need.arm_at
  have hsome := someIn_layer2
  have hgor := gorIn_morIn_layer2.1
  rcases p with _ | ⟨b, c, new⟩ | ps
  · nock_open eval_pole.battery
    simp [nock_exec, Pole.toNoun, Tag.cal, Tag.nok, Tag.dire, hp, execPole, callBody, e1,
      SkaModel.Prod.toNoun]
  rotate_left
  · nock_open eval_pole.battery
    simp [nock_exec, Pole.toNoun, Tag.cal, Tag.nok, Tag.dire, Tag.ir, Tag.drop, hp, execPole,
      callBody, e1, SkaModel.Prod.toNoun]
  have hloop := eval_pole_loop cr' hc' (SkaModel.Prod.toNoun (SkaModel.Prod.ir b c new)) a.toNoun d
    regs (listNoun Frame.toNoun trace) scry v 0 HoonMap.empty
  simp only [SkaModel.Prod.toNoun, Tag.ir, Tag.cal, icore, HoonMap.toNoun_empty, Straight.toNoun] at hloop
  cases e2 : v.mapM (SkaModel.read · regs) with
  | none =>
    rw [e2] at hloop
    nock_open eval_pole.battery
    simp [nock_exec, Pole.toNoun, Tag.cal, Tag.nok, Tag.dire, Tag.ir, hp, execPole, callBody, e1,
      SkaModel.Prod.toNoun, hloop, e2, Straight.toNoun]
  | some vs =>
  rw [e2] at hloop
  simp only [Option.map_some] at hloop
  rw [show regsFrom 0 vs HoonMap.empty = regsOf vs from rfl] at hloop
  have hg := getF_hoonMap Blob.toNoun c.blocks 0
  cases e3 : HoonMap.get c.blocks 0 with
  | none =>
    rw [e3] at hg
    nock_open eval_pole.battery
    simp [nock_exec, Pole.toNoun, Tag.cal, Tag.nok, Tag.dire, Tag.ir, hp, execPole, callBody, e1,
      SkaModel.Prod.toNoun, hloop, e2, Straight.toNoun, hl2, by.arm_at, by_arm, by.got.arm_at,
      got_arm, got_gate_nil layer2 ⟨hneed, hsome, hgor⟩ _ _ hg, execEntry, e3]
  | some b0 =>
  rw [e3] at hg
  obtain ⟨hb, hbg⟩ := hO cr' hc' (regsOf vs) trace b0 c [] scry
  cases e4 : execBlob lib O c scry cr' (regsOf vs) trace b0 [] with
  | none =>
    rw [e4] at hb
    simp only [blobS, icore, Straight.toNoun, argsN, listNoun] at hb
    nock_open eval_pole.battery
    simp [nock_exec, Pole.toNoun, Tag.cal, Tag.nok, Tag.dire, Tag.ir, hp, execPole, callBody, e1,
      SkaModel.Prod.toNoun, hloop, e2, Straight.toNoun, hl2, by.arm_at, by_arm, by.got.arm_at,
      got_arm, got_gate layer2 ⟨hneed, hsome, hgor⟩ _ _ _ hg, execEntry, e3, unitNoun,
      eval_blob.arm, hb, argsN, listNoun, e4]
  | some r =>
  obtain ⟨ton, cr''⟩ := r
  have hc'' := hbg _ e4
  rw [e4] at hb
  simp only [blobS, icore, Straight.toNoun, argsN, listNoun] at hb
  obtain ⟨hsm, hl2''⟩ := corIn_facts hc''
  simp only at hsm hl2''
  rcases ton with q | q | q
  all_goals
    nock_open eval_pole.battery
    simp [nock_exec, Pole.toNoun, Tag.cal, Tag.nok, Tag.dire, Tag.ir, hp, execPole, callBody, e1,
      SkaModel.Prod.toNoun, hloop, e2, Straight.toNoun, hl2, by.arm_at, by_arm, by.got.arm_at,
      got_arm, got_gate layer2 ⟨hneed, hsome, hgor⟩ _ _ _ hg, execEntry, e3, unitNoun,
      eval_blob.arm, hb, argsN, listNoun, resN, Tone.toNoun, afterCall, poleOutS, hsm, e4,
      store_arm]

set_option maxHeartbeats 8000000 in
/-- `+eval-pole` on `%csl`: poke `%dire` for a call whose subject goes whole,
in register `0`, run block `0` of the callee and store the product. -/
theorem eval_pole_csl (cr : Noun) (hc : CorIn cr) (lib : Lib)
    (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun)) (hpk : PokeIs pk cr)
    (O : Oracle Noun) (hO : BlobIs lib O) (nk : Noun → Noun → Noun → Noun → Option (Tone × Noun))
    (scry : Noun) (a : Bell) (sr : Nat) (d : Nat) (regs : TreapMap mugF Noun) (trace : Trace) :
    nock (poleS cr (Pole.csl a sr d) regs trace scry) eval_pole.battery
      = (execPole lib ⟨callBody lib pk O, nk⟩ scry cr (Pole.csl a sr d) regs trace).map poleOutS := by
  obtain ⟨hpkN, hpkG⟩ := hpk
  have hp := hpkN (Ovum.dire a true)
  simp only [pokeN, poke.axis, Ovum.toNoun, flag, if_true, Tag.dire] at hp
  cases e1 : pk cr (Ovum.dire a true) with
  | none =>
    rw [e1] at hp
    nock_open eval_pole.battery
    simp [nock_exec, Pole.toNoun, Tag.csl, Tag.cal, Tag.nok, Tag.dire, hp, execPole, callBody, e1]
  | some r =>
  obtain ⟨p, cr'⟩ := r
  have hc' := hpkG _ _ e1
  rw [e1] at hp
  have hpi := evalPoleIn_icore hc'
  obtain ⟨_, hrd, _, hrc⟩ := hpi
  have hl2 : slot? read.layer2.axis (icore cr') = some layer2 := hc'
  simp only [read.layer2.axis, icore, nock_exec] at hl2
  have hneed : NeedIn layer2 := need.arm_at
  have hsome := someIn_layer2
  have hgor := gorIn_morIn_layer2.1
  rcases p with _ | ⟨b, c, new⟩ | ps
  · nock_open eval_pole.battery
    simp [nock_exec, Pole.toNoun, Tag.csl, Tag.cal, Tag.nok, Tag.dire, hp, execPole, callBody, e1,
      SkaModel.Prod.toNoun]
  rotate_left
  · nock_open eval_pole.battery
    simp [nock_exec, Pole.toNoun, Tag.csl, Tag.cal, Tag.nok, Tag.dire, Tag.ir, Tag.drop, hp, execPole,
      callBody, e1, SkaModel.Prod.toNoun]
  have hpi' := evalPoleIn_icore hc'
  obtain ⟨_, hrd', _, hrc'⟩ := hpi'
  have hld := eval_pole_load (icore cr') hrd' hrc' regs
  cases e2 : SkaModel.read sr regs with
  | none =>
    nock_open eval_pole.battery
    simp [nock_exec, Pole.toNoun, Tag.csl, Tag.csl, Tag.cal, Tag.nok, Tag.dire, Tag.ir, hp, execPole,
      callBody, e1, SkaModel.Prod.toNoun, hld, e2, Straight.toNoun]
  | some vs0 =>
  have hreg : HoonMap.toNoun id (regsOf [vs0] : TreapMap mugF Noun)
      = C (C (A 0) vs0) (C (A 0) (A 0)) := rfl
  have hg := getF_hoonMap Blob.toNoun c.blocks 0
  cases e3 : HoonMap.get c.blocks 0 with
  | none =>
    rw [e3] at hg
    nock_open eval_pole.battery
    simp [nock_exec, Pole.toNoun, Tag.csl, Tag.cal, Tag.nok, Tag.dire, Tag.ir, hp, execPole, callBody, e1,
      SkaModel.Prod.toNoun, hld, e2, hreg, Straight.toNoun, hl2, by.arm_at, by_arm, by.got.arm_at,
      got_arm, got_gate_nil layer2 ⟨hneed, hsome, hgor⟩ _ _ hg, execEntry, e3]
  | some b0 =>
  rw [e3] at hg
  obtain ⟨hb, hbg⟩ := hO cr' hc' (regsOf [vs0]) trace b0 c [] scry
  cases e4 : execBlob lib O c scry cr' (regsOf [vs0]) trace b0 [] with
  | none =>
    rw [e4] at hb
    simp only [blobS, icore, Straight.toNoun, argsN, listNoun, hreg] at hb
    nock_open eval_pole.battery
    simp [nock_exec, Pole.toNoun, Tag.csl, Tag.cal, Tag.nok, Tag.dire, Tag.ir, hp, execPole, callBody, e1,
      SkaModel.Prod.toNoun, hld, e2, hreg, Straight.toNoun, hl2, by.arm_at, by_arm, by.got.arm_at,
      got_arm, got_gate layer2 ⟨hneed, hsome, hgor⟩ _ _ _ hg, execEntry, e3, unitNoun,
      eval_blob.arm, hb, argsN, listNoun, e4]
  | some r =>
  obtain ⟨ton, cr''⟩ := r
  have hc'' := hbg _ e4
  rw [e4] at hb
  simp only [blobS, icore, Straight.toNoun, argsN, listNoun, hreg] at hb
  obtain ⟨hsm, hl2''⟩ := corIn_facts hc''
  simp only at hsm hl2''
  rcases ton with q | q | q
  all_goals
    nock_open eval_pole.battery
    simp [nock_exec, Pole.toNoun, Tag.csl, Tag.cal, Tag.nok, Tag.dire, Tag.ir, hp, execPole, callBody, e1,
      SkaModel.Prod.toNoun, hld, e2, hreg, Straight.toNoun, hl2, by.arm_at, by_arm, by.got.arm_at,
      got_arm, got_gate layer2 ⟨hneed, hsome, hgor⟩ _ _ _ hg, execEntry, e3, unitNoun,
      eval_blob.arm, hb, argsN, listNoun, resN, Tone.toNoun, afterCall, poleOutS, hsm, e4,
      store_arm]

/-- `%caf`, `%cam`, `%csf` and `%csm` run `+eval-pole` again on the plain call. -/
theorem eval_pole_caf (cr : Noun) (a : Bell) (v : List Nat) (d : Nat) (n : Ring)
    (regs : TreapMap mugF Noun) (trace : Trace) (scry : Noun) :
    nock (poleS cr (Pole.caf a v d n) regs trace scry) eval_pole.battery
      = nock (poleS cr (Pole.cal a v d) regs trace scry) eval_pole.battery := by
  nock_open eval_pole.battery
  simp [nock_exec, Pole.toNoun, Tag.caf, Tag.cal, Tag.nok, Tag.imm, Tag.mov, Tag.inc, Tag.con,
    Tag.hed, Tag.tal, Tag.cel, Tag.lob, Tag.equ, Tag.hsp, Tag.hse, Tag.hdp, Tag.hde, Tag.hmp,
    Tag.hme, Tag.hcp, Tag.hce, Tag.spy, Tag.cam, Tag.csl, Tag.csf, Tag.csm]
  rfl

theorem eval_pole_cam (cr : Noun) (a : Bell) (v : List Nat) (d : Nat) (k : Noun)
    (regs : TreapMap mugF Noun) (trace : Trace) (scry : Noun) :
    nock (poleS cr (Pole.cam a v d k) regs trace scry) eval_pole.battery
      = nock (poleS cr (Pole.cal a v d) regs trace scry) eval_pole.battery := by
  nock_open eval_pole.battery
  simp [nock_exec, Pole.toNoun, Tag.caf, Tag.cal, Tag.nok, Tag.imm, Tag.mov, Tag.inc, Tag.con,
    Tag.hed, Tag.tal, Tag.cel, Tag.lob, Tag.equ, Tag.hsp, Tag.hse, Tag.hdp, Tag.hde, Tag.hmp,
    Tag.hme, Tag.hcp, Tag.hce, Tag.spy, Tag.cam, Tag.csl, Tag.csf, Tag.csm]
  rfl

theorem eval_pole_csf (cr : Noun) (a : Bell) (sr d : Nat) (n : Ring)
    (regs : TreapMap mugF Noun) (trace : Trace) (scry : Noun) :
    nock (poleS cr (Pole.csf a sr d n) regs trace scry) eval_pole.battery
      = nock (poleS cr (Pole.csl a sr d) regs trace scry) eval_pole.battery := by
  nock_open eval_pole.battery
  simp [nock_exec, Pole.toNoun, Tag.caf, Tag.cal, Tag.nok, Tag.imm, Tag.mov, Tag.inc, Tag.con,
    Tag.hed, Tag.tal, Tag.cel, Tag.lob, Tag.equ, Tag.hsp, Tag.hse, Tag.hdp, Tag.hde, Tag.hmp,
    Tag.hme, Tag.hcp, Tag.hce, Tag.spy, Tag.cam, Tag.csl, Tag.csf, Tag.csm]
  rfl

theorem eval_pole_csm (cr : Noun) (a : Bell) (sr d : Nat) (k : Noun)
    (regs : TreapMap mugF Noun) (trace : Trace) (scry : Noun) :
    nock (poleS cr (Pole.csm a sr d k) regs trace scry) eval_pole.battery
      = nock (poleS cr (Pole.csl a sr d) regs trace scry) eval_pole.battery := by
  nock_open eval_pole.battery
  simp [nock_exec, Pole.toNoun, Tag.caf, Tag.cal, Tag.nok, Tag.imm, Tag.mov, Tag.inc, Tag.con,
    Tag.hed, Tag.tal, Tag.cel, Tag.lob, Tag.equ, Tag.hsp, Tag.hse, Tag.hdp, Tag.hde, Tag.hmp,
    Tag.hme, Tag.hcp, Tag.hce, Tag.spy, Tag.cam, Tag.csl, Tag.csf, Tag.csm]
  rfl

end Compiler
end Formalization
