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
    (htop : ∀ vu vf, SkaModel.read u regs = some vu → SkaModel.read f regs = some vf →
      nock (topS cr vu vf scry) eval_top.battery = (O.nok cr vu vf scry).map resN)
    (hgood : ∀ vu vf r, SkaModel.read u regs = some vu → SkaModel.read f regs = some vf →
      O.nok cr vu vf scry = some r → CorIn r.2) :
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
  have ht := htop vu vf e1 e2
  cases e3 : O.nok cr vu vf scry with
  | none =>
    rw [e3] at ht
    nock_open eval_pole.battery
    simp [nock_exec, Pole.toNoun, Tag.nok, hld, e1, e2, e3, execPole, htarm, ht]
  | some r =>
    obtain ⟨ton, cr'⟩ := r
    have hc' := hgood vu vf _ e1 e2 e3
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
    (O : Oracle Noun) (nk : Noun → Noun → Noun → Noun → Option (Tone × Noun))
    (scry : Noun) (a : Bell) (v : List Nat) (d : Nat) (regs : TreapMap mugF Noun) (trace : Trace)
    (hO : ∀ b c new cr' vs b0, pk cr (Ovum.dire a false) = some (SkaModel.Prod.ir b c new, cr') →
      v.mapM (SkaModel.read · regs) = some vs → HoonMap.get c.blocks 0 = some b0 →
      nock (blobS cr' (regsOf vs) trace b0 c [] scry) eval_blob.battery
        = (execBlob lib O c scry cr' (regsOf vs) trace b0 []).map resN ∧
      ∀ r, execBlob lib O c scry cr' (regsOf vs) trace b0 [] = some r → CorIn r.2) :
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
  obtain ⟨hb, hbg⟩ := hO b c new cr' vs b0 e1 e2 e3
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
    (O : Oracle Noun) (nk : Noun → Noun → Noun → Noun → Option (Tone × Noun))
    (scry : Noun) (a : Bell) (sr : Nat) (d : Nat) (regs : TreapMap mugF Noun) (trace : Trace)
    (hO : ∀ b c new cr' vs0 b0, pk cr (Ovum.dire a true) = some (SkaModel.Prod.ir b c new, cr') →
      SkaModel.read sr regs = some vs0 → HoonMap.get c.blocks 0 = some b0 →
      nock (blobS cr' (regsOf [vs0]) trace b0 c [] scry) eval_blob.battery
        = (execBlob lib O c scry cr' (regsOf [vs0]) trace b0 []).map resN ∧
      ∀ r, execBlob lib O c scry cr' (regsOf [vs0]) trace b0 [] = some r → CorIn r.2) :
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
  obtain ⟨hb, hbg⟩ := hO b c new cr' vs0 b0 e1 e2 e3
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

/-! ## Every op -/

/-- `+eval-top` is the oracle's `nok` on the cores that keep what the
interpreter reads, and returns such cores. -/
def TopIs (O : Oracle Noun) (cr scry : Noun) : Prop :=
  (∀ vu vf, nock (topS cr vu vf scry) eval_top.battery = (O.nok cr vu vf scry).map resN) ∧
    ∀ vu vf r, O.nok cr vu vf scry = some r → CorIn r.2

theorem local_map (cr : Noun) (lib : Lib) (scry : Noun) (pole : Pole) (regs : TreapMap mugF Noun)
    (trace : Trace) :
    ((localPole lib scry pole regs trace).map fun r => (r.1, r.2.1, r.2.2, cr)).map poleOutS
      = (localPole lib scry pole regs trace).map (poleOut cr) := by
  cases localPole lib scry pole regs trace <;> rfl

/-- `+eval-pole` on every op computes `execPole`, with the interpreter's
calls as the oracle: a call is `callBody` over an oracle that `+eval-blob`
computes, an indirect call what `+eval-top` computes. -/
theorem eval_pole_gate (cr : Noun) (hc : CorIn cr) (lib : Lib) (hslam : SlamIsNock lib)
    (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun)) (hpk : PokeIs pk cr)
    (Ob : Oracle Noun) (hO : BlobIs lib Ob) (nk : Noun → Noun → Noun → Noun → Option (Tone × Noun))
    (scry : Noun) (htop : TopIs ⟨callBody lib pk Ob, nk⟩ cr scry) (pole : Pole)
    (regs : TreapMap mugF Noun) (trace : Trace) :
    nock (poleS cr pole regs trace scry) eval_pole.battery
      = (execPole lib ⟨callBody lib pk Ob, nk⟩ scry cr pole regs trace).map poleOutS := by
  have hcor : slot? 3 (icore cr) = some cr := by simp [nock_exec]
  have hpi := evalPoleIn_icore hc
  have hl2 : slot? read.layer2.axis (icore cr) = some layer2 := hc
  cases pole with
  | nok u f d =>
    exact eval_pole_nok cr hc lib _ scry u f d regs trace (fun vu vf _ _ => htop.1 vu vf)
      (fun vu vf r _ _ => htop.2 vu vf r)
  | cal a v d =>
    exact eval_pole_cal cr hc lib pk hpk Ob nk scry a v d regs trace
      (fun _ c _ cr' vs b0 e1 _ _ => hO cr' (hpk.2 _ _ e1) (regsOf vs) trace b0 c [] scry)
  | caf a v d n =>
    rw [eval_pole_caf, eval_pole_cal cr hc lib pk hpk Ob nk scry a v d regs trace
      (fun _ c _ cr' vs b0 e1 _ _ => hO cr' (hpk.2 _ _ e1) (regsOf vs) trace b0 c [] scry)]; rfl
  | cam a v d k =>
    rw [eval_pole_cam, eval_pole_cal cr hc lib pk hpk Ob nk scry a v d regs trace
      (fun _ c _ cr' vs b0 e1 _ _ => hO cr' (hpk.2 _ _ e1) (regsOf vs) trace b0 c [] scry)]; rfl
  | csl a sr d =>
    exact eval_pole_csl cr hc lib pk hpk Ob nk scry a sr d regs trace
      (fun _ c _ cr' vs0 b0 e1 _ _ => hO cr' (hpk.2 _ _ e1) (regsOf [vs0]) trace b0 c [] scry)
  | csf a sr d n =>
    rw [eval_pole_csf, eval_pole_csl cr hc lib pk hpk Ob nk scry a sr d regs trace
      (fun _ c _ cr' vs0 b0 e1 _ _ => hO cr' (hpk.2 _ _ e1) (regsOf [vs0]) trace b0 c [] scry)]; rfl
  | csm a sr d k =>
    rw [eval_pole_csm, eval_pole_csl cr hc lib pk hpk Ob nk scry a sr d regs trace
      (fun _ c _ cr' vs0 b0 e1 _ _ => hO cr' (hpk.2 _ _ e1) (regsOf [vs0]) trace b0 c [] scry)]; rfl
  | hmp a v f =>
    rw [eval_pole_hmp (icore cr) cr hcor hpi layer2 hl2 turn.arm_at homoIn_layer2 lib scry a v f
      regs trace]
    exact (local_map cr lib scry _ regs trace).symm
  | spy e p d =>
    rw [eval_pole_spy (icore cr) cr hcor hpi lib hslam scry e p d regs trace]
    exact (local_map cr lib scry _ regs trace).symm
  | _ =>
    rw [eval_pole_local (icore cr) cr hcor hpi lib scry _ (by simp [PlainLocal]) regs trace]
    exact (local_map cr lib scry _ regs trace).symm

/-! ## What the model returns, the pill returns -/

/-- The calls of `O` are among those of `callBody` over `Ob`. -/
def CallLe (lib : Lib) (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
    (Ob : Oracle Noun) (O : Oracle Noun) : Prop :=
  ∀ cr a mono vs trace scry r, O.call cr a mono vs trace scry = some r →
    callBody lib pk Ob cr a mono vs trace scry = some r

/-- What `execBlob` with the oracle `O` returns, the pill's `+eval-blob`
returns, on the cores that keep what the interpreter reads; and it returns such
cores. -/
def BlobLe (lib : Lib) (O : Oracle Noun) : Prop :=
  ∀ cr, CorIn cr → ∀ regs trace b s params scry r,
    execBlob lib O s scry cr regs trace b params = some r →
    nock (blobS cr regs trace b s params scry) eval_blob.battery = some (resN r) ∧ CorIn r.2

/-- What the oracle's `nok` returns, the pill's `+eval-top` returns. -/
def TopLe (O : Oracle Noun) : Prop :=
  ∀ cr, CorIn cr → ∀ vu vf scry r, O.nok cr vu vf scry = some r →
    nock (topS cr vu vf scry) eval_top.battery = some (resN r) ∧ CorIn r.2

theorem eval_pole_nok_le (cr : Noun) (hc : CorIn cr) (lib : Lib) (O : Oracle Noun) (hnok : TopLe O)
    (scry : Noun) (u f d : Nat) (regs : TreapMap mugF Noun) (trace : Trace) (r)
    (h : execPole lib O scry cr (Pole.nok u f d) regs trace = some r) :
    nock (poleS cr (Pole.nok u f d) regs trace scry) eval_pole.battery = some (poleOutS r) ∧
      CorIn r.2.2.2 := by
  simp only [execPole, Option.bind_eq_some_iff] at h
  obtain ⟨vu, e1, vf, e2, ⟨ton, cr'⟩, e3, h⟩ := h
  obtain ⟨hT, hC⟩ := hnok cr hc vu vf scry _ e3
  refine ⟨?_, ?_⟩
  · rw [eval_pole_nok cr hc lib O scry u f d regs trace
      (fun vu' vf' e1' e2' => by
        rw [e1, Option.some.injEq] at e1'; rw [e2, Option.some.injEq] at e2'
        subst e1' e2'; rw [hT, e3]; rfl)
      (fun vu' vf' r' e1' e2' e3' => by
        rw [e1, Option.some.injEq] at e1'; rw [e2, Option.some.injEq] at e2'
        subst e1' e2'; rw [e3, Option.some.injEq] at e3'; subst e3'; exact hC)]
    simp only [execPole, e1, e2, e3, Option.bind_some]
    rw [h]; rfl
  · cases ton <;> simp at h <;> subst h <;> exact hC

/-- From a call that the model makes: the poke, the callee's block `0` and its
run. -/
theorem callBody_some {lib : Lib} {pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun)}
    {Ob : Oracle Noun} {cr : Noun} {a : Bell} {mono : Bool} {vs : List Noun} {trace : Trace}
    {scry : Noun} {r : Tone × Noun} (h : callBody lib pk Ob cr a mono vs trace scry = some r) :
    ∃ b c new cr' b0, pk cr (Ovum.dire a mono) = some (SkaModel.Prod.ir b c new, cr') ∧
      HoonMap.get c.blocks 0 = some b0 ∧
      execBlob lib Ob c scry cr' (regsOf vs) trace b0 [] = some r := by
  simp only [callBody, Option.bind_eq_some_iff] at h
  obtain ⟨⟨p, cr'⟩, e1, h⟩ := h
  rcases p with _ | ⟨b, c, new⟩ | _
  · simp at h
  · simp only [execEntry, Option.bind_eq_some_iff] at h
    obtain ⟨b0, e2, h⟩ := h
    exact ⟨b, c, new, cr', b0, e1, e2, h⟩
  · simp at h

theorem eval_pole_cal_le (cr : Noun) (hc : CorIn cr) (lib : Lib)
    (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun)) (hpk : PokeIs pk cr)
    (Ob : Oracle Noun) (hOb : BlobLe lib Ob) (O : Oracle Noun) (hcall : CallLe lib pk Ob O)
    (scry : Noun) (a : Bell) (v : List Nat) (d : Nat) (regs : TreapMap mugF Noun) (trace : Trace) (r)
    (h : execPole lib O scry cr (Pole.cal a v d) regs trace = some r) :
    nock (poleS cr (Pole.cal a v d) regs trace scry) eval_pole.battery = some (poleOutS r) ∧
      CorIn r.2.2.2 := by
  simp only [execPole, Option.bind_eq_some_iff] at h
  obtain ⟨vs, e2, ⟨ton, cr''⟩, e3, h⟩ := h
  have e3' := hcall _ _ _ _ _ _ _ e3
  obtain ⟨b, c, new, cr', b0, e1, e4, e5⟩ := callBody_some e3'
  obtain ⟨hB, hC⟩ := hOb cr' (hpk.2 _ _ e1) _ _ _ _ _ _ _ e5
  refine ⟨?_, ?_⟩
  · rw [eval_pole_cal cr hc lib pk hpk Ob O.nok scry a v d regs trace
      (fun b' c' new' cr₁ vs' b0' e1' e2' e4' => by
        rw [e1, Option.some.injEq, Prod.mk.injEq, SkaModel.Prod.ir.injEq] at e1'
        obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e1'
        rw [e2, Option.some.injEq] at e2'; subst e2'
        rw [e4, Option.some.injEq] at e4'; subst e4'
        refine ⟨by rw [hB, e5]; rfl, fun r' e => ?_⟩
        rw [e5, Option.some.injEq] at e; subst e; exact hC)]
    simp only [execPole, e2, e3', Option.bind_some]
    rw [h]; rfl
  · cases ton <;> simp [afterCall] at h <;> subst h <;> exact hC

theorem eval_pole_csl_le (cr : Noun) (hc : CorIn cr) (lib : Lib)
    (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun)) (hpk : PokeIs pk cr)
    (Ob : Oracle Noun) (hOb : BlobLe lib Ob) (O : Oracle Noun) (hcall : CallLe lib pk Ob O)
    (scry : Noun) (a : Bell) (sr : Nat) (d : Nat) (regs : TreapMap mugF Noun) (trace : Trace) (r)
    (h : execPole lib O scry cr (Pole.csl a sr d) regs trace = some r) :
    nock (poleS cr (Pole.csl a sr d) regs trace scry) eval_pole.battery = some (poleOutS r) ∧
      CorIn r.2.2.2 := by
  simp only [execPole, Option.bind_eq_some_iff] at h
  obtain ⟨vs0, e2, ⟨ton, cr''⟩, e3, h⟩ := h
  have e3' := hcall _ _ _ _ _ _ _ e3
  obtain ⟨b, c, new, cr', b0, e1, e4, e5⟩ := callBody_some e3'
  obtain ⟨hB, hC⟩ := hOb cr' (hpk.2 _ _ e1) _ _ _ _ _ _ _ e5
  refine ⟨?_, ?_⟩
  · rw [eval_pole_csl cr hc lib pk hpk Ob O.nok scry a sr d regs trace
      (fun b' c' new' cr₁ vs' b0' e1' e2' e4' => by
        rw [e1, Option.some.injEq, Prod.mk.injEq, SkaModel.Prod.ir.injEq] at e1'
        obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e1'
        rw [e2, Option.some.injEq] at e2'; subst e2'
        rw [e4, Option.some.injEq] at e4'; subst e4'
        refine ⟨by rw [hB, e5]; rfl, fun r' e => ?_⟩
        rw [e5, Option.some.injEq] at e; subst e; exact hC)]
    simp only [execPole, e2, e3', Option.bind_some]
    rw [h]; rfl
  · cases ton <;> simp [afterCall] at h <;> subst h <;> exact hC

/-- What `execPole` returns, the pill's `+eval-pole` returns, on every op. -/
theorem eval_pole_le (cr : Noun) (hc : CorIn cr) (lib : Lib) (hslam : SlamIsNock lib)
    (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun)) (hpk : PokeIs pk cr)
    (Ob : Oracle Noun) (hOb : BlobLe lib Ob) (O : Oracle Noun) (hcall : CallLe lib pk Ob O)
    (hnok : TopLe O) (scry : Noun) (pole : Pole) (regs : TreapMap mugF Noun) (trace : Trace) (r)
    (h : execPole lib O scry cr pole regs trace = some r) :
    nock (poleS cr pole regs trace scry) eval_pole.battery = some (poleOutS r) ∧
      CorIn r.2.2.2 := by
  have hcor : slot? 3 (icore cr) = some cr := by simp [nock_exec]
  have hpi := evalPoleIn_icore hc
  have hl2 : slot? read.layer2.axis (icore cr) = some layer2 := hc
  have loc : ∀ (e : nock (poleS cr pole regs trace scry) eval_pole.battery
      = (localPole lib scry pole regs trace).map (poleOut cr)),
      execPole lib O scry cr pole regs trace = (localPole lib scry pole regs trace).map
        (fun r => (r.1, r.2.1, r.2.2, cr)) →
      nock (poleS cr pole regs trace scry) eval_pole.battery = some (poleOutS r) ∧
        CorIn r.2.2.2 := by
    intro e hx
    rw [hx] at h
    obtain ⟨r', h1, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [e, h1]
    exact ⟨rfl, hc⟩
  cases pole with
  | nok u f d => exact eval_pole_nok_le cr hc lib O hnok scry u f d regs trace r h
  | cal a v d => exact eval_pole_cal_le cr hc lib pk hpk Ob hOb O hcall scry a v d regs trace r h
  | caf a v d n =>
    rw [eval_pole_caf]; exact eval_pole_cal_le cr hc lib pk hpk Ob hOb O hcall scry a v d regs trace r h
  | cam a v d k =>
    rw [eval_pole_cam]; exact eval_pole_cal_le cr hc lib pk hpk Ob hOb O hcall scry a v d regs trace r h
  | csl a sr d => exact eval_pole_csl_le cr hc lib pk hpk Ob hOb O hcall scry a sr d regs trace r h
  | csf a sr d n =>
    rw [eval_pole_csf]; exact eval_pole_csl_le cr hc lib pk hpk Ob hOb O hcall scry a sr d regs trace r h
  | csm a sr d k =>
    rw [eval_pole_csm]; exact eval_pole_csl_le cr hc lib pk hpk Ob hOb O hcall scry a sr d regs trace r h
  | hmp a v f =>
    exact loc (eval_pole_hmp (icore cr) cr hcor hpi layer2 hl2 turn.arm_at homoIn_layer2 lib scry a v f
      regs trace) rfl
  | spy e p d =>
    exact loc (eval_pole_spy (icore cr) cr hcor hpi lib hslam scry e p d regs trace) rfl
  | _ =>
    exact loc (eval_pole_local (icore cr) cr hcor hpi lib scry _ (by simp [PlainLocal]) regs trace)
      rfl

end Compiler
end Formalization
