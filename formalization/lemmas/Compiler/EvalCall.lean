import lemmas.Compiler.EvalPole
import lemmas.Pill.Arm.Eval_blob
import lemmas.Pill.Arm.Eval_top
import lemmas.Compiler.TreapList

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

end Compiler
end Formalization
