import lemmas.Compiler.HeSock
import lemmas.Pill.Arm.Recursive_call

/-!
`+recursive-call` of the analysis core `ana` against `recursiveCall` of
`lemmas/Ska/CallGraph.lean`, with `+he-sock` given by `heSock`, on call graphs
of `FinMap` (read through `gCore`, as `Ska/Analysis.lean` does).

```hoon
++  recursive-call
  ~%  %recursive-call  ..ride  ~
  |=  [id-kid=identity stk=(list identity) g=callgraph]
  ^-  (unit [?(%rec %he) identity])
  =/  same=@
    %+  roll  stk
    |=  [id=identity acc=@]
    ?.  =(fol.id-kid fol.id)  acc
    +(acc)
  =/  he-on=?  (gte same he-threshold)
  |-  ^-  (unit [?(%rec %he) identity])
  ?~  stk  ~
  ?.  =(fol.id-kid fol.i.stk)  $(stk t.stk)
  =/  d=datum  (git-g g i.stk)
  ?:  ?&  (huge:so less-code.d more.id-kid)
          (huge:so (app:ca indi.d more.id-kid) (app:ca indi.d more.i.stk))
      ==
    `[%rec i.stk]
  ?:  &(he-on (he-sock more.id-kid more.i.stk))
    `[%he [(msg-sock more.id-kid more.i.stk) fol.id-kid]]
  $(stk t.stk)
```

The count `same` is the `+roll` of layer 2 with the gate `recursive_call.cnt`
(`rc_count`); `he-threshold` is the noun at axis `510` of the context, `32`
in `ana`.  The loop `recursive_call.loop` is `recLoop` (`rc_loop`): it reads
`+git-g` at axis `4` of the context, `+he-sock` at `1374`, `+msg-sock` at
`5502` and the library core at `7` (`RcIn`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

/-- The noun of an answer of `+recursive-call`: `[%rec id]` or `[%he id]`. -/
def rcNoun (r : Bool × Ident) : Noun := C (A (if r.1 then 0x636572 else 0x6568)) (identNoun r.2)

theorem listNoun_cons {α : Type} (f : α → Noun) (x : α) (l : List α) :
    listNoun f (x :: l) = C (f x) (listNoun f l) := rfl

theorem listNoun_nil {α : Type} (f : α → Noun) : listNoun f ([] : List α) = A 0 := rfl

/-- The gate of the `+roll`: one more when the formula of the identity is
`kf`, the formula of `id-kid`. -/
theorem rc_cnt (i : Ident) (k : Nat) (bat km kf sstk gN ctx : Noun) :
    nock (C recursive_call.cnt (C (C (identNoun i) (A k)) (C bat (C (C (C km kf) (C sstk gN)) ctx))))
        recursive_call.cnt
      = some (A (k + if i.2 = kf then 1 else 0)) := by
  nock_open recursive_call.cnt
  by_cases h : i.2 = kf
  · simp [nock_exec, identNoun, h]
  · have h' : ¬ kf = i.2 := fun e => h e.symm
    simp [nock_exec, identNoun, h, h']

/-- The `+roll` of `recursive_call.cnt` over the stack, from the count `k`:
`k` plus the number of identities with the formula `kf`. -/
theorem rc_count (c bat sstk gN ctx e : Noun) (km : Noun) (kf : Noun) :
    ∀ (l : List Ident) (k : Nat),
    nock (C roll.loop (C roll.battery (C (C (listNoun identNoun l)
        (C recursive_call.cnt (C (C e (A k))
          (C bat (C (C (C km kf) (C sstk gN)) ctx))))) c))) roll.loop
      = some (A (k + (l.filter (fun i => decide (i.2 = kf))).length))
  | [], k => by nock_open roll.loop; simp [nock_exec, listNoun_nil]
  | i :: l, k => by
    have ih := rc_count c bat sstk gN ctx e km kf l
    have hc := rc_cnt i k bat km kf sstk gN ctx
    nock_open roll.loop
    by_cases h : i.2 = kf
    · have ih1 := ih (k + 1)
      simp only [h, if_true] at hc
      simp [nock_exec, listNoun_cons, hc, ih1, h]
      omega
    · simp only [h, if_false, Nat.add_zero] at hc
      simp [nock_exec, listNoun_cons, hc, ih, h]

/-- `he-threshold` in `ana`. -/
theorem ana_threshold : slot? 510 ana = some (A 32) := by kernel_rfl

/-! ## The loop -/

/-- What `+recursive-call` reads from its context. -/
abbrev RcIn (ctx : Noun) : Prop :=
  GitGIn ctx ∧ slot? git_g.axis ctx = some git_g.arm ∧
    HeSockIn ctx ∧ slot? he_sock.axis ctx = some he_sock.arm ∧
    slot? msg_sock.axis ctx = some msg_sock.arm ∧
    (∃ l1, slot? capeSize.layer1.axis ctx = some l1 ∧ GteIn l1) ∧
    (∃ l2, slot? gitG.layer2.axis ctx = some l2 ∧ slot? roll.axis l2 = some roll.arm)

/-- The graph as `+recursive-call` reads it: `+git-g` of the whole datum. -/
theorem gitG_gCore (g : Callgraph FinMap) (i : Ident) :
    SkaModel.gitG (gCore g) i = (Ana.gitG g i).core := by
  unfold SkaModel.gitG gCore Ana.gitG Treap.gut
  cases Treap.get g i <;> rfl

/-- The loop of `+recursive-call`: `recLoop` with `heSock`. -/
theorem rc_loop (ctx : Noun) (hc : RcIn ctx) (heOn : Bool) (same : Noun) (kid : Ident)
    (g : Callgraph FinMap) : ∀ stk : List Ident,
    nock (C recursive_call.loop (C (loob heOn) (C same (C recursive_call.battery
        (C (C (identNoun kid) (C (listNoun identNoun stk) (Treap.toNoun FDatum.toNoun g))) ctx)))))
        recursive_call.loop
      = (recLoop heSock heOn (gCore g) kid stk).map (unitNoun rcNoun)
  | [] => by nock_open recursive_call.loop; simp [nock_exec, listNoun_nil, recLoop, unitNoun]
  | i :: stk => by
    have ih := rc_loop ctx hc heOn same kid g stk
    obtain ⟨hgi, hga, hhi, hha, hma, -, -⟩ := hc
    have hlib : slot? 7 ctx = some lib := hhi.2.2
    have hga' : slot? 4 ctx = some git_g.arm := hga
    have hha' : slot? 1374 ctx = some he_sock.arm := hha
    have hma' : slot? 5502 ctx = some msg_sock.arm := hma
    have hmi : MsgSockIn ctx := ⟨lib, hlib, soKnitOf_of_soOf soOf_lib⟩
    have hgg := git_g_gate ctx hgi g i
    have hhe := he_sock_gate ctx hhi kid.1 i.1
    have hms := msg_sock_gate ctx hmi kid.1 i.1
    simp only [identNoun] at hgg
    simp only [listNoun_cons] at ih ⊢
    simp only [identNoun] at ih
    unfold recLoop
    rw [gitG_gCore]
    generalize Ana.gitG g i = d at hgg ⊢
    have hu1 := so_huge_gate (C so.battery lib) d.less kid.1
    have hu2 := so_huge_gate (C so.battery lib) (Ca.app d.indi kid.1) (Ca.app d.indi i.1)
    nock_open recursive_call.loop
    by_cases hf : kid.2 = i.2
    rotate_left
    · simp [nock_exec, identNoun, hf, ih]
    obtain ⟨km, kf⟩ := kid
    obtain ⟨im, ifol⟩ := i
    simp only at hf
    subst hf
    simp only [ne_eq, not_true_eq_false, if_false, hitTest, FDatum.core]
    cases h1 : So.huge d.less km with
    | none =>
      rw [h1] at hu1
      simp [nock_exec, identNoun, hlib, hga', git_g_arm, hgg, FDatum.toNoun, so.lib.arm_at,
        so_lib_arm, so.huge.arm_at, so_huge_arm, hu1]
    | some b1 =>
    rw [h1] at hu1
    cases b1 with
    | false =>
      cases heOn <;> simp only [loob_true, loob_false] at ih <;>
        cases hh : heSock km im <;> cases hm : msgSock km im <;>
        simp [nock_exec, identNoun, hlib, hga', git_g_arm, hgg, FDatum.toNoun, so.lib.arm_at,
          so_lib_arm, so.huge.arm_at, so_huge_arm, hu1, hha', he_sock_arm, hhe, hma', msg_sock_arm,
          hms, ih, unitNoun, rcNoun, hh, hm]
    | true =>
    cases h2 : So.huge (Ca.app d.indi km) (Ca.app d.indi im) with
    | none =>
      rw [h2] at hu2
      simp [nock_exec, identNoun, hlib, hga', git_g_arm, hgg, FDatum.toNoun, so.lib.arm_at,
        so_lib_arm, so.huge.arm_at, so_huge_arm, hu1, ca.lib.arm_at, ca_lib_arm, ca.app.arm_at,
        ca_app_arm, ca_app_pill, hu2]
    | some b2 =>
    rw [h2] at hu2
    cases b2 with
    | true =>
      simp [nock_exec, identNoun, hlib, hga', git_g_arm, hgg, FDatum.toNoun, so.lib.arm_at,
        so_lib_arm, so.huge.arm_at, so_huge_arm, hu1, ca.lib.arm_at, ca_lib_arm, ca.app.arm_at,
        ca_app_arm, ca_app_pill, hu2, unitNoun, rcNoun]
    | false =>
      cases heOn <;> simp only [loob_true, loob_false] at ih <;>
        cases hh : heSock km im <;> cases hm : msgSock km im <;>
        simp [nock_exec, identNoun, hlib, hga', git_g_arm, hgg, FDatum.toNoun, so.lib.arm_at,
          so_lib_arm, so.huge.arm_at, so_huge_arm, hu1, ca.lib.arm_at, ca_lib_arm, ca.app.arm_at,
          ca_app_arm, ca_app_pill, hu2, hha', he_sock_arm, hhe, hma', msg_sock_arm,
          hms, ih, unitNoun, rcNoun, hh, hm]

/-! ## The gate -/

@[nock_exec] theorem recursive_call_arm (c : Noun) :
    nock c recursive_call.arm
      = some (C recursive_call.battery
          (C (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (A 0) (A 0))) c)) := by
  nock_open recursive_call.arm; simp only [nock_exec]

theorem roll_battery_loop (x : Noun) :
    nock (C roll.battery x) roll.battery = nock (C roll.loop (C roll.battery x)) roll.loop := by
  nock_open roll.battery; simp only [nock_exec]

/-- Slamming `+recursive-call` on an identity, a stack and a call graph of
`FinMap`, in a context whose `he-threshold` is `thr`. -/
theorem recursive_call_gate (ctx : Noun) (hc : RcIn ctx) (thr : Nat)
    (ht : slot? 510 ctx = some (A thr)) (kid : Ident) (stk : List Ident) (g : Callgraph FinMap) :
    nock (C recursive_call.battery (C (C (identNoun kid)
        (C (listNoun identNoun stk) (Treap.toNoun FDatum.toNoun g))) ctx)) recursive_call.battery
      = (recursiveCall heSock thr kid stk (gCore g)).map (unitNoun rcNoun) := by
  have hl := rc_loop ctx hc (decide (thr ≤ (stk.filter (fun i => decide (i.2 = kid.2))).length))
    (A (stk.filter (fun i => decide (i.2 = kid.2))).length) kid g stk
  obtain ⟨⟨l2, hl2, -, -, -, -⟩, -, -, -, -, ⟨l1, hl1, hgte⟩, ⟨l2', hl2', hroll⟩⟩ := hc
  obtain rfl : l2 = l2' := Option.some.inj (hl2.symm.trans hl2')
  have hl1' : slot? 16383 ctx = some l1 := hl1
  have hl2'' : slot? 8191 ctx = some l2 := hl2
  have hcnt := rc_count l2 recursive_call.battery (listNoun identNoun stk)
    (Treap.toNoun FDatum.toNoun g) ctx (C (C (A 1) (A 0)) (C (A 0) (A 0))) kid.1.toNoun kid.2 stk 0
  have hg := gte_gate l1 hgte.2 (stk.filter (fun i => decide (i.2 = kid.2))).length thr
  simp only [identNoun] at hl
  simp only [Nat.zero_add] at hcnt
  unfold recursiveCall
  nock_open recursive_call.battery
  simp [nock_exec, identNoun, hl1', hl2'', hroll, roll_arm, roll_battery_loop, hcnt, hgte.1, gte_arm,
    hg, hl, ht]

/-! ## On the pill's analysis core -/

theorem rcIn_ana : RcIn ana :=
  ⟨gitGIn_ana, git_g.arm_at, heSockIn_ana, he_sock.arm_at, msg_sock.arm_at,
    ⟨layer1, ana_layer1, gte.arm_at, arith_layer1.2.2.2.1⟩, ⟨layer2, ana_layer2, roll.arm_at⟩⟩

theorem recursive_call_pill (kid : Ident) (stk : List Ident) (g : Callgraph FinMap) :
    nock (C recursive_call.battery (C (C (identNoun kid)
        (C (listNoun identNoun stk) (Treap.toNoun FDatum.toNoun g))) ana)) recursive_call.battery
      = (recursiveCall heSock 32 kid stk (gCore g)).map (unitNoun rcNoun) :=
  recursive_call_gate ana rcIn_ana 32 ana_threshold kid stk g

end Compiler
end Formalization
