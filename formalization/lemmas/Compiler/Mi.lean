import lemmas.Compiler.GitG
import lemmas.Pill.Arm.Mi

/-!
`+gut:mi` and `+put:mi` of the memoization core `+mi` against `Ana.gutMi` and
`Ana.putMi` of `lemmas/Ska/Analysis.lean`, on memos of `FinMap`.

```hoon
++  mi
  |%
  ++  gut
    |=  [m=memo f=^]
    ^-  (map sock [identity datum])
    (~(gut by m) f ~)
  ++  put
    ~%  %put-mi  ..ride  ~
    |=  [m=memo id=identity d=datum]
    ^-  memo
    =/  inner  (gut m fol.id)
    =.  inner  (~(put by inner) less-code.d [id d])
    (~(put by m) fol.id inner)
  --
```

The core `+mi` is `[mi.battery x]` with `x` the analysis core; both gates
read the door `+by` of the library's second layer through `x`, at the axis
`8191` of `x` that `+git-g` reads it at (`MiIn`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

/-- What the gates of `+mi` read from the context `x` of the core: the door
`+by` and what its `gut` and `put` read. -/
abbrev MiIn (x : Noun) : Prop := GitGIn x ∧ ∃ l2, slot? gitG.layer2.axis x = some l2 ∧ MorIn mugF l2

@[nock_exec] theorem mi_gut_arm (c : Noun) :
    nock c mi.gut.arm = some (C mi.gut.battery (C (C (A 0) (C (A 0) (A 0))) c)) := by
  nock_open mi.gut.arm; simp only [nock_exec]

@[nock_exec] theorem mi_put_arm (c : Noun) :
    nock c mi.put.arm
      = some (C mi.put.battery (C (C (A 0) (C (C (C (A 1) (A 0)) (C (A 0) (A 0)))
          (C (A 0) (C (C (A 0) (A 0)) (C (C (A 1) (A 0)) (C (A 1) (C (A 1)
            (C (C (A 0x64696f76) (A 0)) (A 0))))))))) c)) := by
  nock_open mi.put.arm; simp only [nock_exec]

/-- The noun of the inner map that `+gut:mi` returns. -/
noncomputable abbrev innerNoun (n : FinMap Sock (Ident × FDatum FinMap)) : Noun := Treap.toNoun entryNoun n

/-- `+gut:mi`: the inner map of a formula, `~` when the memo has none. -/
theorem mi_gut_gate (x : Noun) (hc : GitGIn x) (m : Memo FinMap) (f : Noun) :
    nock (C mi.gut.battery (C (C (memoNoun m) f) (C mi.battery x))) mi.gut.battery
      = some (innerNoun (gutMi m f)) := by
  obtain ⟨l2, hl2, hby, hfall, hsome, hgor⟩ := hc
  have hg : getF mugF f (memoNoun m)
      = some (unitNoun (Treap.toNoun entryNoun) (Treap.get m f)) :=
    FinMap.getF_toNoun (Treap.toNoun entryNoun) m f
  unfold gutMi Treap.gut
  nock_open mi.gut.battery
  cases e : Treap.get m f with
  | none =>
    rw [e] at hg
    simp only [unitNoun] at hg
    have h0 : innerNoun (Treap.empty : FinMap Sock (Ident × FDatum FinMap)) = A 0 :=
      FinMap.toNoun_empty _
    simp [nock_exec, hl2, hby, by_arm, by.gut.arm_at, gut_arm,
      gut_gate l2 ⟨hfall, hsome, hgor⟩ _ _ _ _ hg (Or.inl rfl), h0]
  | some d =>
    rw [e] at hg
    simp only [unitNoun] at hg
    simp [nock_exec, hl2, hby, by_arm, by.gut.arm_at, gut_arm,
      gut_gate l2 ⟨hfall, hsome, hgor⟩ _ _ _ _ hg (Or.inr ⟨_, rfl⟩)]

/-- `+put:mi`. -/
theorem mi_put_gate (x : Noun) (hc : MiIn x) (m : Memo FinMap) (i : Ident) (d : FDatum FinMap) :
    nock (C mi.put.battery (C (C (memoNoun m) (C (identNoun i) d.toNoun)) (C mi.battery x)))
        mi.put.battery
      = some (memoNoun (putMi m i d)) := by
  obtain ⟨hg, l2', hl2', hmor⟩ := hc
  have hgut := mi_gut_gate x hg m i.2
  obtain ⟨l2, hl2, hby, hfall, hsome, hgor⟩ := hg
  have e : l2 = l2' := Option.some.inj (hl2.symm.trans hl2')
  subst e
  have h1 : putF mugF d.less.toNoun (C (C i.1.toNoun i.2) d.toNoun) (innerNoun (gutMi m i.2))
      = some (innerNoun (Treap.put (gutMi m i.2) d.less (i, d))) :=
    FinMap.putF_toNoun entryNoun (gutMi m i.2) d.less (i, d)
  have h2 : putF mugF i.2 (innerNoun (Treap.put (gutMi m i.2) d.less (i, d))) (memoNoun m)
      = some (memoNoun (Treap.put m i.2 (Treap.put (gutMi m i.2) d.less (i, d)))) :=
    FinMap.putF_toNoun (Treap.toNoun entryNoun) m i.2 (Treap.put (gutMi m i.2) d.less (i, d))
  have p1 := put_gate l2 ⟨hgor, hmor⟩ _ _ _ _ h1
  have p2 := put_gate l2 ⟨hgor, hmor⟩ _ _ _ _ h2
  simp only [FDatum.toNoun] at p1
  unfold putMi
  nock_open mi.put.battery
  simp [nock_exec, identNoun, FDatum.toNoun, mi.gut.arm_at, mi_gut_arm, hgut, hl2, hby, by_arm,
    by.put.arm_at, put_arm, p1, p2]

/-! ## On the pill's analysis core -/

@[nock_exec] theorem mi_arm (c : Noun) : nock c mi.arm = some (C mi.battery c) := by
  nock_open mi.arm; simp only [nock_exec]

theorem miIn_ana : MiIn ana := ⟨gitGIn_ana, layer2, ana_layer2, gorIn_morIn_layer2.2⟩

theorem mi_gut_pill (m : Memo FinMap) (f : Noun) :
    nock (C mi.gut.battery (C (C (memoNoun m) f) (C mi.battery ana))) mi.gut.battery
      = some (innerNoun (gutMi m f)) :=
  mi_gut_gate ana gitGIn_ana m f

theorem mi_put_pill (m : Memo FinMap) (i : Ident) (d : FDatum FinMap) :
    nock (C mi.put.battery (C (C (memoNoun m) (C (identNoun i) d.toNoun)) (C mi.battery ana)))
        mi.put.battery
      = some (memoNoun (putMi m i d)) :=
  mi_put_gate ana miIn_ana m i d

end Compiler
end Formalization
