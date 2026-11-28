import lemmas.Compiler.CompSccLoopSoftTryPes
import lemmas.Compiler.CompRunDirectMonoL
import lemmas.Compiler.CompRunDirectMonoB

/-! # The tries last: the `&` side of `+soft-free` (README Gaps 21.22)

On the subject after `def` (`twSub`: `def`, `fail`, `pes`, then `tzS` of
`CompSccLoopSoftTryPes.lean`), the chain `tpYNY0` .. `tpYNY6` of the try path
(`CompSccLoopSoftTryCut.lean`, lines 5467 to 5476 of the Hoon):
* `tw_loop`: the trap `twTrap` (in `tpYNYH1`, `tw_h1`) over `tops`, each entry by
  `+mono-try-call` (`mtc_gate`) on `[ned.i.tops nxt [r.i.tops fail]]`, is the model's
  `foldlM` of `softEmit`;
* `tw_last`: `=^ first gen` the trap from `there.t.fin.lat`, then
  `(emir head.s ~ ops fin.hed)` and `(emir last.s ~ ~ %hop ~ first)`. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The trap over the tries (`|-  ?~  tops  [nxt gen] ..`) of `tpYNYH1`. -/
def twTrap : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 14)))) (C (C (C (A 0) (A 6)) (C (A 0) (A 0xffffe))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaabbf) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 243)) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 114)) (C (A 0) (A 62)))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x1ffffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 61))) (C (A 10) (C (C (A 6) (C (A 0) (A 2))) (C (A 0) (A 3)))))))))))))))))))

theorem tw_h1 : tpYNYH1 = C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 0) (A 1022)) (C (A 8)
    (C (C (A 0) (A 8175)) (C (A 8) (C (C (A 1) twTrap) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))) := rfl

/-- The subject after `def`: `[def fail pes [kon rub] tom flag lat tpS0]`. -/
abbrev twSub (DEF : Noun) (FAIL PES : Nat) (kon : List Pole) (rub : Nat) (TOM FLAG LAT HD TR OPS CUT AXS : Noun)
    (o : Nat) (s : SoftCall) (g : Gen (TreapMap mugF)) (x : GenRest) (ctx : Noun) : Noun :=
  C DEF (C (A FAIL) (C (A PES) (tzS kon rub TOM FLAG LAT HD TR OPS CUT AXS o s g x ctx)))

theorem tw_listNoun_cons {α : Type} (f : α → Noun) (a : α) (l : List α) :
    listNoun f (a :: l) = C (f a) (listNoun f l) := rfl

/-- **The trap of the tries**: on the core `[twTrap [nxt [tops sub]]]`, the tries `l` in order,
each by `+mono-try-call`, the block of one the `nxt` of the next; the product `[first gen]`. -/
theorem tw_loop {ctx : Noun} (hc : CompIn ctx) (x : GenRest) (DEF : Noun) (FAIL PES : Nat)
    (kon : List Pole) (rub : Nat) (TOM FLAG LAT HD TR OPS CUT AXS : Noun) (o : Nat) (s : SoftCall) :
    ∀ (l : List (Nat × Nat × Need)) (nxt : Nat) (g : Gen (TreapMap mugF)),
    nock (C twTrap (C (A nxt) (C (listNoun seTopN l)
        (twSub DEF FAIL PES kon rub TOM FLAG LAT HD TR OPS CUT AXS o s g x ctx)))) twTrap
      = ((l.foldlM (fun nxt (_, r, n) => monoTryCall n nxt r FAIL) nxt : CM (TreapMap mugF) Nat) g).map fun p =>
          C (A p.1) (genNoun p.2 x) := by
  intro l
  induction l with
  | nil =>
    intro nxt g
    conv => { lhs; arg 2; unfold twTrap }
    simp [nock_exec, listNoun, twSub, tzS, tpKR, tpS0, seS0, compCore, List.foldlM, pure, StateT.pure]
  | cons t l ih =>
    intro nxt g
    obtain ⟨q, r, n⟩ := t
    have hD := mtc_at
    have hm := mtc_gate x hc n nxt r FAIL g
    simp only [compCore] at hm
    rw [tw_listNoun_cons]
    conv => { lhs; arg 2; unfold twTrap }
    cases em : monoTryCall (Map := TreapMap mugF) n nxt r FAIL g with
    | none =>
      rw [em] at hm
      simp only [Option.map_none] at hm
      simp only [twSub, tzS, tpKR, tpS0, seS0, compCore] at hm ⊢
      generalize comp.door = Dr at hD hm ⊢
      generalize listNoun seTopN l = LN
      simp [nock_exec, seTopN, hD, mtc_arm, hm, List.foldlM, bind, StateT.bind, em]
    | some p =>
      obtain ⟨n', g'⟩ := p
      rw [em] at hm
      simp only [Option.map_some] at hm
      have hi := ih n' g'
      simp only [twSub, tzS, tpKR, tpS0, seS0, compCore] at hm hi ⊢
      generalize comp.door = Dr at hD hm hi ⊢
      generalize listNoun seTopN l = LN at hi ⊢
      simp [nock_exec, seTopN, hD, mtc_arm, hm, hi, List.foldlM, bind, StateT.bind, em]

/-- **The tries last** (`+soft-free` `&`, lines 5467 to 5476): on the subject after `def`, with
`hed` the head block, `lat` the last block (`fin.lat` a `%hop` to `lt`), `tries` and `ops` as
`+soft-emit` pushed them: the tries from `there.t.fin.lat` by the trap, then the two `+emir`s; the
product is `gen`. -/
theorem tw_last {ctx : Noun} (hc : CompIn ctx) (x : GenRest) (DEF : Noun) (FAIL PES : Nat)
    (kon : List Pole) (rub : Nat) (TOM FLAG CUT AXS : Noun) (o : Nat) (s : SoftCall)
    (hed lat : Blob) (lt : Jmp) (hlf : lat.fin = Termin.hop lt) (ops : List Pole)
    (tries : List (Nat × Nat × Need)) (g : Gen (TreapMap mugF)) :
    nock (twSub DEF FAIL PES kon rub TOM FLAG lat.toNoun hed.toNoun (listNoun seTopN tries)
        (listNoun Pole.toNoun ops) CUT AXS o s g x ctx) tpYNY0
      = (((tries.foldlM (fun nxt (_, r, n) => monoTryCall n nxt r FAIL) lt.there : CM (TreapMap mugF) Nat) g).bind
          fun p => (emir s.head ⟨[], ops, hed.fin⟩ p.2).bind fun q =>
            emir s.last ⟨[], [], Termin.hop (jmp0 p.1)⟩ q.2).map fun q => genNoun q.2 x := by
  have hD := comp_emir_at
  have hL := tw_loop hc x DEF FAIL PES kon rub TOM FLAG lat.toNoun hed.toNoun (listNoun seTopN tries)
    (listNoun Pole.toNoun ops) CUT AXS o s tries lt.there g
  obtain ⟨lpar, lbody, lfin⟩ := lat
  simp only at hlf
  subst hlf
  obtain ⟨largs, lthere⟩ := lt
  conv => { lhs; arg 2; unfold tpYNY0 tpYNY1 tpYNY2 tpYNY3 tpYNY4 tpYNY5 tpYNY6 tpYNYH2 tpYNYH4; rw [tw_h1] }
  cases ef : ((tries.foldlM (fun nxt (_, r, n) => monoTryCall n nxt r FAIL) lthere : CM (TreapMap mugF) Nat) g) with
  | none =>
    rw [ef] at hL
    simp only [Option.map_none] at hL
    simp only [twSub, tzS, tpKR, tpS0, seS0, compCore, Blob.toNoun, Termin.toNoun, Jmp.toNoun, Option.bind_none,
      Option.map_none] at hL ⊢
    generalize comp.door = Dr at hD hL ⊢
    simp [nock_exec, hL]
  | some p =>
    obtain ⟨first, g1⟩ := p
    rw [ef] at hL
    simp only [Option.map_some] at hL
    have he1 := comp_emir x hc g1 s.head ⟨[], ops, hed.fin⟩
    cases e1 : emir s.head ⟨[], ops, hed.fin⟩ g1 with
    | none => simp [emir] at e1
    | some q1 =>
      obtain ⟨_, g2⟩ := q1
      rw [e1] at he1
      have he2 := comp_emir x hc g2 s.last ⟨[], [], Termin.hop (jmp0 first)⟩
      cases e2 : emir s.last ⟨[], [], Termin.hop (jmp0 first)⟩ g2 with
      | none => simp [emir] at e2
      | some q2 =>
        rw [e2] at he2
        have hlt : Termin.toNoun (Termin.hop ⟨largs, lthere⟩)
            = C (A 0x706f68) (C (listNoun (unitNoun A) largs) (A lthere)) := rfl
        have hlt2 : Termin.toNoun (Termin.hop (jmp0 first)) = C (A 0x706f68) (C (A 0) (A first)) := rfl
        simp only [Option.map_some, Blob.toNoun, hlt2, listNoun] at he1 he2
        simp only [twSub, tzS, tpKR, tpS0, seS0, compCore, Blob.toNoun, hlt, Compiler.SoftCall.toNoun,
          Option.bind_some, Option.map_some] at hL he1 he2 ⊢
        generalize comp.door = Dr at hD hL he1 he2 ⊢
        generalize Termin.toNoun hed.fin = HF at hL he1 he2 ⊢
        simp [nock_exec, hD, comp_emir_arm, hL, he1, he2, e1, e2]

end Compiler
end Formalization
