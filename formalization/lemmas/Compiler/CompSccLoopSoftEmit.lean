import lemmas.Compiler.CompSccLoopSoftEmitCut
import lemmas.Compiler.CompSccLoopSoft

/-! # `+soft-emit` in the pill, first steps (README Gaps 21.17)

* `se_slam`: `seCall e` on the core runs `seBat` on `[seBat [e core]]`.
* **`se_nil`**: on a soft call with no requirement, `+soft-emit` gives back `gen`
  (`softEmitT`'s first case). -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

/-- The slam of `+soft-emit`: the gate's battery on `[seBat [e core]]`. -/
theorem se_slam (g : Gen (TreapMap mugF)) (x : GenRest) (ctx e : Noun) :
    nock (compCore g x ctx) (seCall e) = nock (C seBat (C e (compCore g x ctx))) seBat := by
  have hA := se_at
  simp only [seCall, compCore] at hA ⊢
  generalize comp.door = Dr at hA
  generalize genNoun g x = GN
  simp [nock_exec, seArm, seBunt, hA]

/-- **`+soft-emit` on a soft call with no requirement** gives back `gen`. -/
theorem se_nil (g : Gen (TreapMap mugF)) (x : GenRest) (ctx : Noun) (o : Nat) (s : SoftCall)
    (h : s.req = []) :
    nock (compCore g x ctx) (seCall (C (A o) (Compiler.SoftCall.toNoun s))) = some (genNoun g x) := by
  rw [se_slam]
  simp only [compCore]
  generalize comp.door = Dr
  generalize genNoun g x = GN
  simp [nock_exec, seBat, seT0, seNil, Compiler.SoftCall.toNoun, h]

/-- **The end of the path without tries**: on the subject after the pushes (`hed` the head block
of the bond, `tries` `~`, `ops`, `cut`, `axs`, the gate's subject), the `?>` on `hed`
(`[~ ~ %hop ~ *]`), `?~ tries` and `(emir head.s ~ ops fin.hed)`. -/
theorem se_end (g : Gen (TreapMap mugF)) (x : GenRest) (ctx : Noun) (hc : CompIn ctx) (o : Nat) (s : SoftCall)
    (hd : Blob) (ops : List Pole) (CUT AXS : Noun) (hp : hd.par = []) (hb : hd.body = []) (t : Jmp)
    (hf : hd.fin = Termin.hop t) (ht : t.args = []) :
    nock (C hd.toNoun (C (A 0) (C (listNoun Pole.toNoun ops) (C CUT (C AXS (C seBat
      (C (C (A o) (Compiler.SoftCall.toNoun s)) (compCore g x ctx))))))))
      (C (A 6) (C seHedT (C (C (A 6) (C seTriesT (C seEmir seTryPath))) (C (A 0) (A 0)))))
      = (emir s.head ⟨[], ops, hd.fin⟩ g).map fun p => genNoun p.2 x := by
  have he := comp_emir (ctx := ctx) x hc g s.head ⟨[], ops, hd.fin⟩
  have hA := comp_emir_at
  obtain ⟨par, body, fin⟩ := hd
  simp only at hp hb hf
  subst hp hb hf
  obtain ⟨args, there⟩ := t
  simp only at ht
  subst ht
  simp only [compCore, Blob.toNoun, listNoun, List.foldr] at he ⊢
  generalize comp.door = Dr at he hA
  generalize genNoun g x = GN at he
  simp only [Termin.toNoun, Jmp.toNoun, listNoun, List.foldr, Tag.hop] at he
  generalize (emir s.head ⟨[], ops, Termin.hop ⟨[], there⟩⟩ g).map (fun p => genNoun p.2 x) = R at he
  simp [nock_exec, seHedT, seTriesT, seEmir, Termin.toNoun, Jmp.toNoun, listNoun, Compiler.SoftCall.toNoun, hA,
    comp_emir_arm, Tag.hop, he]

end Compiler
end Formalization
