import lemmas.Compiler.OptLinkAlFinBrz

/-!
# `+alias`: the end of a block, all cases (phase 14, README Gaps 13)

* `alF_hop_ok` to `alF_last_ok`: the ends that only rename, restated as
  `AlFinOK` (the state is unchanged).
* `alFinCase`, `alFin_dispatch`: the `?-` over `-.fin.bob` runs the case of
  the tag; `%lti`, not in the Hoon's `termin`, falls into the last case
  `%bom` and is kept, as the model does.
* `al_fin`: **`AlFinOK alFin fin` for every end `fin`**: where the model's
  `aliasFin g.old loc g.rev g.folded o fin` returns `res`, the Nock of the
  `=^  fin-new  gen` returns `[fin-new gen]` with `fin-new` the noun of
  `res.1` and `gen` related (`GenRelL`) to `g` with `rev := res.2.1`,
  `folded := res.2.2`, given `GenRelL g loc imml` of the `gen` noun and
  `RevNodup g.rev`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- An end that keeps the state, from its Nock on any `gen`. -/
theorem alF_keep_ok (FC : Noun) (fin : Termin) (fin' : (Nat → Nat) → Termin)
    (hm : ∀ old (loc : Opt.AInfo) rev fl o, Opt.aliasFin old loc rev fl o fin = some (fin' old, rev, fl))
    (hn : ∀ X1 X2 P B X4 X5 X6 NEW OLD REST Y Z (f : Nat → Nat), OldRel OLD f →
      nock (alFS X1 X2 (C P (C B (Termin.toNoun fin))) X4 X5 X6 (C alBat (C (C NEW (C OLD REST)) (C Y (C Z optC)))))
        FC = some (C (Termin.toNoun (fin' f)) (C NEW (C OLD REST)))) :
    AlFinOK FC fin := by
  intro g loc imml N hG hnd X1 X2 P B X4 X5 X6 NA BL REVA TR o res hres
  obtain ⟨OLD, INFO, IMMS, LOC, IMML, REV, rfl, hO, hI, hM, hR, hL, hIm⟩ := hG
  rw [hm] at hres
  cases hres
  exact ⟨_, hn X1 X2 P B X4 X5 X6 _ OLD _ alBodyCut _ g.old hO, genRelL_fin hO hI hM hL hIm hR g.folded⟩

theorem alF_hop_ok (t : Jmp) : AlFinOK alFinHop (Termin.hop t) :=
  alF_keep_ok _ _ (fun f => Termin.hop { t with args := t.args.map (Option.map f) }) (fun _ _ _ _ _ => rfl)
    (fun X1 X2 P B X4 X5 X6 NEW OLD REST Y Z f h => alF_hop X1 X2 P B X4 X5 X6 NEW OLD REST Y Z f h t)

theorem alF_jmp_ok (a : Bell) (v : List Nat) : AlFinOK alFinJmp (Termin.jmp a v) :=
  alF_keep_ok _ _ (fun f => Termin.jmp a (v.map f)) (fun _ _ _ _ _ => rfl)
    (fun X1 X2 P B X4 X5 X6 NEW OLD REST Y Z f h => alF_jmp X1 X2 P B X4 X5 X6 NEW OLD REST Y Z f h a v)

theorem alF_jmf_ok (a : Bell) (v : List Nat) (n : Ring) : AlFinOK alFinJmf (Termin.jmf a v n) :=
  alF_keep_ok _ _ (fun f => Termin.jmf a (v.map f) n) (fun _ _ _ _ _ => rfl)
    (fun X1 X2 P B X4 X5 X6 NEW OLD REST Y Z f h => alF_jmf X1 X2 P B X4 X5 X6 NEW OLD REST Y Z f h a v n)

theorem alF_jsp_ok (a : Bell) (s : Nat) : AlFinOK alFinJsp (Termin.jsp a s) :=
  alF_keep_ok _ _ (fun f => Termin.jsp a (f s)) (fun _ _ _ _ _ => rfl)
    (fun X1 X2 P B X4 X5 X6 NEW OLD REST Y Z f h => alF_jsp X1 X2 P B X4 X5 X6 NEW OLD REST Y Z f h a s)

theorem alF_jsf_ok (a : Bell) (s : Nat) (n : Ring) : AlFinOK alFinJsf (Termin.jsf a s n) :=
  alF_keep_ok _ _ (fun f => Termin.jsf a (f s) n) (fun _ _ _ _ _ => rfl)
    (fun X1 X2 P B X4 X5 X6 NEW OLD REST Y Z f h => alF_jsf X1 X2 P B X4 X5 X6 NEW OLD REST Y Z f h a s n)

theorem alF_don_ok (s : Nat) : AlFinOK alFinDon (Termin.don s) :=
  alF_keep_ok _ _ (fun f => Termin.don (f s)) (fun _ _ _ _ _ => rfl)
    (fun X1 X2 P B X4 X5 X6 NEW OLD REST Y Z f h => alF_don X1 X2 P B X4 X5 X6 NEW OLD REST Y Z f h s)

/-- The last case keeps the end: `%bom`, and `%lti` (absent from `termin`). -/
theorem alF_last_ok (fin : Termin)
    (hm : ∀ old (loc : Opt.AInfo) rev fl o, Opt.aliasFin old loc rev fl o fin = some (fin, rev, fl)) :
    AlFinOK alFinLast fin :=
  alF_keep_ok _ _ (fun _ => fin) hm
    (fun X1 X2 P B X4 X5 X6 NEW OLD REST Y Z f h => alF_bom X1 X2 P B X4 X5 X6 (C NEW (C OLD REST)) Y Z fin)

/-! ## The dispatch -/

/-- The case of the `?-` that an end runs. -/
def alFinCase : Termin → Noun
  | Termin.clq .. => alFinClq
  | Termin.eqq .. => alFinEqq
  | Termin.brn .. => alFinBrn
  | Termin.brz .. => alFinBrz
  | Termin.hop .. => alFinHop
  | Termin.jmp .. => alFinJmp
  | Termin.jmf .. => alFinJmf
  | Termin.jsp .. => alFinJsp
  | Termin.jsf .. => alFinJsf
  | Termin.don .. => alFinDon
  | Termin.bom .. => alFinLast
  | Termin.lti .. => alFinLast

/-- **The `?-` over `-.fin.bob`** runs the case of the tag. -/
theorem alFin_dispatch (X1 X2 P B X4 X5 X6 W : Noun) (fin : Termin) :
    nock (alFS X1 X2 (C P (C B (Termin.toNoun fin))) X4 X5 X6 W) alFin
      = nock (alFS X1 X2 (C P (C B (Termin.toNoun fin))) X4 X5 X6 W) (alFinCase fin) := by
  unfold alFS
  cases fin <;> simp [alFin, alFinCase, nock_exec, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop,
    Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]

theorem alFinCase_ok (fin : Termin) : AlFinOK (alFinCase fin) fin := by
  cases fin with
  | clq s z o' => exact alF_clq s z o'
  | eqq l r z o' => exact alF_eqq l r z o'
  | brn s z o' => exact alF_brn s z o'
  | brz s z o' => exact alF_brz s z o'
  | hop t => exact alF_hop_ok t
  | jmp a v => exact alF_jmp_ok a v
  | jmf a v n => exact alF_jmf_ok a v n
  | jsp a s => exact alF_jsp_ok a s
  | jsf a s n => exact alF_jsf_ok a s n
  | don s => exact alF_don_ok s
  | bom b => exact alF_last_ok _ (fun _ _ _ _ _ => rfl)
  | lti n s z o' => exact alF_last_ok _ (fun _ _ _ _ _ => rfl)

/-- **Phase 14 of `+alias`: the end of a block**, every case: the Nock of
`alFin` returns `[fin-new gen]` as `aliasFin` does. -/
theorem al_fin (fin : Termin) : AlFinOK alFin fin := by
  intro g loc imml N hG hnd X1 X2 P B X4 X5 X6 NA BL REVA TR o res hres
  rw [alFin_dispatch]
  exact alFinCase_ok fin g loc imml N hG hnd X1 X2 P B X4 X5 X6 NA BL REVA TR o res hres

end Compiler
end Formalization
