import Formalization.Nock

namespace Formalization
namespace Nock

namespace SmallStep

-- Small-step terms include non-noun intermediate forms. `star` is the explicit
-- reduction marker corresponding to the spec's `*` syntax.
inductive Term where
  | val : Noun -> Term
  | cell : Term -> Term -> Term
  | wut : Term -> Term
  | lus : Term -> Term
  | tis : Term -> Term -> Term
  | edit : Nat -> Term -> Term -> Term
  | pick : Noun -> Term -> Noun -> Noun -> Term
  | star : Term -> Term -> Term
  deriving DecidableEq, Repr

def initial (subject formula : Noun) : Term :=
  Term.star (Term.val subject) (Term.val formula)

-- One small reduction. Contextual rules reduce one child at a time; the
-- non-contextual rules expose exactly one Nock computation rule or one
-- intermediate marker.
inductive Step : Term -> Term -> Prop where
  | cell_left {left left' right} :
      Step left left' ->
      Step (Term.cell left right) (Term.cell left' right)
  | cell_right {left right right'} :
      Step right right' ->
      Step (Term.cell (Term.val left) right) (Term.cell (Term.val left) right')
  | cell_done {left right} :
      Step (Term.cell (Term.val left) (Term.val right)) (Term.val (C left right))

  | wut_step {term term'} :
      Step term term' ->
      Step (Term.wut term) (Term.wut term')
  | wut_done {noun} :
      Step (Term.wut (Term.val noun)) (Term.val (wut noun))

  | lus_step {term term'} :
      Step term term' ->
      Step (Term.lus term) (Term.lus term')
  | lus_done {atom} :
      Step (Term.lus (Term.val (A atom))) (Term.val (A (atom + 1)))

  | tis_left {left left' right} :
      Step left left' ->
      Step (Term.tis left right) (Term.tis left' right)
  | tis_right {left right right'} :
      Step right right' ->
      Step (Term.tis (Term.val left) right) (Term.tis (Term.val left) right')
  | tis_done {left right} :
      Step (Term.tis (Term.val left) (Term.val right)) (Term.val (eqCode left right))

  | edit_replacement {axis replacement replacement' subject} :
      Step replacement replacement' ->
      Step (Term.edit axis replacement subject) (Term.edit axis replacement' subject)
  | edit_subject {axis replacement subject subject'} :
      Step subject subject' ->
      Step (Term.edit axis (Term.val replacement) subject)
        (Term.edit axis (Term.val replacement) subject')
  | edit_done {axis replacement subject out} :
      Edit axis replacement subject out ->
      Step (Term.edit axis (Term.val replacement) (Term.val subject)) (Term.val out)

  | pick_test {subject test test' yes no} :
      Step test test' ->
      Step (Term.pick subject test yes no) (Term.pick subject test' yes no)
  | pick_zero {subject yes no} :
      Step (Term.pick subject (Term.val (A 0)) yes no)
        (Term.star (Term.val subject) (Term.val yes))
  | pick_one {subject yes no} :
      Step (Term.pick subject (Term.val (A 1)) yes no)
        (Term.star (Term.val subject) (Term.val no))

  | star_subject {subject subject' formula} :
      Step subject subject' ->
      Step (Term.star subject formula) (Term.star subject' formula)
  | star_formula {subject formula formula'} :
      Step formula formula' ->
      Step (Term.star (Term.val subject) formula)
        (Term.star (Term.val subject) formula')

  | star_cell {subject b c d} :
      Step (Term.star (Term.val subject) (Term.val (C (C b c) d)))
        (Term.cell
          (Term.star (Term.val subject) (Term.val (C b c)))
          (Term.star (Term.val subject) (Term.val d)))
  | star_op0 {subject axis out} :
      Slot axis subject out ->
      Step (Term.star (Term.val subject) (Term.val (slot axis))) (Term.val out)
  | star_op1 {subject noun} :
      Step (Term.star (Term.val subject) (Term.val (quote noun))) (Term.val noun)
  | star_op2 {subject b c} :
      Step (Term.star (Term.val subject) (Term.val (n3 (A 2) b c)))
        (Term.star
          (Term.star (Term.val subject) (Term.val b))
          (Term.star (Term.val subject) (Term.val c)))
  | star_op3 {subject b} :
      Step (Term.star (Term.val subject) (Term.val (n2 (A 3) b)))
        (Term.wut (Term.star (Term.val subject) (Term.val b)))
  | star_op4 {subject b} :
      Step (Term.star (Term.val subject) (Term.val (n2 (A 4) b)))
        (Term.lus (Term.star (Term.val subject) (Term.val b)))
  | star_op5 {subject b c} :
      Step (Term.star (Term.val subject) (Term.val (n3 (A 5) b c)))
        (Term.tis
          (Term.star (Term.val subject) (Term.val b))
          (Term.star (Term.val subject) (Term.val c)))
  | star_op6 {subject b c d} :
      Step (Term.star (Term.val subject) (Term.val (n4 (A 6) b c d)))
        (Term.pick subject (Term.star (Term.val subject) (Term.val b)) c d)
  | star_op7 {subject b c} :
      Step (Term.star (Term.val subject) (Term.val (n3 (A 7) b c)))
        (Term.star
          (Term.star (Term.val subject) (Term.val b))
          (Term.val c))
  | star_op8 {subject b c} :
      Step (Term.star (Term.val subject) (Term.val (n3 (A 8) b c)))
        (Term.star
          (Term.cell (Term.star (Term.val subject) (Term.val b)) (Term.val subject))
          (Term.val c))
  | star_op9 {subject axis c} :
      Step (Term.star (Term.val subject) (Term.val (n3 (A 9) (A axis) c)))
        (Term.star
          (Term.star (Term.val subject) (Term.val c))
          (Term.val (invoke axis)))
  | star_op10 {subject axis c d} :
      Step (Term.star (Term.val subject) (Term.val (n3 (A 10) (n2 (A axis) c) d)))
        (Term.edit axis
          (Term.star (Term.val subject) (Term.val c))
          (Term.star (Term.val subject) (Term.val d)))
  | star_op11_cell {subject b c d} :
      Step (Term.star (Term.val subject) (Term.val (n3 (A 11) (C b c) d)))
        (Term.star
          (Term.cell
            (Term.star (Term.val subject) (Term.val c))
            (Term.star (Term.val subject) (Term.val d)))
          (Term.val (slot 3)))
  | star_op11_atom {subject tag c} :
      Step (Term.star (Term.val subject) (Term.val (n3 (A 11) (A tag) c)))
        (Term.star (Term.val subject) (Term.val c))

inductive Steps : Term -> Term -> Prop where
  | refl {term} :
      Steps term term
  | tail {before after final} :
      Step before after ->
      Steps after final ->
      Steps before final

namespace Steps

theorem single {before after} (step : Step before after) : Steps before after :=
  Steps.tail step Steps.refl

theorem trans {first middle last}
    (left : Steps first middle) (right : Steps middle last) : Steps first last := by
  induction left with
  | refl => exact right
  | tail step rest ih => exact Steps.tail step (ih right)

theorem cell_left {left left' right}
    (steps : Steps left left') : Steps (Term.cell left right) (Term.cell left' right) := by
  induction steps with
  | refl => exact Steps.refl
  | tail step rest ih => exact Steps.tail (Step.cell_left step) ih

theorem cell_right {left right right'}
    (steps : Steps right right') :
    Steps (Term.cell (Term.val left) right) (Term.cell (Term.val left) right') := by
  induction steps with
  | refl => exact Steps.refl
  | tail step rest ih => exact Steps.tail (Step.cell_right step) ih

theorem wut {term term'}
    (steps : Steps term term') : Steps (Term.wut term) (Term.wut term') := by
  induction steps with
  | refl => exact Steps.refl
  | tail step rest ih => exact Steps.tail (Step.wut_step step) ih

theorem lus {term term'}
    (steps : Steps term term') : Steps (Term.lus term) (Term.lus term') := by
  induction steps with
  | refl => exact Steps.refl
  | tail step rest ih => exact Steps.tail (Step.lus_step step) ih

theorem tis_left {left left' right}
    (steps : Steps left left') : Steps (Term.tis left right) (Term.tis left' right) := by
  induction steps with
  | refl => exact Steps.refl
  | tail step rest ih => exact Steps.tail (Step.tis_left step) ih

theorem tis_right {left right right'}
    (steps : Steps right right') :
    Steps (Term.tis (Term.val left) right) (Term.tis (Term.val left) right') := by
  induction steps with
  | refl => exact Steps.refl
  | tail step rest ih => exact Steps.tail (Step.tis_right step) ih

theorem edit_replacement {axis replacement replacement' subject}
    (steps : Steps replacement replacement') :
    Steps (Term.edit axis replacement subject) (Term.edit axis replacement' subject) := by
  induction steps with
  | refl => exact Steps.refl
  | tail step rest ih => exact Steps.tail (Step.edit_replacement step) ih

theorem edit_subject {axis replacement subject subject'}
    (steps : Steps subject subject') :
    Steps (Term.edit axis (Term.val replacement) subject)
      (Term.edit axis (Term.val replacement) subject') := by
  induction steps with
  | refl => exact Steps.refl
  | tail step rest ih => exact Steps.tail (Step.edit_subject step) ih

theorem pick_test {subject test test' yes no}
    (steps : Steps test test') :
    Steps (Term.pick subject test yes no) (Term.pick subject test' yes no) := by
  induction steps with
  | refl => exact Steps.refl
  | tail step rest ih => exact Steps.tail (Step.pick_test step) ih

theorem star_subject {subject subject' formula}
    (steps : Steps subject subject') :
    Steps (Term.star subject formula) (Term.star subject' formula) := by
  induction steps with
  | refl => exact Steps.refl
  | tail step rest ih => exact Steps.tail (Step.star_subject step) ih

theorem star_formula {subject formula formula'}
    (steps : Steps formula formula') :
    Steps (Term.star (Term.val subject) formula)
      (Term.star (Term.val subject) formula') := by
  induction steps with
  | refl => exact Steps.refl
  | tail step rest ih => exact Steps.tail (Step.star_formula step) ih

end Steps

-- Big-step evaluation for small-step terms. This is the semantic bridge used in
-- the soundness proof: a single small step preserves this relation backwards.
inductive TermEval : Term -> Noun -> Prop where
  | val {noun} :
      TermEval (Term.val noun) noun
  | cell {left right leftOut rightOut} :
      TermEval left leftOut ->
      TermEval right rightOut ->
      TermEval (Term.cell left right) (C leftOut rightOut)
  | wut {term noun} :
      TermEval term noun ->
      TermEval (Term.wut term) (wut noun)
  | lus {term atom} :
      TermEval term (A atom) ->
      TermEval (Term.lus term) (A (atom + 1))
  | tis {left right leftOut rightOut} :
      TermEval left leftOut ->
      TermEval right rightOut ->
      TermEval (Term.tis left right) (eqCode leftOut rightOut)
  | edit {axis replacement subject replacementOut subjectOut out} :
      TermEval replacement replacementOut ->
      TermEval subject subjectOut ->
      Edit axis replacementOut subjectOut out ->
      TermEval (Term.edit axis replacement subject) out
  | pick_zero {subject test yes no out} :
      TermEval test (A 0) ->
      Eval subject yes out ->
      TermEval (Term.pick subject test yes no) out
  | pick_one {subject test yes no out} :
      TermEval test (A 1) ->
      Eval subject no out ->
      TermEval (Term.pick subject test yes no) out
  | star {subjectTerm formulaTerm subject formula out} :
      TermEval subjectTerm subject ->
      TermEval formulaTerm formula ->
      Eval subject formula out ->
      TermEval (Term.star subjectTerm formulaTerm) out

theorem eval_to_steps {subject formula out}
    (eval : Eval subject formula out) :
    Steps (initial subject formula) (Term.val out) := by
  induction eval with
  | cell leftEval rightEval leftSteps rightSteps =>
      exact Steps.tail Step.star_cell
        (Steps.trans (Steps.cell_left leftSteps)
          (Steps.trans (Steps.cell_right rightSteps)
            (Steps.single Step.cell_done)))
  | op0 slot =>
      exact Steps.single (Step.star_op0 slot)
  | op1 =>
      exact Steps.single Step.star_op1
  | op2 subjectEval formulaEval finalEval subjectSteps formulaSteps finalSteps =>
      exact Steps.tail Step.star_op2
        (Steps.trans (Steps.star_subject subjectSteps)
          (Steps.trans (Steps.star_formula formulaSteps) finalSteps))
  | op3 innerEval innerSteps =>
      exact Steps.tail Step.star_op3
        (Steps.trans (Steps.wut innerSteps)
          (Steps.single Step.wut_done))
  | op4 innerEval innerSteps =>
      exact Steps.tail Step.star_op4
        (Steps.trans (Steps.lus innerSteps)
          (Steps.single Step.lus_done))
  | op5 leftEval rightEval leftSteps rightSteps =>
      exact Steps.tail Step.star_op5
        (Steps.trans (Steps.tis_left leftSteps)
          (Steps.trans (Steps.tis_right rightSteps)
            (Steps.single Step.tis_done)))
  | op6_zero testEval branchEval testSteps branchSteps =>
      exact Steps.tail Step.star_op6
        (Steps.trans (Steps.pick_test testSteps)
          (Steps.tail Step.pick_zero branchSteps))
  | op6_one testEval branchEval testSteps branchSteps =>
      exact Steps.tail Step.star_op6
        (Steps.trans (Steps.pick_test testSteps)
          (Steps.tail Step.pick_one branchSteps))
  | op7 subjectEval finalEval subjectSteps finalSteps =>
      exact Steps.tail Step.star_op7
        (Steps.trans (Steps.star_subject subjectSteps) finalSteps)
  | op8 producedEval finalEval producedSteps finalSteps =>
      exact Steps.tail Step.star_op8
        (Steps.trans
          (Steps.star_subject
            (Steps.trans (Steps.cell_left producedSteps)
              (Steps.single Step.cell_done)))
          finalSteps)
  | op9 coreEval finalEval coreSteps finalSteps =>
      exact Steps.tail Step.star_op9
        (Steps.trans (Steps.star_subject coreSteps) finalSteps)
  | op10 replacementEval baseEval edit replacementSteps baseSteps =>
      exact Steps.tail Step.star_op10
        (Steps.trans (Steps.edit_replacement replacementSteps)
          (Steps.trans (Steps.edit_subject baseSteps)
            (Steps.single (Step.edit_done edit))))
  | op11_cell hintEval productEval finalEval hintSteps productSteps finalSteps =>
      exact Steps.tail Step.star_op11_cell
        (Steps.trans
          (Steps.star_subject
            (Steps.trans (Steps.cell_left hintSteps)
              (Steps.trans (Steps.cell_right productSteps)
                (Steps.single Step.cell_done))))
          finalSteps)
  | op11_atom innerEval innerSteps =>
      exact Steps.tail Step.star_op11_atom innerSteps

theorem termEval_to_steps {term out}
    (eval : TermEval term out) : Steps term (Term.val out) := by
  induction eval with
  | val => exact Steps.refl
  | cell leftEval rightEval leftSteps rightSteps =>
      exact Steps.trans (Steps.cell_left leftSteps)
        (Steps.trans (Steps.cell_right rightSteps)
          (Steps.single Step.cell_done))
  | wut innerEval innerSteps =>
      exact Steps.trans (Steps.wut innerSteps)
        (Steps.single Step.wut_done)
  | lus innerEval innerSteps =>
      exact Steps.trans (Steps.lus innerSteps)
        (Steps.single Step.lus_done)
  | tis leftEval rightEval leftSteps rightSteps =>
      exact Steps.trans (Steps.tis_left leftSteps)
        (Steps.trans (Steps.tis_right rightSteps)
          (Steps.single Step.tis_done))
  | edit replacementEval subjectEval edit replacementSteps subjectSteps =>
      exact Steps.trans (Steps.edit_replacement replacementSteps)
        (Steps.trans (Steps.edit_subject subjectSteps)
          (Steps.single (Step.edit_done edit)))
  | pick_zero testEval branchEval testSteps =>
      exact Steps.trans (Steps.pick_test testSteps)
        (Steps.tail Step.pick_zero (eval_to_steps branchEval))
  | pick_one testEval branchEval testSteps =>
      exact Steps.trans (Steps.pick_test testSteps)
        (Steps.tail Step.pick_one (eval_to_steps branchEval))
  | star subjectEval formulaEval eval subjectSteps formulaSteps =>
      exact Steps.trans (Steps.star_subject subjectSteps)
        (Steps.trans (Steps.star_formula formulaSteps)
          (eval_to_steps eval))

theorem step_termEval_backward {before after out}
    (step : Step before after) :
    TermEval after out -> TermEval before out := by
  induction step generalizing out with
  | cell_left step ih =>
      intro eval
      cases eval with
      | cell leftEval rightEval =>
          exact TermEval.cell (ih leftEval) rightEval
  | cell_right step ih =>
      intro eval
      cases eval with
      | cell leftEval rightEval =>
          cases leftEval
          exact TermEval.cell TermEval.val (ih rightEval)
  | cell_done =>
      intro eval
      cases eval
      exact TermEval.cell TermEval.val TermEval.val
  | wut_step step ih =>
      intro eval
      cases eval with
      | wut innerEval => exact TermEval.wut (ih innerEval)
  | wut_done =>
      intro eval
      cases eval
      exact TermEval.wut TermEval.val
  | lus_step step ih =>
      intro eval
      cases eval with
      | lus innerEval => exact TermEval.lus (ih innerEval)
  | lus_done =>
      intro eval
      cases eval
      exact TermEval.lus TermEval.val
  | tis_left step ih =>
      intro eval
      cases eval with
      | tis leftEval rightEval => exact TermEval.tis (ih leftEval) rightEval
  | tis_right step ih =>
      intro eval
      cases eval with
      | tis leftEval rightEval =>
          cases leftEval
          exact TermEval.tis TermEval.val (ih rightEval)
  | tis_done =>
      intro eval
      cases eval
      exact TermEval.tis TermEval.val TermEval.val
  | edit_replacement step ih =>
      intro eval
      cases eval with
      | edit replacementEval subjectEval edit =>
          exact TermEval.edit (ih replacementEval) subjectEval edit
  | edit_subject step ih =>
      intro eval
      cases eval with
      | edit replacementEval subjectEval edit =>
          cases replacementEval
          exact TermEval.edit TermEval.val (ih subjectEval) edit
  | edit_done edit =>
      intro eval
      cases eval
      exact TermEval.edit TermEval.val TermEval.val edit
  | pick_test step ih =>
      intro eval
      cases eval with
      | pick_zero testEval branchEval =>
          exact TermEval.pick_zero (ih testEval) branchEval
      | pick_one testEval branchEval =>
          exact TermEval.pick_one (ih testEval) branchEval
  | pick_zero =>
      intro eval
      cases eval with
      | star subjectEval formulaEval branchEval =>
          cases subjectEval
          cases formulaEval
          exact TermEval.pick_zero TermEval.val branchEval
  | pick_one =>
      intro eval
      cases eval with
      | star subjectEval formulaEval branchEval =>
          cases subjectEval
          cases formulaEval
          exact TermEval.pick_one TermEval.val branchEval
  | star_subject step ih =>
      intro eval
      cases eval with
      | star subjectEval formulaEval finalEval =>
          exact TermEval.star (ih subjectEval) formulaEval finalEval
  | star_formula step ih =>
      intro eval
      cases eval with
      | star subjectEval formulaEval finalEval =>
          cases subjectEval
          exact TermEval.star TermEval.val (ih formulaEval) finalEval
  | star_cell =>
      intro eval
      cases eval with
      | cell leftEval rightEval =>
          cases leftEval with
          | star leftSubject leftFormula leftFinal =>
              cases leftSubject
              cases leftFormula
              cases rightEval with
              | star rightSubject rightFormula rightFinal =>
                  cases rightSubject
                  cases rightFormula
                  exact TermEval.star TermEval.val TermEval.val
                    (Eval.cell leftFinal rightFinal)
  | star_op0 slot =>
      intro eval
      cases eval
      exact TermEval.star TermEval.val TermEval.val (Eval.op0 slot)
  | star_op1 =>
      intro eval
      cases eval
      exact TermEval.star TermEval.val TermEval.val Eval.op1
  | star_op2 =>
      intro eval
      cases eval with
      | star subjectEval formulaEval finalEval =>
          cases subjectEval with
          | star leftSubject leftFormula subjectFinal =>
              cases leftSubject
              cases leftFormula
              cases formulaEval with
              | star rightSubject rightFormula formulaFinal =>
                  cases rightSubject
                  cases rightFormula
                  exact TermEval.star TermEval.val TermEval.val
                    (Eval.op2 subjectFinal formulaFinal finalEval)
  | star_op3 =>
      intro eval
      cases eval with
      | wut innerEval =>
          cases innerEval with
          | star subjectEval formulaEval finalEval =>
              cases subjectEval
              cases formulaEval
              exact TermEval.star TermEval.val TermEval.val (Eval.op3 finalEval)
  | star_op4 =>
      intro eval
      cases eval with
      | lus innerEval =>
          cases innerEval with
          | star subjectEval formulaEval finalEval =>
              cases subjectEval
              cases formulaEval
              exact TermEval.star TermEval.val TermEval.val (Eval.op4 finalEval)
  | star_op5 =>
      intro eval
      cases eval with
      | tis leftEval rightEval =>
          cases leftEval with
          | star leftSubject leftFormula leftFinal =>
              cases leftSubject
              cases leftFormula
              cases rightEval with
              | star rightSubject rightFormula rightFinal =>
                  cases rightSubject
                  cases rightFormula
                  exact TermEval.star TermEval.val TermEval.val
                    (Eval.op5 leftFinal rightFinal)
  | star_op6 =>
      intro eval
      cases eval with
      | pick_zero testEval branchEval =>
          cases testEval with
          | star testSubject testFormula testFinal =>
              cases testSubject
              cases testFormula
              exact TermEval.star TermEval.val TermEval.val
                (Eval.op6_zero testFinal branchEval)
      | pick_one testEval branchEval =>
          cases testEval with
          | star testSubject testFormula testFinal =>
              cases testSubject
              cases testFormula
              exact TermEval.star TermEval.val TermEval.val
                (Eval.op6_one testFinal branchEval)
  | star_op7 =>
      intro eval
      cases eval with
      | star subjectEval formulaEval finalEval =>
          cases subjectEval with
          | star leftSubject leftFormula subjectFinal =>
              cases leftSubject
              cases leftFormula
              cases formulaEval
              exact TermEval.star TermEval.val TermEval.val
                (Eval.op7 subjectFinal finalEval)
  | star_op8 =>
      intro eval
      cases eval with
      | star subjectEval formulaEval finalEval =>
          cases subjectEval with
          | cell producedEval originalEval =>
              cases producedEval with
              | star producedSubject producedFormula producedFinal =>
                  cases producedSubject
                  cases producedFormula
                  cases originalEval
                  cases formulaEval
                  exact TermEval.star TermEval.val TermEval.val
                    (Eval.op8 producedFinal finalEval)
  | star_op9 =>
      intro eval
      cases eval with
      | star subjectEval formulaEval finalEval =>
          cases subjectEval with
          | star coreSubject coreFormula coreFinal =>
              cases coreSubject
              cases coreFormula
              cases formulaEval
              exact TermEval.star TermEval.val TermEval.val
                (Eval.op9 coreFinal finalEval)
  | star_op10 =>
      intro eval
      cases eval with
      | edit replacementEval subjectEval edit =>
          cases replacementEval with
          | star replacementSubject replacementFormula replacementFinal =>
              cases replacementSubject
              cases replacementFormula
              cases subjectEval with
              | star baseSubject baseFormula baseFinal =>
                  cases baseSubject
                  cases baseFormula
                  exact TermEval.star TermEval.val TermEval.val
                    (Eval.op10 replacementFinal baseFinal edit)
  | star_op11_cell =>
      intro eval
      cases eval with
      | star subjectEval formulaEval finalEval =>
          cases subjectEval with
          | cell hintEval productEval =>
              cases hintEval with
              | star hintSubject hintFormula hintFinal =>
                  cases hintSubject
                  cases hintFormula
                  cases productEval with
                  | star productSubject productFormula productFinal =>
                      cases productSubject
                      cases productFormula
                      cases formulaEval
                      exact TermEval.star TermEval.val TermEval.val
                        (Eval.op11_cell hintFinal productFinal finalEval)
  | star_op11_atom =>
      intro eval
      cases eval with
      | star subjectEval formulaEval finalEval =>
          cases subjectEval
          cases formulaEval
          exact TermEval.star TermEval.val TermEval.val (Eval.op11_atom finalEval)

theorem steps_termEval_backward {before after out}
    (steps : Steps before after) :
    TermEval after out -> TermEval before out := by
  induction steps with
  | refl => intro eval; exact eval
  | tail step rest ih =>
      intro eval
      exact step_termEval_backward step (ih eval)

theorem steps_to_termEval {term out}
    (steps : Steps term (Term.val out)) : TermEval term out :=
  steps_termEval_backward steps TermEval.val

theorem bigStep_iff_smallStep {subject formula out} :
    Eval subject formula out ↔ Steps (initial subject formula) (Term.val out) := by
  constructor
  · intro eval
    exact eval_to_steps eval
  · intro steps
    have termEval : TermEval (initial subject formula) out :=
      steps_to_termEval steps
    cases termEval with
    | star subjectEval formulaEval eval =>
        cases subjectEval
        cases formulaEval
        exact eval

theorem terminating_iff {subject formula} :
    (∃ out, Eval subject formula out) ↔
      (∃ out, Steps (initial subject formula) (Term.val out)) := by
  constructor
  · intro h
    rcases h with ⟨out, eval⟩
    exact ⟨out, (bigStep_iff_smallStep.mp eval)⟩
  · intro h
    rcases h with ⟨out, steps⟩
    exact ⟨out, (bigStep_iff_smallStep.mpr steps)⟩

theorem same_result_big_to_small {subject formula out}
    (big : Eval subject formula out) :
    Steps (initial subject formula) (Term.val out) :=
  bigStep_iff_smallStep.mp big

theorem same_result_small_to_big {subject formula out}
    (small : Steps (initial subject formula) (Term.val out)) :
    Eval subject formula out :=
  bigStep_iff_smallStep.mpr small

theorem same_terminating_results {subject formula} :
    (fun out => Eval subject formula out) =
      (fun out => Steps (initial subject formula) (Term.val out)) := by
  funext out
  exact propext bigStep_iff_smallStep

end SmallStep

end Nock
end Formalization
