import Formalization.Nock

namespace Formalization
namespace Nock

def decLoopTest : Noun :=
  n3 (A 5) (n2 (A 4) (slot 7)) (slot 6)

def decLoopNextSample : Noun :=
  n2 (slot 6) (n2 (A 4) (slot 7))

def decLoopNextCore : Noun :=
  n3 (A 10) (n2 (A 3) decLoopNextSample) (slot 1)

def decLoopRecur : Noun :=
  n3 (A 9) (A 2) decLoopNextCore

def decLoopBattery : Noun :=
  n4 (A 6) decLoopTest (slot 7) decLoopRecur

def decGateInitialLoopCore : Noun :=
  n2
    (quote decLoopBattery)
    (n2 (slot 3) (quote (A 0)))

def decGateBattery : Noun :=
  n3 (A 9) (A 2) decGateInitialLoopCore

def decCore (sample : Nat) : Noun :=
  n2 decGateBattery (A sample)

def decLoopCore (sample counter : Nat) : Noun :=
  n2 decLoopBattery (n2 (A sample) (A counter))

-- This is the formula used by desk/tests/tests.hoon's ++test-dec to invoke
-- the compiled arm of the surrounding Hoon core: [9 2 0 1].
def decArmInvocation : Noun :=
  n3 (A 9) (A 2) (slot 1)

#eval evalFuel 128 (decCore 5) decArmInvocation

theorem decArmInvocation_decrements_five :
    evalFuel 128 (decCore 5) decArmInvocation = some (A (5 - 1)) := by
  native_decide

theorem decArmInvocation_decrements_three :
    evalFuel 128 (decCore 3) decArmInvocation = some (A (3 - 1)) := by
  native_decide

private theorem evalSlot1 (subject : Noun) :
    Eval subject (slot 1) subject :=
  Eval.op0 Slot.one

private theorem evalSlot2 (head tail : Noun) :
    Eval (C head tail) (slot 2) head :=
  Eval.op0 (Slot.left Slot.one)

private theorem evalSlot3 (head tail : Noun) :
    Eval (C head tail) (slot 3) tail :=
  Eval.op0 (Slot.right Slot.one)

private theorem evalInvoke2 {battery sample out : Noun}
    (h : Eval (C battery sample) battery out) :
    Eval (C battery sample) (invoke 2) out := by
  unfold invoke
  exact Eval.op2 (evalSlot1 (C battery sample)) (evalSlot2 battery sample) h

private theorem evalLoopSample (sample counter : Nat) :
    Eval (decLoopCore sample counter) (slot 6) (A sample) := by
  unfold decLoopCore
  exact Eval.op0 (Slot.left (Slot.right Slot.one))

private theorem evalLoopCounter (sample counter : Nat) :
    Eval (decLoopCore sample counter) (slot 7) (A counter) := by
  unfold decLoopCore
  exact Eval.op0 (Slot.right (Slot.right Slot.one))

private theorem editLoopSample (sample counter nextCounter : Nat) :
    Edit 3
      (n2 (A sample) (A nextCounter))
      (decLoopCore sample counter)
      (decLoopCore sample nextCounter) := by
  unfold decLoopCore
  exact Edit.right Edit.one

private theorem evalLoopTest (sample counter : Nat) :
    Eval
      (decLoopCore sample counter)
      decLoopTest
      (eqCode (A (counter + 1)) (A sample)) := by
  unfold decLoopTest
  exact Eval.op5
    (Eval.op4 (evalLoopCounter sample counter))
    (evalLoopSample sample counter)

private theorem evalLoopNextSample (sample counter : Nat) :
    Eval
      (decLoopCore sample counter)
      decLoopNextSample
      (n2 (A sample) (A (counter + 1))) := by
  unfold decLoopNextSample
  exact Eval.cell
    (evalLoopSample sample counter)
    (Eval.op4 (evalLoopCounter sample counter))

private theorem evalLoopRecur {sample counter out : Nat}
    (h : Eval (decLoopCore sample (counter + 1)) decLoopBattery (A out)) :
    Eval (decLoopCore sample counter) decLoopRecur (A out) := by
  unfold decLoopRecur decLoopNextCore
  exact Eval.op9
    (Eval.op10
      (evalLoopNextSample sample counter)
      (evalSlot1 (decLoopCore sample counter))
      (editLoopSample sample counter (counter + 1)))
    (evalInvoke2 h)

private theorem evalLoop_3_2 :
    Eval (decLoopCore 3 2) decLoopBattery (A 2) := by
  unfold decLoopBattery
  exact Eval.op6_zero
    (by
      change Eval (decLoopCore 3 2) decLoopTest (eqCode (A (2 + 1)) (A 3))
      exact evalLoopTest 3 2)
    (evalLoopCounter 3 2)

private theorem evalLoop_3_1 :
    Eval (decLoopCore 3 1) decLoopBattery (A 2) := by
  unfold decLoopBattery
  exact Eval.op6_one
    (by
      change Eval (decLoopCore 3 1) decLoopTest (eqCode (A (1 + 1)) (A 3))
      exact evalLoopTest 3 1)
    (evalLoopRecur evalLoop_3_2)

private theorem evalLoop_3_0 :
    Eval (decLoopCore 3 0) decLoopBattery (A 2) := by
  unfold decLoopBattery
  exact Eval.op6_one
    (by
      change Eval (decLoopCore 3 0) decLoopTest (eqCode (A (0 + 1)) (A 3))
      exact evalLoopTest 3 0)
    (evalLoopRecur evalLoop_3_1)

private theorem evalGateInitialLoopCore (sample : Nat) :
    Eval (decCore sample) decGateInitialLoopCore (decLoopCore sample 0) := by
  unfold decGateInitialLoopCore decCore decLoopCore
  exact Eval.cell
    Eval.op1
    (Eval.cell
      (evalSlot3 decGateBattery (A sample))
      Eval.op1)

private theorem evalGateBattery_3 :
    Eval (decCore 3) decGateBattery (A 2) := by
  unfold decGateBattery
  exact Eval.op9
    (evalGateInitialLoopCore 3)
    (evalInvoke2 evalLoop_3_0)

theorem decArmInvocation_bigStep_decrements_three :
    Eval (decCore 3) decArmInvocation (A (3 - 1)) := by
  change Eval (decCore 3) decArmInvocation (A 2)
  unfold decArmInvocation
  exact Eval.op9
    (evalSlot1 (decCore 3))
    (evalInvoke2 evalGateBattery_3)

end Nock
end Formalization
