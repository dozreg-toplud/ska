import lemmas.Compiler.Regs
import lemmas.Ska.Interp

/-!
`+eval-pass` of the interpreter core against `evalPass` of
`lemmas/Ska/Interp.lean`, on register maps of `TreapMap mugF`.

```hoon
++  eval-pass
  |=  [args=(list (unit @uvre)) par=(list @uvre) regs=(map @uvre (unit *))]
  ^-  (map @uvre (unit *))
  ?>  %+  levy  args
      |=  a=(unit @uvre)
      |(?=(~ a) !(lien par |=(p=@uvre =(p u.a))))
  |-  ^-  (map @uvre (unit *))
  ?~  args  ?>(?=(~ par) regs)
  ?>  ?=(^ par)
  =.  regs
    ?~  i.args  (~(put by regs) i.par ~)
    (move u.i.args i.par regs)
  $(args t.args, par t.par)
```

The gate that `+levy` runs is `eval_pass.chk`, the one that `+lien` runs
inside it `eval_pass.mem`, the loop `eval_pass.loop`.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

/-- What `+eval-pass` reads from its context: `+move` and what it reads, and
`+levy` and `+lien` of layer 2. -/
abbrev EvalPassIn (c : Noun) : Prop :=
  slot? move.axis c = some move.arm ∧ MoveIn mugF c ∧
    ∃ l2, slot? read.layer2.axis c = some l2 ∧ slot? levy.axis l2 = some levy.arm ∧
      slot? lien.axis l2 = some lien.arm

@[nock_exec] theorem eval_pass_arm (c : Noun) :
    nock c eval_pass.arm
      = some (C eval_pass.battery (C (C (A 0) (C (A 0) (A 0))) c)) := by
  nock_open eval_pass.arm; simp only [nock_exec]

/-- The arguments of a jump and the parameters of a block, as nouns. -/
def argsN (args : List (Option Nat)) : Noun := listNoun (unitNoun A) args

def parN (par : List Nat) : Noun := listNoun A par

theorem listNoun_eq_listN {α : Type} (f : α → Noun) :
    ∀ l : List α, listNoun f l = listN (l.map f)
  | [] => rfl
  | x :: xs => by simp [listNoun, listN, listNoun_eq_listN f xs]

/-- `+move` on a map of `TreapMap mugF`, in any context that holds what it
reads. -/
theorem move_model (c : Noun) (hc : MoveIn mugF c) (s d : Nat) (regs : TreapMap mugF (Option Noun)) :
    nock (C move.battery (C (C (A s) (C (A d) (HoonMap.toNoun (unitNoun id) regs))) c)) move.battery
      = (SkaModel.move s d regs).map (HoonMap.toNoun (unitNoun id)) := by
  have h := getF_hoonMap (unitNoun id) regs s
  unfold SkaModel.move
  cases e : HoonMap.get regs s with
  | none => rw [e] at h; simpa using move_gate_nil _ hc s d _ h
  | some u =>
    rw [e] at h
    simpa using move_gate _ hc s d _ (unitNoun id u) _ h (putF_hoonMap (unitNoun id) regs d u)

/-- `(~(put by regs) p ~)` through layer 2 of the context, on a map of
`TreapMap mugF`: the poison of `p`. -/
theorem poison_model (l2 : Noun) (hc : GorIn mugF l2 ∧ MorIn mugF l2) (p : Nat)
    (regs : TreapMap mugF (Option Noun)) :
    nock (C by.put.battery (C (C (A p) (A 0)) (C by.battery (C (HoonMap.toNoun (unitNoun id) regs) l2))))
        by.put.battery
      = some (HoonMap.toNoun (unitNoun id) (SkaModel.poison p regs)) :=
  put_gate l2 hc (A p) (A 0) _ _ (putF_hoonMap (unitNoun id) regs p none)

/-- The loop of `+eval-pass`. -/
theorem eval_pass_loop (c : Noun) (hc : EvalPassIn c) :
    ∀ (args : List (Option Nat)) (par : List Nat) (regs : TreapMap mugF (Option Noun)),
    nock (C eval_pass.loop (C eval_pass.battery
        (C (C (argsN args) (C (parN par) (HoonMap.toNoun (unitNoun id) regs))) c))) eval_pass.loop
      = (evalPassLoop args par regs).map (HoonMap.toNoun (unitNoun id)) := by
  obtain ⟨hmv, hmc, l2, hl2, _, _⟩ := hc
  have hmove := hmc
  obtain ⟨l2', hl2', hby, _, _, hgor, hmor⟩ := hmc
  obtain rfl : l2 = l2' := Option.some.inj (hl2.symm.trans hl2')
  intro args
  induction args with
  | nil =>
    intro par regs
    rcases par with _ | ⟨p, par⟩
    · nock_open eval_pass.loop; simp [nock_exec, argsN, parN, listNoun, evalPassLoop]
    · nock_open eval_pass.loop; simp [nock_exec, argsN, parN, listNoun, evalPassLoop]
  | cons a args ih =>
    intro par regs
    rcases par with _ | ⟨p, par⟩
    · nock_open eval_pass.loop; simp [nock_exec, argsN, parN, listNoun, evalPassLoop]
    · rcases a with _ | r
      · have h1 := ih par (SkaModel.poison p regs)
        simp only [argsN, parN] at h1
        nock_open eval_pass.loop
        simp [nock_exec, argsN, parN, listNoun, unitNoun, evalPassLoop, hl2, hby, by_arm,
          by.put.arm_at, put_arm, poison_model l2 ⟨hgor, hmor⟩, h1]
      · have hm := move_model c hmove r p regs
        cases e : SkaModel.move r p regs with
        | none =>
          rw [e] at hm
          nock_open eval_pass.loop
          simp [nock_exec, argsN, parN, listNoun, unitNoun, evalPassLoop, hmv, move_arm, hm, e]
        | some regs' =>
          rw [e] at hm
          have h1 := ih par regs'
          simp only [argsN, parN] at h1
          nock_open eval_pass.loop
          simp [nock_exec, argsN, parN, listNoun, unitNoun, evalPassLoop, hmv, move_arm, hm, e, h1]

/-! ## The check of `+eval-pass` -/

/-- The gate that `+lien` runs: is the parameter the argument's register? -/
theorem eval_pass_mem (y u v Z W : Noun) :
    nock (C eval_pass.mem (C y (C Z (C (C u v) W)))) eval_pass.mem = some (eqCode y v) := by
  nock_open eval_pass.mem; simp only [nock_exec]

theorem loob_decide_eq (y v : Noun) : loob (decide (y = v)) = eqCode y v := by
  unfold eqCode loob; by_cases h : y = v <;> simp [h]

theorem any_map_A (par : List Nat) (r : Nat) :
    (par.map A).any (fun y => decide (y = A r)) = par.contains r := by
  induction par with
  | nil => rfl
  | cons p ps ih => simp [ih, eq_comm]

/-- What the check asks of one argument. -/
def argOK (par : List Nat) : Option Nat → Bool
  | none => true
  | some r => !par.contains r

/-- The gate that `+levy` runs on an argument. -/
theorem eval_pass_chk (c l2 : Noun) (hl2 : slot? read.layer2.axis c = some l2)
    (hlien : slot? lien.axis l2 = some lien.arm) (bat X R : Noun) (par : List Nat)
    (x : Option Nat) :
    nock (C eval_pass.chk (C (unitNoun A x) (C bat (C (C X (C (listN (par.map A)) R)) c))))
        eval_pass.chk
      = some (loob (argOK par x)) := by
  rcases x with _ | r
  · nock_open eval_pass.chk; simp [nock_exec, unitNoun, argOK]
  · have hl := lien_gate l2 eval_pass.mem (A 0)
      (C eval_pass.chk (C (unitNoun A (some r)) (C bat (C (C X (C (listN (par.map A)) R)) c))))
      (fun y => decide (y = A r)) (par.map A)
      (fun y _ => by simp only [unitNoun]; rw [eval_pass_mem, loob_decide_eq])
    simp only [any_map_A, unitNoun] at hl
    nock_open eval_pass.chk
    simp only [unitNoun] at hl ⊢
    by_cases hr : r ∈ par <;>
      simp [nock_exec, nock_ite, hl2, hlien, lien_arm, hl, argOK, hr]

/-- `argOK` on the noun of an argument. -/
def argOKN (par : List Nat) : Noun → Bool
  | Noun.cell _ (Noun.atom r) => !par.contains r
  | _ => true

theorem argOKN_unit (par : List Nat) (x : Option Nat) : argOKN par (unitNoun A x) = argOK par x := by
  cases x <;> rfl

theorem all_argOKN (par : List Nat) (args : List (Option Nat)) :
    (args.map (unitNoun A)).all (argOKN par) = args.all (argOK par) := by
  induction args with
  | nil => rfl
  | cons a as ih => rw [List.map_cons, List.all_cons, ih, argOKN_unit, List.all_cons]

theorem evalPass_eq {Map : Type → Type} [HoonMap Map] (args : List (Option Nat)) (par : List Nat)
    (regs : Map (Option Noun)) :
    evalPass args par regs = if args.all (argOK par) = true then evalPassLoop args par regs else none :=
  rfl

/-- `+eval-pass` computes `evalPass` of `Interp.lean`. -/
theorem eval_pass_gate (c : Noun) (hc : EvalPassIn c) (args : List (Option Nat)) (par : List Nat)
    (regs : TreapMap mugF (Option Noun)) :
    nock (C eval_pass.battery (C (C (argsN args) (C (parN par) (HoonMap.toNoun (unitNoun id) regs))) c))
        eval_pass.battery
      = (evalPass args par regs).map (HoonMap.toNoun (unitNoun id)) := by
  have hloop := eval_pass_loop c hc args par regs
  obtain ⟨_, _, l2, hl2, hlevy, hlien⟩ := hc
  simp only [argsN, parN, listNoun_eq_listN] at hloop
  have hlv := levy_gate l2 eval_pass.chk (A 0)
    (C eval_pass.battery (C (C (listN (args.map (unitNoun A))) (C (listN (par.map A))
      (HoonMap.toNoun (unitNoun id) regs))) c))
    (argOKN par) (args.map (unitNoun A)) (by
      intro n hn
      obtain ⟨x, _, rfl⟩ := List.mem_map.1 hn
      rw [eval_pass_chk c l2 hl2 hlien, argOKN_unit])
  rw [all_argOKN] at hlv
  simp only [argsN, parN, listNoun_eq_listN]
  nock_open eval_pass.battery
  rw [evalPass_eq]
  by_cases ha : args.all (argOK par) = true
  · rw [if_pos ha]; rw [ha] at hlv
    simp [nock_exec, hl2, hlevy, levy_arm, hlv, hloop]
  · rw [if_neg ha]; simp only [Bool.not_eq_true] at ha; rw [ha] at hlv
    simp [nock_exec, hl2, hlevy, levy_arm, hlv]

/-- The pill's interpreter core holds what `+eval-pass` reads. -/
theorem evalPassIn_interp : EvalPassIn interp :=
  ⟨move.arm_at, moveIn_interp, layer2, read.layer2.arm_at, levy.arm_at, lien.arm_at⟩

/-- `+eval-pass` of the pill computes `evalPass`. -/
theorem eval_pass_pill (args : List (Option Nat)) (par : List Nat) (regs : TreapMap mugF (Option Noun)) :
    nock (C eval_pass.battery (C (C (argsN args) (C (parN par) (HoonMap.toNoun (unitNoun id) regs))) interp))
        eval_pass.battery
      = (evalPass args par regs).map (HoonMap.toNoun (unitNoun id)) :=
  eval_pass_gate interp evalPassIn_interp args par regs

end Compiler
end Formalization
