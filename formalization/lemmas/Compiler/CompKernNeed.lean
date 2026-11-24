import lemmas.Compiler.CompKernLink

/-!
# The loop of `+kern-need` against `kernLoop`

The case `%both` of `knLoop` (under the hint `%toss`) is cut into named
parts (`kn_loop_eq`): `knB1` after the fresh register for the tail, `knB2`
after the recursive call on the tail, `knB4` after the `=?` test, the edit of
`ops` and the fresh register for the head, `knB5` after the recursive call
on the head.  Each step is a folded lemma between two runs (`kn_s1`, ...),
and `kn_at` chains them by induction on the need.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

def knB5 : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 2) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 126)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (C (C (A 1) (A 0x646568)) (C (C (A 0) (A 4086)) (C (A 0) (A 6)))) (C (A 0) (A 2))) (C (A 0) (A 2)))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 2))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (C (C (A 1) (A 0x6c6563)) (C (A 0) (A 4086))) (C (A 0) (A 126)))) (C (A 0) (A 1)))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 1020)) (C (A 0) (A 4086)))) (C (C (A 0) (A 0)) (C (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 1020)) (C (A 0) (A 4086)))) (C (A 0) (A 126))) (C (A 0) (A 2046))))))))))))

def knB4 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (C (A 0) (A 2)) (C (A 0) (A 4078)))) (C (A 0) (A 15)))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) knB5))))))))

def knB2 : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 2) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 30)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (C (C (A 1) (A 0x6c6174)) (C (C (A 0) (A 1014)) (C (A 0) (A 6)))) (C (A 0) (A 2))) (C (A 0) (A 2)))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 30) (C (A 0) (A 2))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 127)))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) knB4))))))))))))

def knB1 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (C (A 0) (A 2)) (C (A 0) (A 1007)))) (C (A 0) (A 3)))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) knB2))))))))

def knLoopS : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 122)))) (C (C (C (A 0) (A 6)) (C (A 0) (A 126))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 122)))) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 60)) (C (A 0) (A 123)))) (C (C (A 0) (A 0)) (C (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 60)) (C (A 0) (A 123)))) (C (A 0) (A 6))) (C (A 0) (A 126)))))) (C (A 6) (C (C (A 3) (C (A 0) (A 122))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 31)))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 61) (C (C (A 1) (A 0x68746f62)) (C (C (A 0) (A 2)) (C (A 0) (A 125))))) (C (A 0) (A 3)))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 122))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 31)))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) knB1)))))))))))))))))))

theorem kn_loop_eq : knLoop = knLoopS := by kernel_rfl

/-- The step into `%both`: the fresh register for the tail. -/
theorem kn_s1 (x : GenRest) (ctx : Noun) (r d : Nat) (h t : Need) (ops : List Pole)
    (g : Gen (TreapMap mugF)) :
    nock (knT x ctx r (Need.both d h t) ops g) knLoop
      = nock (C (A g.re) (knT x ctx r (Need.both d h t) ops { g with re := g.re + 1 })) knB1 := by
  conv => { lhs; arg 2; rw [kn_loop_eq]; unfold knLoopS }
  have hD := comp_re_at
  have hre := comp_re' ctx x g
  simp only [knT, compCore] at hre ⊢
  generalize comp.door = Dr at hD hre ⊢
  generalize listNoun Pole.toNoun ops = N at ⊢
  simp [nock_exec, Need.toNoun, Tag.both, Tag.none, Tag.this, hD, hre]

/-- `%none`. -/
theorem kn_none (x : GenRest) (ctx : Noun) (r : Nat) (ops : List Pole) (g : Gen (TreapMap mugF)) :
    nock (knT x ctx r Need.none ops g) knLoop
      = (kernLoop r Need.none ops g).map fun p => C (listNoun Pole.toNoun p.1) (genNoun p.2 x) := by
  simp only [kernLoop, pure, StateT.pure, Option.map_some]
  nock_open knLoop
  simp only [knT, compCore]
  generalize listNoun Pole.toNoun ops = N
  simp [nock_exec, Need.toNoun, Tag.none]

/-- `%this`. -/
theorem kn_this (x : GenRest) (ctx : Noun) (r d : Nat) (ops : List Pole) (g : Gen (TreapMap mugF)) :
    nock (knT x ctx r (Need.this d) ops g) knLoop
      = (kernLoop r (Need.this d) ops g).map fun p => C (listNoun Pole.toNoun p.1) (genNoun p.2 x) := by
  nock_open knLoop
  simp only [knT, compCore]
  by_cases hrd : r = d
  · subst hrd
    generalize listNoun Pole.toNoun ops = N
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this, kernLoop, crashM]
  · simp only [kernLoop, hrd, if_false, pure, StateT.pure, Option.map_some, listNoun, Pole.toNoun]
    generalize listNoun Pole.toNoun ops = N
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.mov, hrd]

/-- A pair is a `%both` on a fresh register. -/
theorem kn_pair (x : GenRest) (ctx : Noun) (r : Nat) (p q : Need) (ops : List Pole)
    (g : Gen (TreapMap mugF)) :
    nock (knT x ctx r (Need.pair p q) ops g) knLoop
      = nock (knT x ctx r (Need.both g.re p q) ops { g with re := g.re + 1 }) knLoop := by
  nock_open knLoop
  obtain ⟨a, b, hp⟩ := cd_need_cell p
  have hD := comp_re_at
  have hre := comp_re' ctx x g
  simp only [knT, compCore, Need.toNoun, hp] at hre ⊢
  generalize comp.door = Dr at hD hre ⊢
  generalize listNoun Pole.toNoun ops = N at ⊢
  generalize q.toNoun = Q at ⊢
  simp [nock_exec, Tag.both, Tag.none, Tag.this, hD, hre]

/-- The recursive call on the tail. -/
theorem kn_s2 (x : GenRest) (ctx : Noun) (r d : Nat) (h t : Need) (ops : List Pole)
    (g : Gen (TreapMap mugF)) (rt : Nat) (iht : KnAt x ctx t) :
    nock (C (A rt) (knT x ctx r (Need.both d h t) ops g)) knB1
      = (kernLoop rt t ops g).bind fun p =>
          nock (C (listNoun Pole.toNoun p.1) (C (A rt) (knT x ctx r (Need.both d h t) ops p.2))) knB2 := by
  have ih := iht rt ops g
  nock_open knB1
  simp only [knT, compCore] at ih ⊢
  generalize comp.door = Dr at ih ⊢
  generalize listNoun Pole.toNoun ops = N at ih ⊢
  cases e : kernLoop rt t ops g with
  | none =>
    rw [e] at ih
    simp [nock_exec, Need.toNoun, ih]
  | some p =>
    obtain ⟨o1, g1⟩ := p
    rw [e] at ih
    simp only [Option.map_some] at ih
    simp only [Option.bind_some]
    generalize listNoun Pole.toNoun o1 = N1 at ih ⊢
    simp [nock_exec, Need.toNoun, ih]

/-- The `=?` test after the tail, the edit of `ops` and the fresh register
for the head. -/
theorem kn_s3 (x : GenRest) (ctx : Noun) (r d : Nat) (h t : Need) (ops ops1 : List Pole)
    (g : Gen (TreapMap mugF)) (rt : Nat) (hs : ∃ e, ops1 = e ++ ops) :
    nock (C (listNoun Pole.toNoun ops1) (C (A rt) (knT x ctx r (Need.both d h t) ops g))) knB2
      = nock (C (A g.re) (C (listNoun Pole.toNoun (if ops1 ≠ ops then Pole.tal d rt :: ops1 else ops1))
          (C (A rt) (knT x ctx r (Need.both d h t)
            (if ops1 ≠ ops then Pole.tal d rt :: ops1 else ops1) { g with re := g.re + 1 })))) knB4 := by
  have hD := comp_re_at
  have hre := comp_re' ctx x g
  nock_open knB2
  by_cases hc : ops1 = ops
  · subst hc
    simp only [ne_eq, not_true_eq_false, if_false]
    simp only [knT, compCore] at hre ⊢
    generalize comp.door = Dr at hD hre ⊢
    generalize listNoun Pole.toNoun ops1 = N
    simp [nock_exec, Need.toNoun, hD, hre]
  · obtain ⟨e, he⟩ := hs
    have hne : listNoun Pole.toNoun ops1 ≠ listNoun Pole.toNoun ops := by
      intro hq; subst he; exact hc ((kn_suf_eq Pole.toNoun e ops).1 hq)
    simp only [knT, compCore] at hre ⊢
    simp only [ne_eq, hc, not_false_eq_true, if_true, listNoun, Pole.toNoun]
    generalize comp.door = Dr at hD hre ⊢
    generalize listNoun Pole.toNoun ops1 = N1 at hne ⊢
    generalize listNoun Pole.toNoun ops = N at hne ⊢
    simp [nock_exec, Need.toNoun, hD, hre, eqCode, hne, Tag.tal]

/-- The recursive call on the head. -/
theorem kn_s4 (x : GenRest) (ctx : Noun) (r d : Nat) (h t : Need) (ops1 : List Pole)
    (g : Gen (TreapMap mugF)) (rt rh : Nat) (ihh : KnAt x ctx h) :
    nock (C (A rh) (C (listNoun Pole.toNoun ops1) (C (A rt) (knT x ctx r (Need.both d h t) ops1 g)))) knB4
      = (kernLoop rh h ops1 g).bind fun p =>
          nock (C (listNoun Pole.toNoun p.1) (C (A rh) (C (listNoun Pole.toNoun ops1)
            (C (A rt) (knT x ctx r (Need.both d h t) ops1 p.2))))) knB5 := by
  have ih := ihh rh ops1 g
  nock_open knB4
  simp only [knT, compCore] at ih ⊢
  generalize comp.door = Dr at ih ⊢
  generalize listNoun Pole.toNoun ops1 = N at ih ⊢
  cases e : kernLoop rh h ops1 g with
  | none =>
    rw [e] at ih
    simp [nock_exec, Need.toNoun, ih]
  | some p =>
    obtain ⟨o1, g1⟩ := p
    rw [e] at ih
    simp only [Option.map_some] at ih
    simp only [Option.bind_some]
    generalize listNoun Pole.toNoun o1 = N1 at ih ⊢
    simp [nock_exec, Need.toNoun, ih]

/-- The `=?` test after the head, the `%cel` and the `%mov`. -/
theorem kn_s5 (x : GenRest) (ctx : Noun) (r d : Nat) (h t : Need) (ops1 opsh : List Pole)
    (g : Gen (TreapMap mugF)) (rt rh : Nat) (hs : ∃ e, opsh = e ++ ops1) :
    nock (C (listNoun Pole.toNoun opsh) (C (A rh) (C (listNoun Pole.toNoun ops1)
      (C (A rt) (knT x ctx r (Need.both d h t) ops1 g))))) knB5
      = if r = d then none else some (C (listNoun Pole.toNoun (Pole.mov r d :: Pole.cel d ::
          (if opsh ≠ ops1 then Pole.hed d rh :: opsh else opsh))) (genNoun g x)) := by
  nock_open knB5
  by_cases hc : opsh = ops1
  · subst hc
    simp only [ne_eq, not_true_eq_false, if_false, listNoun, Pole.toNoun]
    simp only [knT, compCore]
    generalize listNoun Pole.toNoun opsh = N
    by_cases hrd : r = d
    · subst hrd; simp [nock_exec, Need.toNoun]
    · simp [nock_exec, Need.toNoun, hrd, Tag.cel, Tag.mov]
  · obtain ⟨e, he⟩ := hs
    have hne : listNoun Pole.toNoun opsh ≠ listNoun Pole.toNoun ops1 := by
      intro hq; subst he; exact hc ((kn_suf_eq Pole.toNoun e ops1).1 hq)
    simp only [ne_eq, hc, not_false_eq_true, if_true, listNoun, Pole.toNoun]
    simp only [knT, compCore]
    generalize listNoun Pole.toNoun opsh = N1 at hne ⊢
    generalize listNoun Pole.toNoun ops1 = N at hne ⊢
    by_cases hrd : r = d
    · subst hrd; simp [nock_exec, Need.toNoun, eqCode, hne]
    · simp [nock_exec, Need.toNoun, hrd, eqCode, hne, Tag.cel, Tag.mov, Tag.hed]

/-- **`%both`** from the links of its head and tail. -/
theorem kn_both (x : GenRest) (ctx : Noun) (d : Nat) (h t : Need) (ihh : KnAt x ctx h)
    (iht : KnAt x ctx t) : KnAt x ctx (Need.both d h t) := by
  intro r ops g
  rw [kn_s1, kn_s2 x ctx r d h t ops _ g.re iht]
  simp only [kernLoop, kernBoth, bind, StateT.bind, re, crashM, pure, StateT.pure]
  cases e1 : kernLoop g.re t ops { g with re := g.re + 1 } with
  | none => simp [e1]
  | some p1 =>
    obtain ⟨o1, g1⟩ := p1
    have hs1 := kernLoop_suf _ _ _ _ _ e1
    simp only [Option.bind_some, e1, Function.comp_apply]
    rw [kn_s3 x ctx r d h t ops o1 g1 g.re hs1]
    generalize hO : (if o1 ≠ ops then Pole.tal d g.re :: o1 else o1) = O1
    rw [kn_s4 x ctx r d h t O1 _ g.re g1.re ihh]
    cases e2 : kernLoop g1.re h O1 { g1 with re := g1.re + 1 } with
    | none => simp [e1, ← hO, e2]
    | some p2 =>
      obtain ⟨o2, g2⟩ := p2
      have hs2 := kernLoop_suf _ _ _ _ _ e2
      simp only [Option.bind_some]
      rw [kn_s5 x ctx r d h t O1 o2 g2 g.re g1.re hs2]
      by_cases hrd : r = d
      · simp only [hrd, if_true, crashM]; rfl
      · simp only [hrd, if_false, StateT.pure, pure, Option.map_some]

/-- **The loop of `+kern-need` is `kernLoop`**, on every need. -/
theorem kn_at (x : GenRest) (ctx : Noun) : ∀ ned : Need, KnAt x ctx ned
  | Need.none => fun r ops g => kn_none x ctx r ops g
  | Need.this d => fun r ops g => kn_this x ctx r d ops g
  | Need.both d h t => kn_both x ctx d h t (kn_at x ctx h) (kn_at x ctx t)
  | Need.pair p q => fun r ops g => by
      rw [kn_pair, kn_both x ctx g.re p q (kn_at x ctx p) (kn_at x ctx q)]
      simp only [kernLoop, bind, StateT.bind, re, Option.bind_some]

end Compiler
end Formalization
