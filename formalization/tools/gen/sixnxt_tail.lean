/-! ## The top -/

/-- `[6 [3 [0 2]] [0 3] [1 0]]` meets `RunTE`: the test `pickD_three2`,
`pickF_pure`, the branches `sixN_of_uok`. -/
theorem six3N_runTE (lib : Lib) {N : Needs} (env : CallEnv) (P : Noun → Prop) :
    RunTE (S := S) (Map := Map) lib N env P (n4 (A 6) (n2 (A 3) (slot 2)) (slot 3) (quote (A 0)))
      (Nomm.n6 (Nomm.n3 (Nomm.n0 2)) (Nomm.n0 3) (Nomm.n1 (A 0))) :=
  six_nextT lib env (pickD_three2 lib env P) (pickF_pure env rfl rfl)
    (sixN_of_uok lib env (uok_x lib (fragX_n0 (by decide)))
      (fun s hs gul tm r => mink_pure (codeOK_none lib) rfl ((CallTreeA.n0 3).annot P) hs gul tm r) rfl)
    (sixN_of_uok lib env (uok_x lib (FragX.frag (nm := Nomm.n1 (A 0)) fun _ => trivial))
      (fun s hs gul tm r => mink_pure (codeOK_none lib) rfl ((CallTreeA.n1 (A 0)).annot P) hs gul tm r) rfl)
    (by decide)

/-- **`[4 [6 [3 [0 2]] [0 3] [1 0]]]` meets both halves of the contract**:
a `%6` under `%next`, the operand of `%4`. -/
theorem fourSix_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.n4 (Nomm.n6 (Nomm.n3 (Nomm.n0 2)) (Nomm.n0 3) (Nomm.n1 (A 0)))) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n2 (A 4) (n4 (A 6) (n2 (A 3) (slot 2)) (slot 3) (quote (A 0)))) [s] c ∧
      ContractBwd lib N s (n2 (A 4) (n4 (A 6) (n2 (A 3) (slot 2)) (slot 3) (quote (A 0)))) [s] c :=
  have H := finishLUC_contractGBW (S := S) (Map := Map) lib (P := fun _ => True) N
    (fun hr => four_doneT lib (six3N_runTE lib env _) (minkC4_four lib _ _) (by decide) (by simp [gen0]) rfl
      upBelow_gen0 clear_gen0 condBelow_gen0 hr) hc
  ⟨H.1, fun s => H.2 s trivial⟩

/-- **`[3 [6 [3 [0 2]] [0 3] [1 0]]]` meets both halves of the contract**:
a `%6` under `%next`, the operand of `%3`. -/
theorem threeSix_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.n3 (Nomm.n6 (Nomm.n3 (Nomm.n0 2)) (Nomm.n0 3) (Nomm.n1 (A 0)))) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n2 (A 3) (n4 (A 6) (n2 (A 3) (slot 2)) (slot 3) (quote (A 0)))) [s] c ∧
      ContractBwd lib N s (n2 (A 3) (n4 (A 6) (n2 (A 3) (slot 2)) (slot 3) (quote (A 0)))) [s] c :=
  have H := finishLUC_contractGBW (S := S) (Map := Map) lib (P := fun _ => True) N
    (fun hr => three_doneT lib (six3N_runTE lib env _) (minkC3_three lib _ _) (by decide) (by simp [gen0]) rfl
      upBelow_gen0 clear_gen0 condBelow_gen0 hr) hc
  ⟨H.1, fun s => H.2 s trivial⟩

/-- **A test that begins under `%pick` with the block `[brn re z o]`** (the
indirect call, `[0 axe]`) and whose need has no entries meets `PickF`
(`runLC_pick_next`, `noEnt_of_noEntF`). -/
theorem pickF_of_next (env : CallEnv) {nm : Nomm}
    (hs : (∃ p q, nm = Nomm.n2 p q Option.none) ∨ (∃ ax, 1 ≤ ax ∧ nm = Nomm.n0 ax)) (hn : NoEntF nm) :
    PickF (S := S) (Map := Map) env nm := by
  intro sup z o region g0 g1 nex h
  rw [runLC_pick_next env sup hs z o region g0] at h
  exact entries_nil_flat (noEnt_of_noEntF (S := S) (Map := Map) env hn
    (goal := CGoal.next (lazyReg g0.re) (jmp0 g0.bo)) trivial h)

/-- `[6 [2 [0 3] [0 2]] [0 3] [1 0]]`, a calling test, meets `RunTE`: the
test `pickD_of_pickTree`, `pickF_of_next`. -/
theorem six2N_runTE (lib : Lib) {N : Needs} (env : CallEnv) (P : Noun → Prop) :
    RunTE (S := S) (Map := Map) lib N env P (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (slot 3) (quote (A 0)))
      (Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 3) (Nomm.n1 (A 0))) :=
  six_nextT lib env
    (pickD_of_pickTree lib env (PickTree.ind (CallTreeA.n0 3) (CallTreeA.n0 2))
      (NoEntF.ind rfl rfl (NoEntF.pure rfl rfl)))
    (pickF_of_next env (Or.inl ⟨_, _, rfl⟩) (NoEntF.ind rfl rfl (NoEntF.pure rfl rfl)))
    (sixN_of_uok lib env (uok_x lib (fragX_n0 (by decide)))
      (fun s hs gul tm r => mink_pure (codeOK_none lib) rfl ((CallTreeA.n0 3).annot P) hs gul tm r) rfl)
    (sixN_of_uok lib env (uok_x lib (FragX.frag (nm := Nomm.n1 (A 0)) fun _ => trivial))
      (fun s hs gul tm r => mink_pure (codeOK_none lib) rfl ((CallTreeA.n1 (A 0)).annot P) hs gul tm r) rfl)
    (by decide)

/-- **`[4 [6 [2 [0 3] [0 2]] [0 3] [1 0]]]` meets both halves of the
contract**: a `%6` with a calling test under `%next`, the operand of `%4`. -/
theorem fourSixCall_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.n4 (Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 3) (Nomm.n1 (A 0)))) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n2 (A 4) (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (slot 3) (quote (A 0)))) [s] c ∧
      ContractBwd lib N s (n2 (A 4) (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (slot 3) (quote (A 0)))) [s] c :=
  have H := finishLUC_contractGBW (S := S) (Map := Map) lib (P := fun _ => True) N
    (fun hr => four_doneT lib (six2N_runTE lib env _) (minkC4_four lib _ _) (by decide) (by simp [gen0]) rfl
      upBelow_gen0 clear_gen0 condBelow_gen0 hr) hc
  ⟨H.1, fun s => H.2 s trivial⟩

-- The code of `fourSixCall_contract`'s nomm exists and agrees with `+mink`.
#guard SixCheck.sem [Nomm.n4 (Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 3) (Nomm.n1 (A 0)))] ==
  (1, 1, 24, 24)

-- The whole-subject code of both nomms exists and agrees with `+mink` on
-- the 24 subjects of `CompSixLSCheck.lean`.
#guard SixCheck.sem [Nomm.n4 (Nomm.n6 (Nomm.n3 (Nomm.n0 2)) (Nomm.n0 3) (Nomm.n1 (A 0))),
  Nomm.n3 (Nomm.n6 (Nomm.n3 (Nomm.n0 2)) (Nomm.n0 3) (Nomm.n1 (A 0)))] == (2, 2, 48, 48)

end Comp
end SkaModel
end Formalization
