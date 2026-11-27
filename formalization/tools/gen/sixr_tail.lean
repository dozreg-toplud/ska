/-! ## The tree of `R` -/

theorem nommR_eq : nommR = Nomm.n6 (Nomm.n3 (Nomm.n0 3)) (Nomm.n7 tenR callR) (Nomm.n0 3) := rfl

/-- The formula of `R`, with `fR` the formula of its call. -/
def nommRFOf (fR : Noun) : Noun := n4 (A 6) (n2 (A 3) (slot 3)) (n3 (A 7) tenRF fR) (slot 3)

/-- `[3 [0 3]]`, the test of `R`: `PickD` with the bound `0`. -/
theorem pickD_three3 (lib : Lib) {N : Needs} (env : CallEnv) (P : Noun → Prop) :
    PickD (S := S) (Map := Map) lib N env P (n2 (A 3) (slot 3)) (Nomm.n3 (Nomm.n0 3)) 0 :=
  pickD_of_uok lib env (uok_x lib (FragX.three (FragX.frag (nm := Nomm.n0 3) fun _ => trivial)))
    (fun s hs gul tm r => mink_pure (codeOK_none lib) rfl ((CallTreeA.three (CallTreeA.n0 3)).annot P) hs gul tm r)
    (by decide)

/-- `[0 3]`, the no branch of `R`: `SixD` with the bound `0`. -/
theorem sixD_slot3 (lib : Lib) {N : Needs} (env : CallEnv) (P : Noun → Prop) :
    SixD (S := S) (Map := Map) lib N env P (slot 3) (Nomm.n0 3) 0 :=
  sixD_of_callTreeA lib env (CallTreeA.n0 3) (NoEntF.pure rfl rfl) P

/-- **The yes branch of `R`, `[7 [10 [3 [0 7]] [0 1]] R-call]`, meets
`DoneE`** when the call does on the products of the `%10`. -/
theorem doneE_yesR (lib : Lib) {N : Needs} {env : CallEnv} {P : Noun → Prop} {fR : Noun}
    (Hcall : DoneE (S := S) (Map := Map) lib N env (Img lib P tenRF) fR callR) :
    DoneE (S := S) (Map := Map) lib N env P (n3 (A 7) tenRF fR) (Nomm.n7 tenR callR) :=
  doneE_seven lib (lokSE_tenR lib env P) (noEnt_pure env rfl rfl) (by decide) Hcall

/-- **`R` under `%done` meets `SixDN`**, given `Hcall`. -/
theorem sixDN_nommR (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {fR : Noun}
    (Hcall : DoneE (S := S) (Map := Map) lib N env (Img lib P tenRF) fR callR) :
    SixDN (S := S) (Map := Map) lib N env P (nommRFOf fR) nommR (0 + 0 + 0 + 2) :=
  six_doneGBN lib env (c := Nomm.n3 (Nomm.n0 3)) rfl (pickD_three3 lib env P) (sixD_of_doneE (doneE_yesR lib Hcall))
    (sixD_slot3 lib env P) (by decide)

/-- **The n-ary contract of `R`** (the code `finishLFC` makes for `nommR`,
entered with the split of a subject with the cape's axes), given `Hcall`. -/
theorem finishLFC_contractR (lib : Lib) {env : CallEnv} {P : Noun → Prop} {fR : Noun} (N : Needs)
    (Hcall : DoneE (S := S) (Map := Map) lib N env (Img lib P tenRF) fR callR)
    {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c : Straight Map} (h : finishLFC (S := S) env nommR ord less bake = some c) :
    ∀ s, P s → CapeAxes less s → ∀ args, SkaModel.split c.need s = some args →
      ContractFwd lib N s (nommRFOf fR) args c ∧ ContractBwd lib N s (nommRFOf fR) args c :=
  finishLFC_contractGBN lib N (fun hr =>
    ⟨(sixDN_nommR lib env Hcall (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).1,
      (sixDN_nommR lib env Hcall (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).2.2⟩) hbake h

/-- **The whole-subject contract of `R` with `runLC`**, given `Hcall`. -/
theorem finishLUC_contractR (lib : Lib) (env : CallEnv) {P : Noun → Prop} {fR : Noun} (N : Needs)
    (Hcall : DoneE (S := S) (Map := Map) lib N env (Img lib P tenRF) fR callR)
    {c : Straight Map} (hc : finishLUC (S := S) env nommR = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s (nommRFOf fR) [s] c ∧ ContractBwd lib N s (nommRFOf fR) [s] c :=
  finishLUC_contractGB lib N (fun hr =>
    (sixDN_nommR lib env Hcall (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).1) hc

end Comp
end SkaModel
end Formalization
