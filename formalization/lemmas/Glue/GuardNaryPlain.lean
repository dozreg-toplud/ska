import lemmas.Glue.SplitDefRun

/-!
# `GuardNaryC` on `PlainNC`: the n-ary entry from `KIMid` alone (track G)

LEDGER 2.c.  The n-ary final pass `finishLFC` on `PlainNC` (`PlainN`,
nothing baked): the top run, `+need-ord-alloc-regs`, `+coerce-lazy` of the
run's lazy need from the allocated input need, the empty bake's `+add-ops`,
then `+to-straight`.  Nothing is baked, so the inputs are a run
(`isRun_needOrdAllocRegs`) and `+to-straight` takes the RENAMING path by
`proxRen cond (hasProxies cond) (renReg r0 n)` (`toStraightF_run`): no map
path is reached on this class.

* `kpa_sureLoop`, `kpa_coerceLazy`, `kpa_coerceList`, `kpa_coerceLazyL`:
  `+coerce-lazy` keeps `InvA` at `FL` labels when the input need's
  registers lie in `[R1, R2)` and every sure need of the lazy is distinct
  and below `R1` (each `+kern-need` is `kpa_kernAdd`; the `%mov`s have no
  split);
* `ks_sureLoop`, `ks_coerceLazy`, `ks_coerceList`, `ks_coerceLazyL`: the
  same keeps `SDS` (`Glue/SplitDefBase.lean`);
* `nary_noKey`: at the state the final pass reads, a defined register is no
  key of `cond` (track D's `IL` at the end of the top run, carried through
  `+coerce-lazy` as in `tn_all`);
* **`guardNaryC_plain`**: `GuardNaryC` on `PlainNC` from `KIMid`;
* **`entryNary_plain`**: `EntryNary` on `PlainNC` from `KIMid` alone (track
  D's `optInNary_plain`, `readsInNary_plain`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Lazy Raw

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map] [HoonMapKeys Map]

/-! ## The labels of the entries of a lazy need -/

mutual
theorem lzL_ent {P : Nat → Prop} : ∀ (l : Lazy S), LzL P l → ∀ e ∈ entries l, P e.1
  | mk s f b, h, e, he => by
    cases h with
    | mk h1 h2 h3 h4 h5 h6 =>
      simp only [entries, List.mem_append] at he
      rcases he with he | he
      · exact lzL_entB b h5 h6 e he
      · exact lzL_entF f h1 h2 h3 h4 e he

theorem lzL_entB {P : Nat → Prop} : ∀ (b : List (Nat × Lazy S)), (∀ e ∈ b, P e.1) → (∀ e ∈ b, LzL P e.2) →
    ∀ e ∈ bondEntries b, P e.1
  | [], _, _, e, he => by simp [bondEntries] at he
  | (o, l) :: rest, h5, h6, e, he => by
    simp only [bondEntries, List.mem_append, List.mem_cons] at he
    rcases he with (rfl | he) | he
    · exact h5 _ List.mem_cons_self
    · exact lzL_ent l (h6 _ List.mem_cons_self) e he
    · exact lzL_entB rest (fun e h => h5 e (List.mem_cons_of_mem _ h)) (fun e h => h6 e (List.mem_cons_of_mem _ h))
        e he

theorem lzL_entF {P : Nat → Prop} : ∀ (f : List (ForkE S)), (∀ e ∈ f, P e.1.1) → (∀ e ∈ f, LzL P e.1.2) →
    (∀ e ∈ f, P e.2.1) → (∀ e ∈ f, LzL P e.2.2) → ∀ e ∈ forkEntries f, P e.1
  | [], _, _, _, _, e, he => by simp [forkEntries] at he
  | ((oy, y), (on, n)) :: rest, h1, h2, h3, h4, e, he => by
    simp only [forkEntries, List.mem_append, List.mem_cons] at he
    rcases he with ((rfl | he) | (rfl | he)) | he
    · exact h1 _ List.mem_cons_self
    · exact lzL_ent y (h2 _ List.mem_cons_self) e he
    · exact h3 _ List.mem_cons_self
    · exact lzL_ent n (h4 _ List.mem_cons_self) e he
    · exact lzL_entF rest (fun e h => h1 e (List.mem_cons_of_mem _ h)) (fun e h => h2 e (List.mem_cons_of_mem _ h))
        (fun e h => h3 e (List.mem_cons_of_mem _ h)) (fun e h => h4 e (List.mem_cons_of_mem _ h)) e he
end

/-! ## `+coerce-lazy` over `KPA` -/

theorem noSplit_mov (r d : Nat) : NoSplit [Pole.mov r d] := fun p hp => by
  simp only [List.mem_singleton] at hp; subst hp; rfl

/-- `+sure-require-look` of a distinct need below `r` (`r ≤ r0`, the form of
`rs_srl` that allows an empty input need). -/
theorem rs_srlN (r r0 : Nat) (sur : Sure S) (hr : r ≤ r0) (hd : Distinct sur.ned) (hn : NB r sur.ned) :
    RS r0 (fun r' (ned : Need) => Distinct ned ∧ ∀ y, NMem ned y → (y < r ∨ r0 ≤ y) ∧ y < r')
      (sureRequireLook sur : CM Map Need) := by
  intro g x g' hg e
  have L := sureRequireLook_spec e
  refine ⟨L.dist hd (fun y hy => by have := hn y hy; omega), fun y hy => ?_⟩
  rcases L.mem y hy with h | ⟨h1, h2⟩
  · have := hn y h; have := L.le; omega
  · exact ⟨Or.inr (by omega), h2⟩

/-- **`+sure-loop` keeps `InvA`**: the input need's registers lie in
`[R1, R2)`, the target's are distinct, below `re`, and outside
`[R1, R2)`. -/
theorem kpa_sureLoop (R1 R2 o : Nat) : ∀ (ned tgt : Need) (K0 : Nat → Nat → Prop) (b0 r0 : Nat), FL K0 b0 o →
    (∀ y, NMem ned y → R1 ≤ y ∧ y < R2) → R2 ≤ r0 → Distinct tgt →
    (∀ y, NMem tgt y → (y < R1 ∨ R2 ≤ y) ∧ y < r0) →
    KPA K0 b0 r0 (fun _ _ _ _ => True) (sureLoop o ned tgt : CM Map Unit)
  | Need.none, tgt, K0, b0, r0, ho, hn, hr, dt, ht => by
    simp only [sureLoop]
    exact KPA.ite' _ (fun _ => KPA.pure' fun _ _ _ _ => trivial) fun _ => KPA.crash
  | Need.this r, tgt, K0, b0, r0, ho, hn, hr, dt, ht => by
    simp only [sureLoop]
    have hr1 := hn r rfl
    exact kpa_kernAdd r tgt o ho (by omega) (fun hm => by have := ht r hm; omega) (fun y hy => (ht y hy).2) dt
  | Need.pair p q, tgt, K0, b0, r0, ho, hn, hr, dt, ht => by
    cases tgt with
    | none => simp only [sureLoop]; exact KPA.pure' fun _ _ _ _ => trivial
    | this _ => simp only [sureLoop]; exact KPA.crash
    | both _ _ _ => simp only [sureLoop]; exact KPA.crash
    | pair tp tq =>
      simp only [sureLoop]
      obtain ⟨d1, d2, -⟩ := dt
      refine KPA.bind' (kpa_sureLoop R1 R2 o p tp K0 b0 r0 ho (fun y hy => hn y (Or.inl hy)) hr d1
        (fun y hy => ht y (Or.inl hy))) fun _ K1 b1 r1 X1 _ => ?_
      exact kpa_sureLoop R1 R2 o q tq K1 b1 r1 (ho.up X1) (fun y hy => hn y (Or.inr hy))
        (by have := X1.2.1; omega) d2 (fun y hy => by have := ht y (Or.inr hy); have := X1.2.1; omega)
  | Need.both r h t, tgt, K0, b0, r0, ho, hn, hr, dt, ht => by
    cases tgt with
    | none => simp only [sureLoop]; exact KPA.pure' fun _ _ _ _ => trivial
    | this d =>
      simp only [sureLoop]
      exact KPA.ite' _ (fun _ => KPA.crash) fun _ => KPA.addOps' (guardedBody_of_noSplit (noSplit_mov r d)) ho
    | pair tp tq =>
      simp only [sureLoop]
      obtain ⟨d1, d2, -⟩ := dt
      refine KPA.bind' (kpa_sureLoop R1 R2 o h tp K0 b0 r0 ho (fun y hy => hn y (Or.inr (Or.inl hy))) hr d1
        (fun y hy => ht y (Or.inl hy))) fun _ K1 b1 r1 X1 _ => ?_
      exact kpa_sureLoop R1 R2 o t tq K1 b1 r1 (ho.up X1) (fun y hy => hn y (Or.inr (Or.inr hy)))
        (by have := X1.2.1; omega) d2 (fun y hy => by have := ht y (Or.inr hy); have := X1.2.1; omega)
    | both d th tt =>
      simp only [sureLoop]
      obtain ⟨d1, d2, -⟩ := dt
      refine KPA.ite' _ (fun _ => KPA.crash) fun _ => ?_
      refine KPA.bind' (KPA.addOps' (guardedBody_of_noSplit (noSplit_mov r d)) ho) fun _ K1 b1 r1 X1 _ => ?_
      refine KPA.bind' (kpa_sureLoop R1 R2 o h th K1 b1 r1 (ho.up X1) (fun y hy => hn y (Or.inr (Or.inl hy)))
        (by have := X1.2.1; omega) d1
        (fun y hy => by have := ht y (Or.inr (Or.inl hy)); have := X1.2.1; omega)) fun _ K2 b2 r2 X2 _ => ?_
      exact kpa_sureLoop R1 R2 o t tt K2 b2 r2 ((ho.up X1).up X2) (fun y hy => hn y (Or.inr (Or.inr hy)))
        (by have := X1.2.1; have := X2.2.1; omega) d2
        (fun y hy => by have := ht y (Or.inr (Or.inr hy)); have := X1.2.1; have := X2.2.1; omega)

/-- **`+coerce-lazy` of one sure need keeps `InvA`.** -/
theorem kpa_coerceLazy (R1 R2 : Nat) (ned : Need) (less : Cape) (o : Nat) (sur : Sure S)
    {K0 : Nat → Nat → Prop} {b0 r0 : Nat} (ho : FL K0 b0 o) (hd : Distinct sur.ned) (hb : NB R1 sur.ned)
    (hn : ∀ y, NMem ned y → R1 ≤ y ∧ y < R2) (h12 : R1 ≤ R2) (h2 : R2 ≤ r0) :
    KPA K0 b0 r0 (fun _ _ _ _ => True) (coerceLazy ned o sur less : CM Map Unit) := by
  unfold coerceLazy
  refine KPA.bind' (KPA.same fun g x g' e => ?_) fun lok K1 b1 r1 X1 _ => ?_
  · obtain ⟨l, -, e⟩ := Option.map_eq_some_iff.mp e
    cases e; exact ⟨rfl, rfl, rfl, Nat.le_refl _⟩
  refine KPA.bind' ((KPA.sureRequireLook' _).andR
    (rs_srlN R1 r1 ⟨sur.ned, lok⟩ (by have := X1.2.1; omega) hd hb)) fun tgt K2 b2 r2 X2 ht => ?_
  obtain ⟨-, dt, mt⟩ := ht
  exact kpa_sureLoop R1 R2 o ned tgt K2 b2 r2 (ho.up (X1.trans X2)) hn
    (by have := X1.2.1; have := X2.2.1; omega) dt
    (fun y hy => by have := mt y hy; have := X1.2.1; omega)

/-- `+coerce-lazy` of a list of entries keeps `InvA`. -/
theorem kpa_coerceList (R1 R2 : Nat) (ned : Need) (less : Cape) (hn : ∀ y, NMem ned y → R1 ≤ y ∧ y < R2)
    (h12 : R1 ≤ R2) : ∀ (L : List (Nat × Lazy S)) (K0 : Nat → Nat → Prop) (b0 r0 : Nat),
    (∀ e ∈ L, FL K0 b0 e.1 ∧ Distinct e.2.sure.ned ∧ NB R1 e.2.sure.ned) → R2 ≤ r0 →
    KPA K0 b0 r0 (fun _ _ _ _ => True) (coerceList ned less L : CM Map Unit)
  | [], K0, b0, r0, _, _ => by rw [coerceList]; exact KPA.pure' fun _ _ _ _ => trivial
  | (o, l) :: rest, K0, b0, r0, hL, hr => by
    rw [coerceList]
    have h0 := hL _ List.mem_cons_self
    refine KPA.bind' (kpa_coerceLazy R1 R2 ned less o l.sure h0.1 h0.2.1 h0.2.2 hn h12 hr)
      fun _ K1 b1 r1 X1 _ => ?_
    exact kpa_coerceList R1 R2 ned less hn h12 rest K1 b1 r1
      (fun e he => let h := hL e (List.mem_cons_of_mem _ he); ⟨h.1.up X1, h.2⟩) (Nat.le_trans hr X1.2.1)

theorem coerceLazyL_list (ned : Need) (less : Cape) (o : Nat) (l : Lazy S) :
    (coerceLazyL ned less o l : CM Map Unit) = coerceList ned less ((o, l) :: entries l) := by
  rw [coerceLazyL_flat]; rfl

/-- **`+coerce-lazy` of a lazy need keeps `InvA`.** -/
theorem kpa_coerceLazyL (R1 R2 : Nat) (ned : Need) (less : Cape) (o : Nat) (l : Lazy S)
    {K0 : Nat → Nat → Prop} {b0 r0 : Nat}
    (hL : ∀ e ∈ (o, l) :: entries l, FL K0 b0 e.1 ∧ Distinct e.2.sure.ned ∧ NB R1 e.2.sure.ned)
    (hn : ∀ y, NMem ned y → R1 ≤ y ∧ y < R2) (h12 : R1 ≤ R2) (h2 : R2 ≤ r0) :
    KPA K0 b0 r0 (fun _ _ _ _ => True) (coerceLazyL ned less o l : CM Map Unit) := by
  rw [coerceLazyL_list]
  exact kpa_coerceList R1 R2 ned less hn h12 _ K0 b0 r0 hL h2

/-! ## `+coerce-lazy` over `KS` -/

theorem ks_sureLoop (o : Nat) : ∀ (ned tgt : Need), KSB (sureLoop o ned tgt : CM Map Unit)
  | Need.none, tgt => by simp only [sureLoop]; exact KS.ite' _ (KS.pure' trivial) KS.crash
  | Need.this r, tgt => by
    simp only [sureLoop]; exact KS.bind' (ks_kernNeed r tgt) fun ops h => KS.addOps' o h
  | Need.pair p q, tgt => by
    cases tgt with
    | pair tp tq => simp only [sureLoop]; exact KS.bind' (ks_sureLoop o p tp) fun _ _ => ks_sureLoop o q tq
    | none => simp only [sureLoop]; exact KS.pure' trivial
    | this _ => simp only [sureLoop]; exact KS.crash
    | both _ _ _ => simp only [sureLoop]; exact KS.crash
  | Need.both r h t, tgt => by
    cases tgt with
    | none => simp only [sureLoop]; exact KS.pure' trivial
    | this d =>
      simp only [sureLoop]; exact KS.ite' _ KS.crash (KS.addOps' _ (sdBody_of_noSplit (noSplit_mov r d)))
    | pair tp tq => simp only [sureLoop]; exact KS.bind' (ks_sureLoop o h tp) fun _ _ => ks_sureLoop o t tq
    | both d th tt =>
      simp only [sureLoop]
      exact KS.ite' _ KS.crash (KS.bind' (KS.addOps' _ (sdBody_of_noSplit (noSplit_mov r d))) fun _ _ =>
        KS.bind' (ks_sureLoop o h th) fun _ _ => ks_sureLoop o t tt)

theorem ks_coerceLazy (ned : Need) (less : Cape) (o : Nat) (sur : Sure S) :
    KSB (coerceLazy ned o sur less : CM Map Unit) := by
  unfold coerceLazy
  exact KS.bind' (KS.lift' _) fun _ _ => KS.bind' (ks_sureRequireLook _) fun _ _ => ks_sureLoop o ned _

theorem ks_coerceList (ned : Need) (less : Cape) : ∀ (L : List (Nat × Lazy S)),
    KSB (coerceList ned less L : CM Map Unit)
  | [] => by rw [coerceList]; exact KS.pure' trivial
  | (o, l) :: rest => by
    rw [coerceList]; exact KS.bind' (ks_coerceLazy ned less o l.sure) fun _ _ => ks_coerceList ned less rest

theorem ks_coerceLazyL (ned : Need) (less : Cape) (o : Nat) (l : Lazy S) :
    KSB (coerceLazyL ned less o l : CM Map Unit) := by
  rw [coerceLazyL_list]; exact ks_coerceList ned less _

/-! ## No defined register is a key -/

/-- **At the state the n-ary final pass reads, a defined register is no key
of `cond`** (track D's `IL` at the end of the top run, through
`+need-ord-alloc-regs` and `+coerce-lazy`, as in `tn_all`). -/
theorem nary_noKey {env : CallEnv} {nm : Nomm} (hp : PlainN nm) {ord : NeedOrd} {less : Cape}
    {nex : NextL S} {g1 g2 g3 g4 : Comp.Gen Map} {nedF : Need}
    (h1 : runLC env Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1))
    (h2 : (needOrdAllocRegs ord : CM Map Need) g1 = some (nedF, g2))
    (h3 : (coerceLazyL nedF less nex.th.there nex.laz : CM Map Unit) g2 = some ((), g3))
    (h4 : (addOps nex.th.there [] : CM Map Unit) g3 = some ((), g4)) :
    ∀ x, Defd g4.blocks x → HoonMap.get g4.cond x = Option.none := by
  obtain ⟨J1, L1⟩ := liveRun_plain_topOfL env (armsLL_of env splitSpecL intoSpecL) hp h1
  have I1 : IL (fun _ _ => False) (CGoalL.next nex.laz nex.th) g1 := J1
  have SA1 := topSAR_plain (S := S) (Map := Map) (env := env) hp nex g1 h1
  have S1 := tn_sip I1 SA1
  obtain ⟨-, hap, hent⟩ := (I1.goal : GoalL g1 (CGoalL.next nex.laz nex.th))
  obtain ⟨⟨k2, e2⟩, l2, -, mF⟩ := needOrdAllocRegs_spec ord g1 g2 nedF h2
  subst e2
  have l2' : g1.re ≤ k2 := l2
  have I0 : CoI (fun _ : Map Blob => True) (fun k => 3 * k) 0 nedF k2
      ((nex.th.there, nex.laz) :: entries nex.laz) { g1 with re := k2 } := by
    refine ⟨sip_reg S1 l2', Nat.le_refl _, fun r hr => ⟨(mF r hr).2, fun d => ?_⟩, hap, fun e he => ?_⟩
    · have := S1.defd_lt d; have := (mF r hr).1; omega
    · obtain ⟨⟨b, hb, -⟩, ds, hr⟩ := hent e he
      exact ⟨⟨b, hb⟩, ds, fun r hm => ⟨by have := (hr r hm).1; omega,
        fun m => by have := (hr r hm).1; have := (mF r m).1; omega, (hr r hm).2⟩⟩
  obtain ⟨⟨I3, D3⟩, P, pP, kP, rP, -⟩ := coerceLazyL_prepI (S := S) (Map := Map)
    (fun rest g => CoI (fun _ : Map Blob => True) (fun k => 3 * k) 0 nedF k2 rest g ∧
      CoD g1.re ((nex.th.there, nex.laz) :: entries nex.laz) g1.blocks rest g)
    (fun _ _ _ _ _ _ hI hs => tn_step l2' hI hs) ⟨I0, fun e he => he, fun y d => Or.inl d⟩ h3
  have hd3 : g3.drop = false := I3.1.drop
  obtain ⟨S4, b4, hb4, e4, -, -⟩ := sip_addOps I3.1 (opsOK_nil g3) h4
  have get4 : ∀ k, HoonMap.get g4.blocks k = HoonMap.get g3.blocks k := fun k => by
    rw [e4]
    by_cases e : k = nex.th.there
    · subst e; rw [get_put_self, hb4, pre_nil]
    · rw [get_put_ne e]
  have c4 : g4.cond = g1.cond := by
    obtain ⟨b4', -, e4'⟩ := addOps_spec h4 hd3
    have k3 : g3.cond = g1.cond := (kc_coerceLazyL nedF less _ _).keep { g1 with re := k2 } _ _ h3
    rw [e4']
    exact k3
  have dd4 : ∀ y, Defd g4.blocks y → Defd g3.blocks y := fun y d => by
    obtain ⟨o, b, hb, m⟩ := defd_iff.mp d
    exact defd_iff.mpr ⟨o, b, by rw [← get4]; exact hb, m⟩
  intro x d
  rw [c4]
  cases e : HoonMap.get g1.cond x with
  | none => rfl
  | some v =>
    obtain ⟨k1, k2', k3, -, -⟩ := I1.cond x v e
    rcases D3.2 x (dd4 x d) with d1 | ⟨e', he', m⟩ | hx
    · exact absurd d1 k2'
    · exact absurd ⟨e', he', m⟩ k3
    · omega

/-! ## The n-ary guard -/

/-- **`GuardNaryC` on `PlainNC`** from `KIMid`. -/
theorem guardNaryC_plain (hD : ∀ env, KIMid S Map env) : GuardNaryC S Map PlainNC := by
  intro env N bl cape bake nm ord c hf hs
  obtain ⟨hp, hbake⟩ : PlainN nm ∧ ∀ ned, bake ned = (ned, []) := hf
  unfold finishLFC at hs
  obtain ⟨⟨nex, g1⟩, h1, hA⟩ := Option.bind_eq_some_iff.mp hs
  simp only at hA
  split at hA
  · cases hA
  obtain ⟨⟨nedF, g2⟩, h2, hB⟩ := Option.bind_eq_some_iff.mp hA
  rw [hbake] at hB
  simp only [List.map_nil] at hB
  obtain ⟨⟨u3, g3⟩, h3, hC⟩ := Option.bind_eq_some_iff.mp hB
  obtain ⟨⟨u4, g4⟩, h4, hT⟩ := Option.bind_eq_some_iff.mp hC
  cases u3; cases u4
  -- `InvA` through the top run
  have hn : NoSixC nm := noSix_of_plain nm hp
  have h1M : runLCM env true Option.none nm (CGoalL.done : CGoalL S) [] gen0 = some (nex, g1) := by
    rw [runLCM_eq env true nm (by simp [plainN_noDirect nm hp])]; exact h1
  obtain ⟨K1, hI1, X1, hR1⟩ := (runG_lcm (hD env) nm hn Option.none (fun _ _ => False) 1 0 CGoalL.done [] trivial
    trivial).k _ gen0 nex g1 invA_gen0 (by simp [gen0]) (XB.refl _ _ _) h1M
  have h0 : 0 < g1.bo := Nat.lt_of_lt_of_le (by simp [gen0]) X1.1
  -- track D's `IL` for the entries' needs
  obtain ⟨J1, -⟩ := liveRun_plain_topOfL env (armsLL_of env splitSpecL intoSpecL) hp h1
  have I1 : IL (fun _ _ => False) (CGoalL.next nex.laz nex.th) g1 := J1
  obtain ⟨-, -, hent⟩ := (I1.goal : GoalL g1 (CGoalL.next nex.laz nex.th))
  -- `+need-ord-alloc-regs`
  have ND := nary_noKey hp h1 h2 h3 h4
  obtain ⟨⟨k2, e2⟩, l2, -, mF⟩ := needOrdAllocRegs_spec ord g1 g2 nedF h2
  have hb2 : g2.bo = g1.bo := by rw [e2]
  have hI2 : InvA K1 g2 := by rw [e2]; exact ⟨hI1.ok, hI1.drop, hI1.below, hI1.kin⟩
  -- `+coerce-lazy`
  have hL : ∀ e ∈ (nex.th.there, nex.laz) :: entries nex.laz,
      FL K1 g2.bo e.1 ∧ Distinct e.2.sure.ned ∧ NB g1.re e.2.sure.ned := by
    intro e he
    obtain ⟨-, ds, hr⟩ := hent e he
    refine ⟨?_, ds, fun y hy => (hr y hy).1⟩
    rw [hb2]
    rcases List.mem_cons.mp he with rfl | he
    · exact hR1.1
    · exact lzL_ent nex.laz hR1.2.2 e he
  obtain ⟨K3, hI3, X3, -⟩ := (kpa_coerceLazyL g1.re g2.re nedF cape nex.th.there nex.laz (K0 := K1) (b0 := g2.bo)
    (r0 := g2.re) hL mF l2 (Nat.le_refl _)).k K1 g2 () g3 hI2 (by rw [hb2]; exact h0) (XB.refl _ _ _) h3
  have hfo3 : FL K3 g3.bo nex.th.there := ((hL _ List.mem_cons_self).1).up X3
  -- the empty bake
  have h03 : 0 < g3.bo := Nat.lt_of_lt_of_le (by rw [hb2]; exact h0) X3.1
  obtain ⟨K4, hI4, X4, -⟩ := (KPA.addOps' (K0 := K3) (b0 := g3.bo) (r0 := g3.re)
    (guardedBody_of_noSplit noSplit_nil) hfo3).k K3 g3 () g4 hI3 h03 (XB.refl _ _ _) h4
  have hfo : FL K4 g4.bo nex.th.there := hfo3.up X4
  -- the proxy facts
  have s1 := ((ks_runLC (S := S) (Map := Map) env nm hp Option.none CGoalL.done []).k _ _ _ sds_gen0 h1).1
  have s2 : SDS g2 := by rw [e2]; exact s1
  have s3 := ((ks_coerceLazyL nedF cape nex.th.there nex.laz).k _ _ _ s2 h3).1
  have s4 := ((KS.addOps' (Map := Map) nex.th.there (sdBody_of_noSplit noSplit_nil)).k _ _ _ s3 h4).1
  have dq : ∀ k b, HoonMap.get g4.blocks k = some b → ∀ q ∈ b.body, ∀ x, aliasDst q = some x →
      Defd g4.blocks x := by
    intro k b hb q hq x hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
    exact ⟨(k, some i), b, q, hb, hi, hx⟩
  have P : ProxOKN g4.blocks g4.cond := by
    refine ⟨fun k b hb x hx => ND x ?_, fun k b hb p hpb s hs => ND s ?_⟩
    · rcases hx with hx | ⟨q, hq, hx⟩
      · exact ⟨(k, Option.none), b, hb, hx⟩
      · exact dq k b hb q hq x hx
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hpb
      obtain ⟨j, -, q, hq, hx⟩ := s4 k b hb i p s hi hs
      exact dq k b hb q (List.mem_of_getElem? hq) s hx
  -- the final pass: the renaming path
  rw [toStraightF_run _ _ _ (isRun_needOrdAllocRegs h2)] at hT
  obtain ⟨start, hst, hT⟩ := Option.bind_eq_some_iff.mp hT
  obtain ⟨new, hnew, rfl⟩ := Option.map_eq_some_iff.mp hT
  have P0 := proxOKN_start P hst
  have B1 := blocksOKA_npN (blocksOKA_start hI4.ok hfo.2 hst) P0
  have R := celAnn_renameN B1 (renA_proxN P0 _ _) hnew
  exact ⟨R.1, _, R.2⟩

/-- **`EntryNary` on `PlainNC` from `KIMid` alone** (track D's
`optInNary_plain`, `readsInNary_plain`). -/
theorem entryNary_plain (lib : Lib) (hD : ∀ env, KIMid S Map env) : EntryNary S Map lib PlainNC :=
  entryNary_of lib optInNary_plain readsInNary_plain (guardNaryC_plain hD)

end Glue
end SkaModel
end Formalization
