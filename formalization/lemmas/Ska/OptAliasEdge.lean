import lemmas.Ska.OptAliasFin
import lemmas.Ska.CompFrame

/-!
# The values at the start of a block of `+alias`, along the edge taken

An execution that leaves the walked block `q` by a jump to `o` reaches the
start of `o` with the register file at `q`'s end, `R`, and the pass of the
jump's arguments gives the file `R'`.  **`aedge_aok`**: if the walk state at
`q`'s end meets `AOK` on `R`, the state at the start of `o` (the global `old`
when `o` is walked, the facts of `aliasStart` refined by `aliasPars`, the
immediates of `aliasStartImms`) meets `AOK` on `R'`, given that

* the end of `q` in the code after takes a jump `j'` to `o` on `R` (from
  `afn_jump`, which also keeps `q` listed in `rev`, so `q ∈ g.rev o`);
* the parameters of `o` get the values of `j'`'s arguments (`aedge_pass`
  describes `+eval-pass` on distinct parameters that are no arguments, and
  `AOK.old` at `q`'s end turns the arguments before into those after);
* no fact or immediate at `q`'s end names a parameter of `o`;
* each register done at `o` is done at `q`'s end with the same `old`, neither
  it nor its `old` a parameter, or it is a parameter that keeps its own name.

The facts at the start name only what the facts at `q`'s end name
(`ast_start_names`) and the immediates at the start are among `q`'s
(`ast_imms_sub`): the join is weaker than each side, and the refinement only
sets flags.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map]

set_option linter.unusedSectionVars false

/-! ## What the start names -/

/-- Every fact of `m` names only what the fact of `iq` at the same key
names. -/
def NamesIn (m iq : AInfo) : Prop := ∀ r i x, m r = some i → ANames i x → ∃ i', iq r = some i' ∧ ANames i' x

theorem aedge_joinE_names {a b : InfoReg} {x : Nat} (h : ANames (joinRegE a b) x) : ANames a x ∧ ANames b x := by
  unfold joinRegE at h
  split at h
  · rename_i e; subst e; exact ⟨h, h⟩
  · exact ast_join_names h

theorem aedge_namesL {a b iq : AInfo} (h : NamesIn a iq) : NamesIn (joinInfoA a b) iq := by
  intro r i x hr hx
  cases ha : a r <;> cases hb : b r <;> simp only [joinInfoA, ha, hb, reduceCtorEq, Option.some.injEq] at hr
  subst hr; exact h r _ x ha (aedge_joinE_names hx).1

theorem aedge_namesR {a b iq : AInfo} (h : NamesIn b iq) : NamesIn (joinInfoA a b) iq := by
  intro r i x hr hx
  cases ha : a r <;> cases hb : b r <;> simp only [joinInfoA, ha, hb, reduceCtorEq, Option.some.injEq] at hr
  subst hr; exact h r _ x hb (aedge_joinE_names hx).2

theorem aedge_names_fold (g : AGen Map) (iq : AInfo) : ∀ (t : List Nat) (acc info : AInfo),
    t.foldlM (fun acc o1 => (g.info o1).map fun i1 => joinInfoA acc i1) acc = some info →
    (NamesIn acc iq ∨ ∃ q ∈ t, g.info q = some iq) → NamesIn info iq
  | [], acc, info, h, hh => by
    simp only [List.foldlM_nil] at h
    cases h
    rcases hh with hh | ⟨q, hq, _⟩
    · exact hh
    · cases hq
  | o1 :: t, acc, info, h, hh => by
    simp only [List.foldlM_cons] at h
    obtain ⟨acc', h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨i1, hi1, rfl⟩ := Option.map_eq_some_iff.mp h1
    apply aedge_names_fold g iq t _ info h
    rcases hh with hh | ⟨q, hq, hiq⟩
    · exact Or.inl (aedge_namesL hh)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [hiq] at hi1; cases hi1
        exact Or.inl (aedge_namesR fun r i x hr hx => ⟨i, hr, hx⟩)
      · exact Or.inr ⟨q, hq, hiq⟩

theorem aedge_names_jab {m m' iq : AInfo} {s : Nat} {f : InfoReg → InfoReg} (hm : NamesIn m iq)
    (hj : jabA m s f = some m') (hf : ∀ i x, ANames (f i) x → ANames i x) : NamesIn m' iq := by
  obtain ⟨i, hi, rfl⟩ := as_jab hj
  intro r i' x hr hx
  by_cases e : r = s
  · subst e; rw [as_upd_self] at hr; cases hr; exact hm r i x hi (hf i x hx)
  · rw [as_upd_other _ _ e] at hr; exact hm r i' x hr hx

/-- **The facts at the start name only what the facts of a listed predecessor
name.** -/
theorem ast_start_names {g : AGen Map} {o q : Nat} {pre : List Nat} {info iq : AInfo}
    (h : aliasStart g o pre = some info) (hq : q ∈ pre) (hiq : g.info q = some iq) : NamesIn info iq := by
  cases pre with
  | nil => cases hq
  | cons p t =>
    simp only [aliasStart] at h
    obtain ⟨i0, hi0, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨info0, hf, h⟩ := Option.bind_eq_some_iff.mp h
    have hj : NamesIn info0 iq := aedge_names_fold g iq t i0 info0 hf (by
      rcases List.mem_cons.mp hq with rfl | hq
      · rw [hiq] at hi0; cases hi0; exact Or.inl fun r i x hr hx => ⟨i, hr, hx⟩
      · exact Or.inr ⟨q, hq, hiq⟩)
    have fl : ∀ s m' (f : InfoReg → InfoReg), jabA info0 s f = some m' →
        (∀ i x, ANames (f i) x → ANames i x) → NamesIn m' iq := fun s m' f e hf => aedge_names_jab hj e hf
    split at h
    · cases h; exact hj
    obtain ⟨pb, -, h⟩ := Option.bind_eq_some_iff.mp h
    generalize pb.fin = fin at h
    cases fin with
    | brn s z o' =>
      simp only at h
      split at h
      · exact fl _ _ _ h (fun i x hx => hx)
      · split at h
        · exact fl _ _ _ h (fun i x hx => hx)
        · split at h
          · exact fl _ _ _ h (fun i x hx => hx)
          · cases h
    | brz s z o' =>
      simp only at h
      split at h
      · exact fl _ _ _ h (fun i x hx => hx)
      · split at h
        · obtain ⟨si, -, h⟩ := Option.bind_eq_some_iff.mp h
          split at h
          · exact fl _ _ _ h (fun i x hx => hx)
          · cases h; exact hj
        · cases h; exact hj
    | clq s z o' =>
      simp only at h
      split at h
      · exact fl _ _ _ h (fun i x hx => hx)
      · split at h
        · cases h; exact hj
        · cases h
    | hop => cases h; exact hj
    | lti => cases h; exact hj
    | eqq => cases h; exact hj
    | jmp => cases h; exact hj
    | jmf => cases h; exact hj
    | jsp => cases h; exact hj
    | jsf => cases h; exact hj
    | don => cases h; exact hj
    | bom => cases h; exact hj

theorem aedge_imms_fold (g : AGen Map) (mq : AImms) : ∀ (t : List Nat) (acc m : AImms),
    t.foldlM (fun acc o1 => (g.imms o1).map fun m1 => joinImmsA acc m1) acc = some m →
    ((∀ n r, r ∈ acc n → r ∈ mq n) ∨ ∃ q ∈ t, g.imms q = some mq) → ∀ n r, r ∈ m n → r ∈ mq n
  | [], acc, m, h, hh => by
    simp only [List.foldlM_nil] at h
    cases h
    rcases hh with hh | ⟨q, hq, _⟩
    · exact hh
    · cases hq
  | o1 :: t, acc, m, h, hh => by
    simp only [List.foldlM_cons] at h
    obtain ⟨acc', h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨m1, hm1, rfl⟩ := Option.map_eq_some_iff.mp h1
    apply aedge_imms_fold g mq t _ m h
    rcases hh with hh | ⟨q, hq, hmq⟩
    · exact Or.inl fun n r hr => hh n r (List.mem_filter.mp hr).1
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [hmq] at hm1; cases hm1
        exact Or.inl fun n r hr => by simpa using (List.mem_filter.mp hr).2
      · exact Or.inr ⟨q, hq, hmq⟩

/-- **The immediates at the start are among those of a listed
predecessor.** -/
theorem ast_imms_sub {g : AGen Map} {pre : List Nat} {m mq : AImms} {q : Nat}
    (h : aliasStartImms g pre = some m) (hq : q ∈ pre) (hmq : g.imms q = some mq) :
    ∀ n r, r ∈ m n → r ∈ mq n := by
  cases pre with
  | nil => cases hq
  | cons p t =>
    simp only [aliasStartImms] at h
    obtain ⟨m0, hm0, h⟩ := Option.bind_eq_some_iff.mp h
    exact aedge_imms_fold g mq t m0 m h (by
      rcases List.mem_cons.mp hq with rfl | hq
      · rw [hmq] at hm0; cases hm0; exact Or.inl fun _ _ hr => hr
      · exact Or.inr ⟨q, hq, hmq⟩)

/-! ## The edge -/

/-- A jump an end takes is one of its jumps. -/
theorem aedge_taken_mem {R : Nat → Option Noun} {fin : Termin} {j : Jmp} (h : takenR R fin = some j) :
    j ∈ getJmps fin := by
  cases fin <;> simp only [takenR, getJmps] at h ⊢
  case lti n s z o =>
    have hif : ∀ (c : Bool), (if c = true then z else o) ∈ [z, o] := fun c => by cases c <;> simp
    obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h; exact hif _
  case clq s z o =>
    obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h; cases v <;> simp
  case eqq l r z o =>
    obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.mp h; split <;> simp
  case brn s z o =>
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h; simp
    · split at h
      · cases h; simp
      · cases h
  case brz s z o =>
    obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h; split <;> simp
  case hop t => cases h; simp
  all_goals cases h

/-- The jump a listed predecessor takes to `o` is one of the edges. -/
theorem aedge_mem {g : AGen Map} {o q : Nat} {pre : List Nat} {edges : List (Nat × List (Option Nat))}
    {pb : Blob} {j : Jmp} (h : aliasEdges g o pre = some edges) (hq : q ∈ pre) (hpb : HoonMap.get g.new q = some pb)
    (hj : j ∈ getJmps pb.fin) (ho : j.there = o) : (q, j.args) ∈ edges := by
  unfold aliasEdges at h
  obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨y, hy, hfy⟩ := ast_mapM_mem hL hq
  rw [hpb] at hfy
  simp only [Option.map_some, Option.some.injEq] at hfy
  subst hfy
  exact List.mem_flatten.mpr ⟨_, hy, List.mem_filterMap.mpr ⟨j, hj, by simp [ho]⟩⟩

theorem aedge_read_put {u p : Nat} {w : Option Noun} {regs : Map (Option Noun)} (h : u ≠ p) :
    read u (HoonMap.put regs p w) = read u regs := by
  simp only [read, HoonMap.get_put, h, if_false]

/-- **`+eval-pass` on distinct parameters that are no arguments**: each
parameter gets the value of its argument (none for `~` or poison), every
other register keeps its value. -/
theorem aedge_pass : ∀ (args : List (Option Nat)) (par : List Nat) (regs R : Map (Option Noun)),
    (∀ u, some u ∈ args → u ∉ par) → par.Nodup → evalPassLoop args par regs = some R →
    ∀ (k x : Nat), par[k]? = some x →
      read x R = match args[k]? with | some (some u) => read u regs | _ => none
  | [], par, regs, R, _, _, h, k, x, hk => by
    simp only [evalPassLoop] at h
    split at h
    · rename_i e; subst e; simp at hk
    · cases h
  | _ :: _, [], _, _, _, _, h, _, _, _ => by simp [evalPassLoop] at h
  | a :: args, p :: par, regs, R, ha, hn, h, k, x, hk => by
    rw [Opt.evalPassLoop_cons] at h
    obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.mp h
    have hpn : p ∉ par := (List.nodup_cons.mp hn).1
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      have hg := Comp.evalPassLoop_frame args par _ R h p hpn
      simp only [HoonMap.get_put, if_true] at hg
      simp only [List.getElem?_cons_zero]
      cases a with
      | none =>
        simp only [argU, Option.some.injEq] at hw; subst hw
        simp [read, hg]
      | some u =>
        simp only [argU] at hw
        simp only [read, hg, hw]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk ⊢
      rw [aedge_pass args par _ R (fun u hu hm => ha u (List.mem_cons_of_mem _ hu) (List.mem_cons_of_mem _ hm))
        (List.nodup_cons.mp hn).2 h k x hk]
      split
      · rename_i u hu
        have hum : some u ∈ args := List.mem_of_getElem? hu
        exact aedge_read_put fun e => ha u (List.mem_cons_of_mem _ hum) (by rw [e]; exact List.mem_cons_self)
      · rfl

/-! ## The values at the start -/

/-- **`AOK` at the start of a block from `AOK` at the end of the predecessor
the execution came from.** -/
theorem aedge_aok {g : AGen Map} {o q : Nat} {b : Blob} {info : AInfo} {imms : AImms}
    {edges : List (Nat × List (Option Nat))} {loc0 : AInfo}
    (hst : aliasStart g o (g.rev o) = some info) (him : aliasStartImms g (g.rev o) = some imms)
    (hed : aliasEdges g o (g.rev o) = some edges) (hpa : aliasPars g b.par edges info = some loc0)
    (hq : q ∈ g.rev o) {lq : AInfo} {mq : AImms} {oq : Nat → Nat} (hlq : g.info q = some lq)
    (hmq : g.imms q = some mq) {pb : Blob} (hpb : HoonMap.get g.new q = some pb)
    {R R' : Nat → Option Noun} {Dq Do : Nat → Prop} (hok : AOK ⟨oq, lq, mq⟩ R Dq)
    {j : Jmp} (hj : takenR R pb.fin = some j) (hjo : j.there = o)
    (hpar : ∀ (k x : Nat), b.par[k]? = some x → R' x = match j.args[k]? with | some (some u) => R u | _ => none)
    (hoff : ∀ x, x ∉ b.par → R' x = R x)
    (hnm : ∀ r i x, lq r = some i → ANames i x → x ∉ b.par) (hnmi : ∀ n r, r ∈ mq n → r ∉ b.par)
    (hDo : ∀ x, Do x → (Dq x ∧ g.old x = oq x ∧ x ∉ b.par ∧ oq x ∉ b.par) ∨ (x ∈ b.par ∧ g.old x = x)) :
    AOK ⟨g.old, loc0, imms⟩ R' Do := by
  have hgo : g.rev o = [q] → GoesTo R o pb.fin := fun _ => hjo ▸ afn_goesTo hj
  have hF : FactsOK R info := ast_start hst hq hlq hok.info (fun e pb' hpb' => by
    rw [hpb] at hpb'; cases hpb'; exact hgo e)
  have hN := ast_start_names hst hq hlq
  have hI : ImmsOK R imms := ast_imms him hq hmq hok.imm
  have he : (q, j.args) ∈ edges := aedge_mem hed hq hpb (aedge_taken_mem hj) hjo
  refine ⟨fun n r hr => ?_, ?_, fun d hd => ?_⟩
  · rw [hoff r (hnmi n r (ast_imms_sub him hq hmq n r hr))]; exact hI n r hr
  · refine ast_pars hlq hok.info hnm hoff b.par edges info loc0 j.args hpa he (fun _ h => h) hpar
      (fun r i v hr hrn hv => ?_)
    rw [hoff r hrn] at hv
    refine ast_frame_set (hF r i v hr hv) (fun x hx => hoff x fun hxp => ?_)
    obtain ⟨i', hi', hx'⟩ := hN r i x hr hx
    exact hnm r i' x hi' hx' hxp
  · simp only
    rcases hDo d hd with ⟨hdq, ho, hdp, hop⟩ | ⟨-, ho⟩
    · rw [ho, hoff _ hop, hoff _ hdp]; exact hok.old d hdq
    · rw [ho]

/-! ## The structural invariant at the start -/

theorem aedge_joinReg_empL (y : InfoReg) : joinReg {} y = {} := by
  cases y; simp [joinReg, InfoReg.loobImm]

theorem aedge_joinReg_empR (x : InfoReg) : joinReg x {} = {} := by
  obtain ⟨c, l, ho, to, hh, ht, dc, im⟩ := x
  simp only [joinReg, InfoReg.loobImm, InfoReg.mk.injEq]
  refine ⟨by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_⟩ <;> split <;> simp_all

theorem aedge_joinE_ne {a b : InfoReg} (h : joinRegE a b ≠ {}) : a ≠ {} ∧ b ≠ {} := by
  unfold joinRegE at h
  split at h
  · rename_i e; subst e; exact ⟨h, h⟩
  · exact ⟨fun e => h (by rw [e, aedge_joinReg_empL]), fun e => h (by rw [e, aedge_joinReg_empR])⟩

/-- Every non-empty fact of `m` is at a key where `iq` has a non-empty
fact. -/
def KeysIn (m iq : AInfo) : Prop := ∀ r i, m r = some i → i = {} ∨ ∃ i', iq r = some i' ∧ i' ≠ {}

theorem aedge_keys_fold (g : AGen Map) (iq : AInfo) : ∀ (t : List Nat) (acc info : AInfo),
    t.foldlM (fun acc o1 => (g.info o1).map fun i1 => joinInfoA acc i1) acc = some info →
    (KeysIn acc iq ∨ ∃ q ∈ t, g.info q = some iq) → KeysIn info iq
  | [], acc, info, h, hh => by
    simp only [List.foldlM_nil] at h
    cases h
    rcases hh with hh | ⟨q, hq, _⟩
    · exact hh
    · cases hq
  | o1 :: t, acc, info, h, hh => by
    simp only [List.foldlM_cons] at h
    obtain ⟨acc', h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨i1, hi1, rfl⟩ := Option.map_eq_some_iff.mp h1
    apply aedge_keys_fold g iq t _ info h
    have side : ∀ (a b : AInfo), (∀ r x y, a r = some x → b r = some y → x ≠ {} → ∃ i', iq r = some i' ∧ i' ≠ {}) →
        KeysIn (joinInfoA a b) iq := by
      intro a b hab r i hr
      cases ha : a r with
      | none => simp [joinInfoA, ha] at hr
      | some x =>
        cases hb : b r with
        | none => simp [joinInfoA, ha, hb] at hr
        | some y =>
          simp only [joinInfoA, ha, hb, Option.some.injEq] at hr
          subst hr
          by_cases e : joinRegE x y = {}
          · exact Or.inl e
          · exact Or.inr (hab r x y ha hb (aedge_joinE_ne e).1)
    rcases hh with hh | ⟨q, hq, hiq⟩
    · refine Or.inl (side _ _ fun r x y hx _ hne => ?_)
      rcases hh r x hx with e | e
      · exact absurd e hne
      · exact e
    · rcases List.mem_cons.mp hq with rfl | hq
      · have e1 : i1 = iq := Option.some.inj (hi1.symm.trans hiq)
        refine Or.inl fun r i hr => ?_
        cases ha : acc r with
        | none => simp [joinInfoA, ha] at hr
        | some x =>
          cases hb : i1 r with
          | none => simp [joinInfoA, ha, hb] at hr
          | some y =>
            simp only [joinInfoA, ha, hb, Option.some.injEq] at hr
            subst hr
            by_cases e : joinRegE x y = {}
            · exact Or.inl e
            · exact Or.inr ⟨y, by rw [← e1]; exact hb, (aedge_joinE_ne e).2⟩
      · exact Or.inr ⟨q, hq, hiq⟩

/-- **The non-empty facts at the start** are at keys where the listed
predecessor `q` has non-empty facts, or at the register its end tests. -/
theorem ast_start_keys {g : AGen Map} {o q : Nat} {pre : List Nat} {info iq : AInfo} {pb : Blob}
    (h : aliasStart g o pre = some info) (hq : q ∈ pre) (hiq : g.info q = some iq)
    (hpb : HoonMap.get g.new q = some pb) :
    ∀ r i, info r = some i → i = {} ∨ (∃ i', iq r = some i' ∧ i' ≠ {}) ∨ r ∈ Path.finReads pb.fin := by
  cases pre with
  | nil => cases hq
  | cons p t =>
    simp only [aliasStart] at h
    obtain ⟨i0, hi0, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨info0, hf, h⟩ := Option.bind_eq_some_iff.mp h
    have hj : KeysIn info0 iq := aedge_keys_fold g iq t i0 info0 hf (by
      rcases List.mem_cons.mp hq with rfl | hq
      · rw [hiq] at hi0; cases hi0
        exact Or.inl fun r i hr => by
          by_cases e : i = {}
          · exact Or.inl e
          · exact Or.inr ⟨i, hr, e⟩
      · exact Or.inr ⟨q, hq, hiq⟩)
    have plain : ∀ r i, info0 r = some i → i = {} ∨ (∃ i', iq r = some i' ∧ i' ≠ {}) ∨ r ∈ Path.finReads pb.fin :=
      fun r i hr => (hj r i hr).elim Or.inl (fun e => Or.inr (Or.inl e))
    by_cases ht : t ≠ []
    · rw [if_pos ht] at h; cases h; exact plain
    have htn : t = [] := Classical.byContradiction ht
    subst htn
    have hqp : q = p := by simpa using hq
    subst hqp
    rw [if_neg (fun e => e rfl)] at h
    obtain ⟨pb', hpb', h⟩ := Option.bind_eq_some_iff.mp h
    rw [hpb] at hpb'; cases hpb'
    have jab : ∀ s (f : InfoReg → InfoReg) m', s ∈ Path.finReads pb.fin → jabA info0 s f = some m' →
        ∀ r i, m' r = some i → i = {} ∨ (∃ i', iq r = some i' ∧ i' ≠ {}) ∨ r ∈ Path.finReads pb.fin := by
      intro s f m' hs e r i hr
      obtain ⟨i0', _, rfl⟩ := as_jab e
      by_cases er : r = s
      · subst er; exact Or.inr (Or.inr hs)
      · rw [as_upd_other _ _ er] at hr; exact plain r i hr
    revert h
    cases hfin : pb.fin with
    | brn s z o' =>
      have hs : s ∈ Path.finReads pb.fin := by rw [hfin]; simp [Path.finReads]
      intro h
      rw [← hfin]
      simp only at h
      split at h
      · exact jab _ _ _ hs h
      · split at h
        · exact jab _ _ _ hs h
        · split at h
          · exact jab _ _ _ hs h
          · cases h
    | brz s z o' =>
      have hs : s ∈ Path.finReads pb.fin := by rw [hfin]; simp [Path.finReads]
      intro h
      rw [← hfin]
      simp only at h
      split at h
      · exact jab _ _ _ hs h
      · split at h
        · obtain ⟨si, -, h⟩ := Option.bind_eq_some_iff.mp h
          split at h
          · exact jab _ _ _ hs h
          · cases h; exact plain
        · cases h; exact plain
    | clq s z o' =>
      have hs : s ∈ Path.finReads pb.fin := by rw [hfin]; simp [Path.finReads]
      intro h
      rw [← hfin]
      simp only at h
      split at h
      · exact jab _ _ _ hs h
      · split at h
        · cases h; exact plain
        · cases h
    | hop => intro h; rw [← hfin]; cases h; exact plain
    | lti => intro h; rw [← hfin]; cases h; exact plain
    | eqq => intro h; rw [← hfin]; cases h; exact plain
    | jmp => intro h; rw [← hfin]; cases h; exact plain
    | jmf => intro h; rw [← hfin]; cases h; exact plain
    | jsp => intro h; rw [← hfin]; cases h; exact plain
    | jsf => intro h; rw [← hfin]; cases h; exact plain
    | don => intro h; rw [← hfin]; cases h; exact plain
    | bom => intro h; rw [← hfin]; cases h; exact plain

theorem aedge_filterMap_lt : ∀ {l : List (Option InfoReg)}, none ∈ l → (l.filterMap id).length < l.length
  | [], h => absurd h List.not_mem_nil
  | a :: l, h => by
    cases a with
    | none => simp only [List.filterMap_cons, id, List.length_cons]; exact Nat.lt_succ_of_le (List.length_filterMap_le _ _)
    | some a =>
      simp only [List.filterMap_cons, id, List.length_cons]
      have : none ∈ l := by simpa using h
      exact Nat.succ_lt_succ (aedge_filterMap_lt this)

/-- `param-info` names nothing when an edge passes `~`. -/
theorem aedge_param_none {ins : List (Option InfoReg)} (h : none ∈ ins) {x : Nat} : ¬ ANames (paramInfo ins) x := by
  intro hx
  unfold paramInfo at hx
  split at hx
  · exact ab_nm_empty hx
  · rename_i hd tl heq
    dsimp only at hx
    have hlt := aedge_filterMap_lt h
    rw [heq] at hlt
    have hne : ¬ ((hd :: tl).length = ins.length) := by omega
    rw [heq] at hx
    simp only [hne, if_false] at hx
    rcases hx with hx | hx | hx | hx | hx <;> simp at hx

/-- **The parameter loop keeps the names in `D`** when the facts of `q`'s
arguments name only registers of `D`; a key of the result is a key before or
a parameter. -/
theorem ast_pars_names {g : AGen Map} {q : Nat} {iq : AInfo} {D : Nat → Prop} (hiq : g.info q = some iq)
    (hD : ∀ r i y, iq r = some i → ANames i y → D y) :
    ∀ (ps : List Nat) (edges : List (Nat × List (Option Nat))) (loc loc0 : AInfo) (args : List (Option Nat)),
      aliasPars g ps edges loc = some loc0 → (q, args) ∈ edges →
      (∀ r i y, loc r = some i → ANames i y → D y) →
      (∀ r i y, loc0 r = some i → ANames i y → D y) ∧ (∀ r i, loc0 r = some i → loc r = some i ∨ r ∈ ps)
  | [], edges, loc, loc0, args, h, _, hl => by
    simp only [aliasPars, Option.some.injEq] at h
    subst h
    exact ⟨hl, fun r i hr => Or.inl hr⟩
  | x :: ps, edges, loc, loc0, args, h, he, hl => by
    simp only [aliasPars] at h
    obtain ⟨ins, hins, h⟩ := Option.bind_eq_some_iff.mp h
    have hx : ∀ y, ANames (paramInfo ins) y → D y := by
      intro y hy
      obtain ⟨w, hw, hwq⟩ := ast_mapM_mem hins he
      cases args with
      | nil => simp [aliasIn] at hwq
      | cons a0 rest =>
        cases a0 with
        | none =>
          simp only [aliasIn, Option.some.injEq] at hwq; subst hwq
          exact absurd hy (aedge_param_none hw)
        | some u =>
          simp only [aliasIn, hiq, Option.bind_some] at hwq
          obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hwq
          exact hD u a y ha (ast_param_names hw hy)
    obtain ⟨n1, n2⟩ := ast_pars_names hiq hD ps _ _ loc0 args.tail h
      (List.mem_map.mpr ⟨(q, args), he, rfl⟩) (fun r i y hr hy => by
        by_cases e : r = x
        · subst e; rw [as_upd_self] at hr; cases hr; exact hx y hy
        · rw [as_upd_other _ _ e] at hr; exact hl r i y hr hy)
    refine ⟨n1, fun r i hr => ?_⟩
    rcases n2 r i hr with hr | hr
    · by_cases e : r = x
      · subst e; exact Or.inr List.mem_cons_self
      · rw [as_upd_other _ _ e] at hr; exact Or.inl hr
    · exact Or.inr (List.mem_cons_of_mem _ hr)

/-- **`ABInv` at the start of a block from `ABInv` at the end of the
predecessor taken**: `Def` at `q`'s end and the parameters of `o` are in
`Def` at `o`, the registers `q`'s end reads are in `Def` at `q`'s end, a
register done at `o` is done at `q`'s end with the same `old` or is a
parameter that keeps its own name, and a register outside `Def` at `o` in `Cl`
keeps its own name in the global `old`. -/
theorem aedge_abinv {g : AGen Map} {o q : Nat} {b : Blob} {info : AInfo} {imms : AImms}
    {edges : List (Nat × List (Option Nat))} {loc0 : AInfo}
    (hst : aliasStart g o (g.rev o) = some info) (him : aliasStartImms g (g.rev o) = some imms)
    (hed : aliasEdges g o (g.rev o) = some edges) (hpa : aliasPars g b.par edges info = some loc0)
    (hq : q ∈ g.rev o) {lq : AInfo} {mq : AImms} {oq : Nat → Nat} (hlq : g.info q = some lq)
    (hmq : g.imms q = some mq) {pb : Blob} (hpb : HoonMap.get g.new q = some pb)
    {Defq Dq Defo Do Cl : Nat → Prop} (hi : ABInv ⟨oq, lq, mq⟩ Defq Dq Cl)
    {j : Jmp} (hj : j ∈ getJmps pb.fin) (hjo : j.there = o)
    (hDef : ∀ x, Defq x → Defo x) (hparD : ∀ x ∈ b.par, Defo x) (hfinD : ∀ x ∈ Path.finReads pb.fin, Defq x)
    (hDo : ∀ x, Do x → (Dq x ∧ g.old x = oq x) ∨ (x ∈ b.par ∧ g.old x = x))
    (hself : ∀ d, ¬ Defo d → Cl d → g.old d = d) :
    ABInv ⟨g.old, loc0, imms⟩ Defo Do Cl := by
  have he : (q, j.args) ∈ edges := aedge_mem hed hq hpb hj hjo
  have hN := ast_start_names hst hq hlq
  have hK := ast_start_keys hst hq hlq hpb
  obtain ⟨n1, n2⟩ := ast_pars_names (D := Defo) hlq (fun r i y hr hy => hDef y (hi.loc.1 r i y hr hy))
    b.par edges info loc0 j.args hpa he (fun r i y hr hy => by
      obtain ⟨i', hi', hy'⟩ := hN r i y hr hy
      exact hDef y (hi.loc.1 r i' y hi' hy'))
  refine ⟨fun n r hr => hDef r (hi.imm n r (ast_imms_sub him hq hmq n r hr)), ⟨n1, fun r i hr => ?_⟩,
    fun d hd => ?_, fun d hd => ?_, hself⟩
  · rcases n2 r i hr with hr | hr
    · rcases hK r i hr with e | ⟨i', hi', hne⟩ | hf
      · exact Or.inl e
      · rcases hi.loc.2 r i' hi' with e | e
        · exact absurd e hne
        · exact Or.inr (hDef r e)
      · exact Or.inr (hDef r (hfinD r hf))
    · exact Or.inr (hparD r hr)
  · rcases hDo d hd with ⟨hdq, ho⟩ | ⟨hp, ho⟩
    · simp only; rw [ho]; exact hDef _ (hi.old d hdq)
    · simp only; rw [ho]; exact hparD d hp
  · rcases hDo d hd with ⟨hdq, -⟩ | ⟨hp, -⟩
    · exact hDef d (hi.done d hdq)
    · exact hparD d hp

end Opt
end SkaModel
end Formalization
