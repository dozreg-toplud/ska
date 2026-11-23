import lemmas.Ska.AnaInv
import lemmas.Ska.FolNorm

/-!
# The bridge with answers judged at the end of the run

`Bridge.lean` puts a run of the state-passing `fol-loop` in `FolR P` for one
predicate `P` of answers, fixed before the run.  For convergence the answers
must be judged against the state at the end of the run: an answer read from
the entry of a function on the stack is right at the end because the entry
is the same then (the frame `Keep`), which is not a property of the state at
the time of the answer alone.  Here `P` is a family `Pf` over the `gen` of
the run that only grows along the run (`PLe`), and the run is in
`FolR (Pf gs')` for its last `gen` `gs'` (`bridge_stepD`, `folLoop_goOKD`,
`run_folTopRD`).  The constant family gives back `Bridge.lean`.
-/

namespace Formalization
namespace SkaModel

open Nock

/-- `FolR` is monotone in its answers. -/
theorem folR_monoP {P Q : Sock → Noun → TabEntry → Prop} (hPQ : ∀ s f a, P s f a → Q s f a) :
    ∀ (n : Nat) {fol : Noun} {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen gen' : Gen}
      {out : FolOut}, FolR P n fol sub mk bc df gen out gen' → FolR Q n fol sub mk bc df gen out gen'
  | 0, _, _, _, _, _, _, _, _, h => h.elim
  | n + 1, _, _, _, _, _, _, _, _, h => by
    obtain ⟨tab, go, g', ht, hgo, h, he⟩ := h
    exact ⟨tab, go, g', fun s f a e => hPQ _ _ _ (ht s f a e),
      fun _ _ _ _ _ _ _ _ e => folR_monoP hPQ n (hgo _ _ _ _ _ _ _ _ e), h, he⟩

namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- A family of answer predicates over the `gen` of a run. -/
abbrev PFam (M : Type → Type → Type) (R : Type) := GenS M R → Sock → Noun → TabEntry → Prop

/-- The answers of `Pf` at `g` are answers at `g'`. -/
def PLe (Pf : PFam M R) (g g' : GenS M R) : Prop := ∀ s f a, Pf g s f a → Pf g' s f a

theorem PLe.refl (Pf : PFam M R) (g : GenS M R) : PLe Pf g g := fun _ _ _ h => h

theorem PLe.trans {Pf : PFam M R} {g1 g2 g3 : GenS M R} (h1 : PLe Pf g1 g2) (h2 : PLe Pf g2 g3) :
    PLe Pf g1 g3 := fun s f a h => h2 s f a (h1 s f a h)

/-- Two `gen`s that agree on what `LocalStable` reads. -/
def LFEq (gs gs' : GenS M R) : Prop :=
  gs'.low = gs.low ∧ gs'.back = gs.back ∧ gs'.st.g = gs.st.g ∧ gs'.st.done = gs.st.done ∧
    gs'.st.order = gs.st.order ∧ gs'.st.stk = gs.st.stk ∧ gs'.st.next = gs.st.next ∧
    gs'.st.moved = gs.st.moved ∧ gs'.st.tick = gs.st.tick ∧ gs'.st.ticks = gs.st.ticks

/-- `Pf` reads only what `LocalStable` reads, and the callees, in which it
grows. -/
def PStable (Pf : PFam M R) : Prop :=
  ∀ gs gs' : GenS M R, LFEq gs gs' → (∀ c, Treap.has gs.callees c = true → Treap.has gs'.callees c = true) →
    PLe Pf gs gs'

theorem PStable.app {Pf : PFam M R} (hS : PStable Pf) {gs gs' : GenS M R}
    (h1 : gs'.low = gs.low) (h2 : gs'.back = gs.back) (h3 : gs'.st.g = gs.st.g)
    (h4 : gs'.st.done = gs.st.done) (h5 : gs'.st.order = gs.st.order) (h6 : gs'.st.stk = gs.st.stk)
    (h7 : gs'.st.next = gs.st.next) (h8 : gs'.st.moved = gs.st.moved) (h9 : gs'.st.tick = gs.st.tick)
    (h10 : gs'.st.ticks = gs.st.ticks) (hc : gs'.callees = gs.callees) : PLe Pf gs gs' :=
  hS gs gs' ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ (fun c h => by rw [hc]; exact h)

/-- `Inv` reads only what `LocalStable` reads, and the callees. -/
def LocalStableC (Inv : GenS M R → Prop) : Prop :=
  ∀ gs gs' : GenS M R, Inv gs → LFEq gs gs' → gs'.callees = gs.callees → Inv gs'

theorem LocalStableC.app {Inv : GenS M R → Prop} (hL : LocalStableC Inv) {gs gs' : GenS M R}
    (hi : Inv gs) (h1 : gs'.low = gs.low) (h2 : gs'.back = gs.back) (h3 : gs'.st.g = gs.st.g)
    (h4 : gs'.st.done = gs.st.done) (h5 : gs'.st.order = gs.st.order) (h6 : gs'.st.stk = gs.st.stk)
    (h7 : gs'.st.next = gs.st.next) (h8 : gs'.st.moved = gs.st.moved) (h9 : gs'.st.tick = gs.st.tick)
    (h10 : gs'.st.ticks = gs.st.ticks) (hc : gs'.callees = gs.callees) : Inv gs' :=
  hL gs gs' hi ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ hc

theorem LocalStable.toC {Inv : GenS M R → Prop} (hL : LocalStable Inv) : LocalStableC Inv :=
  fun gs gs' hi h _ => hL gs gs' hi h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
    h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2

/-- What the bridge needs of a subject sock: well formed, with a normal cape. -/
def SubOK (s : Sock) : Prop := WellFormed s ∧ NormSock s

/-- What the bridge asks of `resolve`: it keeps the capes of `gen`, its
answers only grow, and the `gen` that `fol-loop` makes after the call (the
result with the identity of the answer among its callees) has `Inv` and the
answer among its answers. -/
def ResOKD (Pf : PFam M R) (Inv : GenS M R → Prop) (res : ResGo M R) : Prop :=
  ∀ idT gs r gs', Inv gs → SubOK idT.1 → idT.1 ≠ Sock.void → res idT gs = some (r, gs') →
    gs'.gen = gs.gen ∧ PLe Pf gs gs' ∧
    ∀ (gs'' : GenS M R) seat, LFEq gs' gs'' → gs''.callees = Treap.ins gs'.callees ⟨seat, r.1⟩ →
      Inv gs'' ∧ Pf gs'' idT.1 idT.2 r.2.core.tab

/-- What the bridge gives of a recursion: `Inv` kept, answers that grow, and
results in `FolR` with the answers at the end. -/
def GoOKD (Pf : PFam M R) (Inv : GenS M R → Prop) (n : Nat) (go : FolGoS M R) : Prop :=
  ∀ fol sub seat mk bc df gs out gs', Inv gs → SubOK sub.sock → go fol sub seat mk bc df gs = some (out, gs') →
    Inv gs' ∧ PLe Pf gs gs' ∧ ∀ γ, FolR (Pf gs') n fol sub mk bc df (gs.at γ) out gs'.gen

section Step

variable {Pf : PFam M R} {Inv : GenS M R → Prop} {res : ResGo M R} {go : FolGoS M R} {n : Nat}

theorem GoOKD.ch (hgo : GoOKD Pf Inv n go) {fol : Noun} {sub : Anno} {seat mk : Option Noun} {bc df : Bool}
    {gs gs' : GenS M R} {out : FolOut} (hi : Inv gs) (hs : SubOK sub.sock)
    (h : go fol sub seat mk bc df gs = some (out, gs')) {g : GenS M R} (hle : PLe Pf gs' g)
    (γ γ' : Nat) : FolR (Pf g) n fol sub mk bc df (gs.at γ) out (gs'.at γ') :=
  folR_reghost (folR_monoP hle n ((hgo _ _ _ _ _ _ _ _ _ hi hs h).2.2 γ)) rfl

theorem GoOKD.le (hgo : GoOKD Pf Inv n go) {fol : Noun} {sub : Anno} {seat mk : Option Noun} {bc df : Bool}
    {gs gs' : GenS M R} {out : FolOut} (hi : Inv gs) (hs : SubOK sub.sock)
    (h : go fol sub seat mk bc df gs = some (out, gs')) : PLe Pf gs gs' :=
  (hgo _ _ _ _ _ _ _ _ _ hi hs h).2.1

theorem GoOKD.inv (hgo : GoOKD Pf Inv n go) {fol : Noun} {sub : Anno} {seat mk : Option Noun} {bc df : Bool}
    {gs gs' : GenS M R} {out : FolOut} (hi : Inv gs) (hs : SubOK sub.sock)
    (h : go fol sub seat mk bc df gs = some (out, gs')) : Inv gs' :=
  (hgo _ _ _ _ _ _ _ _ _ hi hs h).1

theorem GoOKD.wf (hP : ∀ g tab, TabIn (Pf g) tab → TabWF tab ∧ TabNorm tab) (hgo : GoOKD Pf Inv n go) {fol : Noun}
    {sub : Anno} {seat mk : Option Noun} {bc df : Bool}
    {gs gs' : GenS M R} {out : FolOut} (hi : Inv gs) (hs : SubOK sub.sock)
    (h : go fol sub seat mk bc df gs = some (out, gs')) : SubOK out.prod.sock :=
  ⟨folR_wf (fun t ht => (hP gs' t ht).1) n hs.1 ((hgo _ _ _ _ _ _ _ _ _ hi hs h).2.2 0),
   folR_norm (fun t ht => (hP gs' t ht).2) n hs.2 ((hgo _ _ _ _ _ _ _ _ _ hi hs h).2.2 0)⟩

theorem spotHint_invC {Inv : GenS M R → Prop} (hL : LocalStableC Inv) (env : Env R) (tag : Nat)
    (h1 h2 : Noun) (seat : Option Noun) {gen : GenS M R} (hi : Inv gen) :
    Inv (spotHint env tag h1 h2 seat gen).2 := by
  unfold spotHint
  split
  · split
    · exact hi
    · split
      · exact hL.app hi rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      · exact hi
  · exact hi

theorem spotHint_le {Pf : PFam M R} (hS : PStable Pf) (env : Env R) (tag : Nat)
    (h1 h2 : Noun) (seat : Option Noun) (gen : GenS M R) :
    PLe Pf gen (spotHint env tag h1 h2 seat gen).2 := by
  unfold spotHint
  split
  · split
    · exact PLe.refl _ _
    · split
      · exact hS.app rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      · exact PLe.refl _ _
  · exact PLe.refl _ _

theorem fastHint_le {Pf : PFam M R} {Inv : GenS M R → Prop} (hL : LocalStableC Inv) (hS : PStable Pf)
    {env : Env R} {tag : Nat} {h f : FolOut} {gen gen' : GenS M R} (hi : Inv gen)
    (e : fastHint env tag h f gen = some gen') :
    Inv gen' ∧ gen'.gen = gen.gen ∧ PLe Pf gen gen' := by
  unfold fastHint at e
  split at e
  · simp only [Option.map_eq_some_iff] at e
    obtain ⟨r, _, rfl⟩ := e
    split
    · exact ⟨hL.app hi rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, rfl,
        hS.app rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
    · exact ⟨hL.app hi rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, rfl,
        hS.app rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
  · cases e; exact ⟨hi, rfl, PLe.refl _ _⟩

/-- **One level of the state-passing `fol-loop` is in `FolR`, with the
answers at its end.** -/
theorem bridge_stepD (env : Env R) (hP : ∀ g tab, TabIn (Pf g) tab → TabWF tab ∧ TabNorm tab) (hL : LocalStableC Inv)
    (hS : PStable Pf) (hres : ResOKD Pf Inv res) (hgo : GoOKD Pf Inv n go)
    {fol : Noun} {sub : Anno} {seat mk : Option Noun} {bc df : Bool} {gs gs' : GenS M R} {out : FolOut}
    (hi : Inv gs) (hsub : SubOK sub.sock) (h : folStep env res go fol sub seat mk bc df gs = some (out, gs')) :
    Inv gs' ∧ PLe Pf gs gs' ∧ ∀ γ, FolR (Pf gs') (n + 1) fol sub mk bc df (gs.at γ) out gs'.gen := by
  cases hs : shape fol with
  | cons a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨l, g1⟩, h1, ⟨r, g2⟩, h2, rfl, rfl⟩ := h
    have i1 := hgo.inv hi hsub h1
    have l2 := hgo.le i1 hsub h2
    refine ⟨hgo.inv i1 hsub h2, (hgo.le hi hsub h1).trans l2, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (l, g1.at (γ + 1))),
        ((q, sub, mk, bc, df, g1.at (γ + 1)), (r, g2.at (γ + 2)))]) (g' := g2.at (γ + 2)) tabIn_none ?_ ?_ rfl
    · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hgo.ch hi hsub h1 l2 _ _, hgo.ch i1 hsub h2 (PLe.refl _ _) _ _⟩
    · simp only [SkaModel.folStep, hs]
      rw [goL_hd]; simp only [Option.bind_some]
      rw [goL_tl (by simp [GenS.at]), goL_hd]; rfl
  | op0 p =>
    simp only [folStep, hs, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨pr, hpr, rfl, rfl⟩ := h
    refine ⟨hi, PLe.refl _ _, fun γ => folR_of_calls (calls := []) (g' := gs.at γ) tabIn_none (by simp) ?_ rfl⟩
    simp only [SkaModel.folStep, hs, hpr, Option.map_some]
  | op1 p =>
    simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hi, PLe.refl _ _, fun γ => folR_of_calls (calls := []) (g' := gs.at γ) tabIn_none (by simp)
      (by simp only [SkaModel.folStep, hs]) rfl⟩
  | op2 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff] at h
    obtain ⟨⟨s1, g1⟩, h1, ⟨f1, g2⟩, h2, h3⟩ := h
    dsimp only at h2 h3
    have i1 := hgo.inv hi hsub h1
    have ws1 : SubOK s1.prod.sock := hgo.wf hP hi hsub h1
    have i2 := hgo.inv i1 hsub h2
    have l1 := hgo.le hi hsub h1
    have l2 := hgo.le i1 hsub h2
    have i2' : Inv ({ g2 with want := Ca.uni g2.want (distribute Cape.yes f1.prod.src) } : GenS M R) :=
      hL.app i2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have l2' : PLe Pf g2 ({ g2 with want := Ca.uni g2.want (distribute Cape.yes f1.prod.src) } : GenS M R) :=
      hS.app rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rcases callStep_cases h3 with ⟨el, eb, est, ec, hc⟩ | ⟨fa, fb, i, g3, h4, rfl, hc⟩ | ⟨fa, fb, r, g3, h4, hnv4, el, eb, est, ec, hc⟩
    · have l3 : PLe Pf g2 gs' := hS.app el eb (by rw [est]) (by rw [est]) (by rw [est]) (by rw [est])
        (by rw [est]) (by rw [est]) (by rw [est]) (by rw [est]) ec
      refine ⟨hL.app i2 el eb (by rw [est]) (by rw [est]) (by rw [est]) (by rw [est]) (by rw [est])
        (by rw [est]) (by rw [est]) (by rw [est]) ec, l1.trans (l2.trans l3), fun γ => ?_⟩
      refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (s1, g1.at (γ + 1))),
          ((q, sub, mk, bc, df, g1.at (γ + 1)), (f1, g2.at (γ + 2)))]) (g' := gs'.at (γ + 2)) tabIn_none ?_ ?_ rfl
      · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hgo.ch hi hsub h1 (l2.trans l3) _ _, hgo.ch i1 hsub h2 l3 _ _⟩
      · simp only [SkaModel.folStep, hs]
        rw [goL_hd]; simp only [Option.bind_some]
        rw [goL_tl (by simp [GenS.at]), goL_hd]; simp only [Option.bind_some]
        exact hc _ _ _
    · have i3 := hgo.inv i2' ws1 h4
      have l4 := hgo.le i2' ws1 h4
      refine ⟨i3, l1.trans (l2.trans (l2'.trans l4)), fun γ => ?_⟩
      refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (s1, g1.at (γ + 1))),
          ((q, sub, mk, bc, df, g1.at (γ + 1)), (f1, g2.at (γ + 2))),
          ((C fa fb, s1.prod, mk, bc, df,
            GenS.at ({ g2 with want := Ca.uni g2.want (distribute Cape.yes f1.prod.src) } : GenS M R) (γ + 2)),
            (i, gs'.at (γ + 3)))]) (g' := gs'.at (γ + 3)) tabIn_none ?_ ?_ rfl
      · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hgo.ch hi hsub h1 (l2.trans (l2'.trans l4)) _ _, hgo.ch i1 hsub h2 (l2'.trans l4) _ _,
          hgo.ch i2' ws1 h4 (PLe.refl _ _) _ _⟩
      · simp only [SkaModel.folStep, hs]
        rw [goL_hd]; simp only [Option.bind_some]
        rw [goL_tl (by simp [GenS.at]), goL_hd]; simp only [Option.bind_some]
        refine hc _ _ _ _ ?_
        rw [goL_tl (by simp [GenS.at]), goL_tl (by simp [GenS.at]), goL_hd]
    · obtain ⟨hg3, l3, hp⟩ := hres _ _ _ _ i2 ws1 hnv4 h4
      have hlf : LFEq g3 gs' := ⟨el, eb, by rw [est], by rw [est], by rw [est], by rw [est], by rw [est],
        by rw [est], by rw [est], by rw [est]⟩
      have l4 : PLe Pf g3 gs' := hS g3 gs' hlf (fun c h => by
        rw [ec]; exact (Treap.has_ins _ _ _).mpr (Or.inr h))
      obtain ⟨i3, hp'⟩ := hp gs' seat hlf ec
      refine ⟨i3, l1.trans (l2.trans (l3.trans l4)), fun γ => ?_⟩
      refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (s1, g1.at (γ + 1))),
          ((q, sub, mk, bc, df, g1.at (γ + 1)), (f1, g2.at (γ + 2)))]) (g' := gs'.at (γ + 2))
          (tabIn_one hp') ?_ ?_ rfl
      · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hgo.ch hi hsub h1 (l2.trans (l3.trans l4)) _ _, hgo.ch i1 hsub h2 (l3.trans l4) _ _⟩
      · simp only [SkaModel.folStep, hs]
        rw [goL_hd]; simp only [Option.bind_some]
        rw [goL_tl (by simp [GenS.at]), goL_hd]; simp only [Option.bind_some]
        exact hc hg3 _ _
  | op3 a b =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, rfl, rfl⟩ := h
    refine ⟨hgo.inv hi hsub h1, hgo.le hi hsub h1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (p1, g1.at (γ + 1)))])
      (g' := g1.at (γ + 1)) tabIn_none (by simpa using hgo.ch hi hsub h1 (PLe.refl _ _) _ _) ?_ rfl
    simp only [SkaModel.folStep, hs]
    rw [goL_hd]; rfl
  | op4 a b =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, rfl, rfl⟩ := h
    refine ⟨hgo.inv hi hsub h1, hgo.le hi hsub h1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (p1, g1.at (γ + 1)))])
      (g' := g1.at (γ + 1)) tabIn_none (by simpa using hgo.ch hi hsub h1 (PLe.refl _ _) _ _) ?_ rfl
    simp only [SkaModel.folStep, hs]
    rw [goL_hd]; rfl
  | op5 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    have i1 := hgo.inv hi hsub h1
    have l2 := hgo.le i1 hsub h2
    refine ⟨hgo.inv i1 hsub h2, (hgo.le hi hsub h1).trans l2, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (p1, g1.at (γ + 1))),
        ((q, sub, mk, bc, df, g1.at (γ + 1)), (q1, g2.at (γ + 2)))]) (g' := g2.at (γ + 2)) tabIn_none ?_ ?_ rfl
    · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hgo.ch hi hsub h1 l2 _ _, hgo.ch i1 hsub h2 (PLe.refl _ _) _ _⟩
    · simp only [SkaModel.folStep, hs]
      rw [goL_hd]; simp only [Option.bind_some]
      rw [goL_tl (by simp [GenS.at]), goL_hd]; rfl
  | op6 a b q r =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, ⟨r1, g3⟩, h3, rfl, rfl⟩ := h
    have i1 := hgo.inv hi hsub h1
    have i2 := hgo.inv i1 hsub h2
    have l2 := hgo.le i1 hsub h2
    have l3 := hgo.le i2 hsub h3
    refine ⟨hgo.inv i2 hsub h3, (hgo.le hi hsub h1).trans (l2.trans l3), fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (p1, g1.at (γ + 1))),
        ((q, sub, mk, bc, df, g1.at (γ + 1)), (q1, g2.at (γ + 2))),
        ((r, sub, mk, bc, df, g2.at (γ + 2)), (r1, g3.at (γ + 3)))]) (g' := g3.at (γ + 3)) tabIn_none ?_ ?_ rfl
    · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hgo.ch hi hsub h1 (l2.trans l3) _ _, hgo.ch i1 hsub h2 l3 _ _, hgo.ch i2 hsub h3 (PLe.refl _ _) _ _⟩
    · simp only [SkaModel.folStep, hs]
      rw [goL_hd]; simp only [Option.bind_some]
      rw [goL_tl (by simp [GenS.at]), goL_hd]; simp only [Option.bind_some]
      rw [goL_tl (by simp [GenS.at]), goL_tl (by simp [GenS.at]), goL_hd]; rfl
  | op7 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    have i1 := hgo.inv hi hsub h1
    have wp1 : SubOK p1.prod.sock := hgo.wf hP hi hsub h1
    have l2 := hgo.le i1 wp1 h2
    refine ⟨hgo.inv i1 wp1 h2, (hgo.le hi hsub h1).trans l2, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (p1, g1.at (γ + 1))),
        ((q, p1.prod, mk, bc, df, g1.at (γ + 1)), (q1, g2.at (γ + 2)))]) (g' := g2.at (γ + 2)) tabIn_none ?_ ?_ rfl
    · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hgo.ch hi hsub h1 l2 _ _, hgo.ch i1 wp1 h2 (PLe.refl _ _) _ _⟩
    · simp only [SkaModel.folStep, hs]
      rw [goL_hd]; simp only [Option.bind_some]
      rw [goL_tl (by simp [GenS.at]), goL_hd]; rfl
  | op8 a b q =>
    simp only [folStep, hs] at h
    refine ⟨hgo.inv hi hsub h, hgo.le hi hsub h, fun γ => ?_⟩
    refine folR_of_calls (calls := [((n3 (A 7) (C (C a b) (slot 1)) q, sub, mk, bc, df, gs.at γ),
        (out, gs'.at (γ + 1)))]) (g' := gs'.at (γ + 1)) tabIn_none
        (by simpa using hgo.ch hi hsub h (PLe.refl _ _) _ _) ?_ rfl
    simp only [SkaModel.folStep, hs]
    rw [goL_hd]
  | op9 p a b =>
    simp only [folStep, hs] at h
    refine ⟨hgo.inv hi hsub h, hgo.le hi hsub h, fun γ => ?_⟩
    refine folR_of_calls (calls := [((n3 (A 7) (C a b) (n3 (A 2) (slot 1) (slot p)), sub, mk, bc, df, gs.at γ),
        (out, gs'.at (γ + 1)))]) (g' := gs'.at (γ + 1)) tabIn_none
        (by simpa using hgo.ch hi hsub h (PLe.refl _ _) _ _) ?_ rfl
    simp only [SkaModel.folStep, hs]
    rw [goL_hd]
  | op10 ax don r1 r2 =>
    simp only [folStep, hs] at h
    split at h
    · rename_i hx
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨hi, PLe.refl _ _, fun γ => folR_of_calls (calls := []) (g' := gs.at γ) tabIn_none (by simp) ?_ rfl⟩
      simp only [SkaModel.folStep, hs, if_pos hx]
    · rename_i hx
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨dn, g1⟩, h1, ⟨rc, g2⟩, h2, s', hd, rfl, rfl⟩ := h
      have i1 := hgo.inv hi hsub h1
      have l2 := hgo.le i1 hsub h2
      refine ⟨hgo.inv i1 hsub h2, (hgo.le hi hsub h1).trans l2, fun γ => ?_⟩
      refine folR_of_calls (calls := [((don, sub, mk, bc, df, gs.at γ), (dn, g1.at (γ + 1))),
          ((C r1 r2, sub, mk, bc, df, g1.at (γ + 1)), (rc, g2.at (γ + 2)))]) (g' := g2.at (γ + 2))
          tabIn_none ?_ ?_ rfl
      · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hgo.ch hi hsub h1 l2 _ _, hgo.ch i1 hsub h2 (PLe.refl _ _) _ _⟩
      · simp only [SkaModel.folStep, hs, if_neg hx]
        rw [goL_hd]; simp only [Option.bind_some]
        rw [goL_tl (by simp [GenS.at]), goL_hd]; simp only [Option.bind_some, hd, Option.map_some]
  | op11s p a b =>
    simp only [folStep, hs] at h
    split at h
    · rename_i hp
      refine ⟨hgo.inv hi hsub h, hgo.le hi hsub h, fun γ => ?_⟩
      refine folR_of_calls (calls := [((n3 (A 2) (slot 1) (quote (C (A 11) (C (A p) (C a b)))), sub, mk, true,
          df, gs.at γ), (out, gs'.at (γ + 1)))]) (g' := gs'.at (γ + 1)) tabIn_none
          (by simpa using hgo.ch hi hsub h (PLe.refl _ _) _ _) ?_ rfl
      simp only [SkaModel.folStep, hs, if_pos hp]
      rw [goL_hd]
    · rename_i hp
      simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨q1, g1⟩, h1, rfl, rfl⟩ := h
      refine ⟨hgo.inv hi hsub h1, hgo.le hi hsub h1, fun γ => ?_⟩
      refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (q1, g1.at (γ + 1)))])
        (g' := g1.at (γ + 1)) tabIn_none (by simpa using hgo.ch hi hsub h1 (PLe.refl _ _) _ _) ?_ rfl
      simp only [SkaModel.folStep, hs, if_neg hp]
      rw [goL_hd]; rfl
  | op11d tag h1 h2 f =>
    simp only [folStep, hs, Option.bind_eq_some_iff] at h
    obtain ⟨⟨hh, g1⟩, e1, h⟩ := h
    have i0 := spotHint_invC hL env tag h1 h2 seat hi
    have l0 : PLe Pf gs (spotHint env tag h1 h2 seat gs).2 := spotHint_le hS env tag h1 h2 seat gs
    have hat0 : ∀ γ, (spotHint env tag h1 h2 seat gs).2.at γ = gs.at γ :=
      fun γ => GenS.at_eq (spotHint_gen env tag h1 h2 seat gs) γ
    have i1 := hgo.inv i0 hsub e1
    have l1 := hgo.le i0 hsub e1
    have whh : SubOK hh.prod.sock := hgo.wf hP i0 hsub e1
    have F1 : ∀ {g : GenS M R}, PLe Pf g1 g → ∀ γ γ', FolR (Pf g) n (C h1 h2) sub mk bc df (gs.at γ) hh (g1.at γ') :=
      fun hle γ γ' => by rw [← hat0 γ]; exact hgo.ch i0 hsub e1 hle _ _
    split at h
    · rename_i hc
      have l2 := hgo.le i1 hsub h
      refine ⟨hgo.inv i1 hsub h, l0.trans (l1.trans l2), fun γ => ?_⟩
      refine folR_of_calls (calls := [((C h1 h2, sub, mk, bc, df, gs.at γ), (hh, g1.at (γ + 1))),
          ((n3 (A 2) (slot 1) (quote f), sub, some hh.prod.sock.data, bc, df, g1.at (γ + 1)),
            (out, gs'.at (γ + 2)))]) (g' := gs'.at (γ + 2)) tabIn_none ?_ ?_ rfl
      · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨F1 l2 _ _, hgo.ch i1 hsub h (PLe.refl _ _) _ _⟩
      · simp only [SkaModel.folStep, hs]
        rw [goL_hd]; simp only [Option.bind_some]
        rw [if_pos hc, goL_tl (by simp [GenS.at]), goL_hd]
    · rename_i hc
      simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨arm, g2⟩, harm, ⟨fr, g3⟩, h3, g4, h4, rfl, rfl⟩ := h
      have iA : Inv g2 ∧ PLe Pf g1 g2 := by
        rcases meanArm_cases harm with ⟨rfl, _⟩ | ⟨cg, hcg, rfl, _⟩
        · exact ⟨i1, PLe.refl _ _⟩
        · exact ⟨hgo.inv i1 whh hcg, hgo.le i1 whh hcg⟩
      have l3 := hgo.le iA.1 hsub h3
      obtain ⟨i4, hg4, l4⟩ := fastHint_le hL hS (hgo.inv iA.1 hsub h3) h4
      refine ⟨i4, l0.trans (l1.trans (iA.2.trans (l3.trans l4))), fun γ => ?_⟩
      rcases meanArm_cases harm with ⟨rfl, hm⟩ | ⟨cg, hcg, rfl, hm⟩
      · refine folR_of_calls (calls := [((C h1 h2, sub, mk, bc, df, gs.at γ), (hh, g2.at (γ + 1))),
            ((f, sub, mk, bc, df, g2.at (γ + 1)), (fr, g3.at (γ + 2)))]) (g' := g3.at (γ + 2)) tabIn_none ?_ ?_
            (by rw [GenS.at_erase, hg4])
        · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
          exact ⟨F1 (l3.trans l4) _ _, hgo.ch i1 hsub h3 l4 _ _⟩
        · simp only [SkaModel.folStep, hs]
          rw [goL_hd]; simp only [Option.bind_some]
          rw [if_neg hc, hm]; simp only [Option.bind_some]
          rw [goL_tl (by simp [GenS.at]), goL_hd]; rfl
      · have icg := hgo.inv i1 whh hcg
        refine folR_of_calls (calls := [((C h1 h2, sub, mk, bc, df, gs.at γ), (hh, g1.at (γ + 1))),
            ((n3 (A 2) (slot 1) (slot 2), hh.prod, mk, bc, true, g1.at (γ + 1)), (cg.1, cg.2.at (γ + 2))),
            ((f, sub, mk, bc, df, cg.2.at (γ + 2)), (fr, g3.at (γ + 3)))]) (g' := g3.at (γ + 3)) tabIn_none ?_ ?_
            (by rw [GenS.at_erase, hg4])
        · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
          exact ⟨F1 (iA.2.trans (l3.trans l4)) _ _, hgo.ch i1 whh hcg (l3.trans l4) _ _,
            hgo.ch icg hsub h3 l4 _ _⟩
        · simp only [SkaModel.folStep, hs]
          rw [goL_hd]; simp only [Option.bind_some]
          rw [if_neg hc, hm _ _ _ (by rw [goL_tl (by simp [GenS.at]), goL_hd])]
          simp only [Option.bind_some]
          rw [goL_tl (by simp [GenS.at]), goL_tl (by simp [GenS.at]), goL_hd]; rfl
  | op12 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    have i1 := hgo.inv hi hsub h1
    have l2 := hgo.le i1 hsub h2
    refine ⟨hgo.inv i1 hsub h2, (hgo.le hi hsub h1).trans l2, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (p1, g1.at (γ + 1))),
        ((q, sub, mk, bc, df, g1.at (γ + 1)), (q1, g2.at (γ + 2)))]) (g' := g2.at (γ + 2)) tabIn_none ?_ ?_ rfl
    · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hgo.ch hi hsub h1 l2 _ _, hgo.ch i1 hsub h2 (PLe.refl _ _) _ _⟩
    · simp only [SkaModel.folStep, hs]
      rw [goL_hd]; simp only [Option.bind_some]
      rw [goL_tl (by simp [GenS.at]), goL_hd]; rfl
  | other =>
    simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hi, PLe.refl _ _, fun γ => folR_of_calls (calls := []) (g' := gs.at γ) tabIn_none (by simp)
      (by simp only [SkaModel.folStep, hs]) rfl⟩

end Step

/-- **The state-passing `fol-loop` is in `FolR`, with the answers at the end
of each call.** -/
theorem folLoop_goOKD {Pf : PFam M R} {Inv : GenS M R → Prop} (env : Env R) (memoF : Memo M)
    (hP : ∀ g tab, TabIn (Pf g) tab → TabWF tab ∧ TabNorm tab) (hL : LocalStableC Inv) (hS : PStable Pf) :
    ∀ n, (∀ k, k < n → ResOKD Pf Inv (resolve env memoF k)) → GoOKD Pf Inv n (folLoop env memoF n)
  | 0 => fun _ _ _ _ _ _ _ _ _ _ _ _ h => by rw [folLoop_zero] at h; cases h
  | n + 1 => fun hres _ _ _ _ _ _ _ _ _ hi hs h => by
    rw [folLoop_succ] at h
    exact bridge_stepD env hP hL hS (hres n (Nat.lt_succ_self n))
      (folLoop_goOKD env memoF hP hL hS n (fun k hk => hres k (Nat.lt_succ_of_lt hk))) hi hs h

/-- **The run of `+run` on `id` is a run with the answers of its last `gen`.** -/
theorem run_folTopRD {Pf : PFam M R} {Inv : GenS M R → Prop} (env : Env R) (memoF : Memo M)
    (hP : ∀ g tab, TabIn (Pf g) tab → TabWF tab ∧ TabNorm tab) (hL : LocalStableC Inv) (hS : PStable Pf) {n index : Nat}
    (hres : ∀ k, k < n → ResOKD Pf Inv (resolve env memoF k)) {id : Ident} {st : SkaState M R}
    {out : FolOut} {gs' : GenS M R} (hi : Inv (genInit index st)) (hw : SubOK id.1)
    (h : folLoop env memoF n id.2 ⟨id.1, A 1⟩ none none false false (genInit index st) = some (out, gs')) :
    Inv gs' ∧ PLe Pf (genInit index st) gs' ∧ FolTopR (Pf gs') n id.1 id.2 out gs'.gen := by
  obtain ⟨i', l', F⟩ := folLoop_goOKD env memoF hP hL hS n hres _ _ _ _ _ _ _ _ _ hi hw h
  exact ⟨i', l', F 0⟩

end Ana
end SkaModel
end Formalization
