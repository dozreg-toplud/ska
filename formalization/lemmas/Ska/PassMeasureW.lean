import lemmas.Ska.PassMeasureP

/-!
# The stack invariant of the pass loop (track F, Gaps 16)

`Ska/PassMeasureP.lean` proved that the pass loop of `+analyze` ends given
`RunStkW`: every `+run` of a stack member keeps `WInv` (every entry of the
graph and of the memo of the poke has a normal `indi`, and every stack
member's entry is `RunW`).  Here it is proved, for every fuel, by the skeleton
of `allPT` (`allPW`), and `passOn_wf` loses that hypothesis (`passOn_wf_W`).

* `fol-loop` keeps `indi` normal when its table's answers have a normal
  `indi` (`normCape_distribute`, `callStep_ni`, `folStep_ni`, `folR_ni`).
* The writes: a push writes the bunt entry at a subject that is tidy and not
  `%void` (`runW_bunt`, `push_w`); the subject socks given to `resolve` are not
  `%void` (the guard of `callStep`, carried by the bridge's `hAS`), and a `%he`
  turn keeps that (`msgSock_ne_void`); `+run` writes `runW_runDatum`
  (`runEnd_w`); a memo hit writes at an identity that is not on the stack
  (`hit_w`); `+pop` takes its members off the stack (`popGo_w`); `+cull` drops
  members (`cull_winv`).
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## 1. `indi` stays normal through `fol-loop` -/

theorem normCape_distribute : ∀ (s : Noun) (c : Cape), NormCape c → NormCape (distribute c s)
  | Noun.atom a, c, hc => by
    have key : ∀ x : Option Cape, (∀ y, x = some y → NormCape y) → NormCape (x.getD Cape.no) := by
      intro x hx
      cases x with
      | none => exact normCape_no
      | some y => exact hx y rfl
    unfold distribute
    split
    · exact normCape_no
    · split
      · exact normCape_no
      · rename_i hno
        apply key
        intro y hy
        unfold Ca.pat at hy
        repeat' split at hy
        all_goals first
          | (cases hy; done)
          | (cases hy; exact normCape_no)
          | (cases hy; exact (normCape_patLoop c hno hc _).1)
    · rename_i heq; cases heq
  | Noun.cell sh st, c, hc => by
    unfold distribute
    split
    · exact normCape_no
    · split
      · exact normCape_uni (normCape_distribute sh _ hc.hed) (normCape_distribute st _ hc.tel)
      · exact normCape_uni (normCape_distribute sh _ normCape_yes) (normCape_distribute st _ normCape_yes)

/-- The table's answers have a normal `indi`. -/
def TabNI (tab : Tab) : Prop := ∀ s f a, tab s f = some a → NormCape a.indi

/-- A recursion that keeps `indi` of `gen` normal. -/
def GoNI (go : FolGo) : Prop :=
  ∀ fol sub mk bc df gen out gen', NormCape gen.indi → go fol sub mk bc df gen = some (out, gen') →
    NormCape gen'.indi

theorem callStep_ni {tab : Tab} {go : FolGo} (htab : TabNI tab) (IH : GoNI go)
    {mk : Option Noun} {bc df : Bool} {s f out : FolOut} {gen gen' : Gen}
    (hg : NormCape gen.indi) (h : callStep tab go mk bc df s f gen = some (out, gen')) : NormCape gen'.indi := by
  unfold callStep at h
  by_cases hv : s.prod.sock = Sock.void ∨ f.prod.sock = Sock.void
  · rw [if_pos hv] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hg
  rw [if_neg hv] at h
  have dflt : ∀ (o : FolOut) (g : Gen), some (o, g) = some (out, gen') →
      g.indi = Ca.uni gen.indi (distribute Cape.yes f.prod.src) → NormCape gen'.indi := by
    intro o g e hgi
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    rw [hgi]; exact normCape_uni hg (normCape_distribute _ _ normCape_yes)
  cases hf : f.prod.sock with
  | void => exact absurd (Or.inr hf) hv
  | mk c d =>
  rw [hf] at h
  cases c with
  | no => exact dflt _ _ h rfl
  | cell _ _ => exact dflt _ _ h rfl
  | yes =>
  cases d with
  | atom _ => exact dflt _ _ h rfl
  | cell fa fb =>
  cases bc with
  | true => exact dflt _ _ h rfl
  | false =>
  simp only at h
  split at h
  · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨io, ig⟩, hi, rfl, rfl⟩ := h
    refine IH _ _ _ _ _ _ _ _ ?_ hi
    exact hg
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨dd, hd, h⟩ := h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact normCape_uni hg (normCape_distribute _ _ (htab _ _ _ hd))

theorem meanArm_ni {go : FolGo} (IH : GoNI go) {tag : Nat} {h : FolOut} {mk : Option Noun} {bc : Bool}
    {gen g : Gen} {arm : Option (Bell × Option Noun)} (hg : NormCape gen.indi)
    (e : meanArm go tag h mk bc gen = some (arm, g)) : NormCape g.indi := by
  unfold meanArm at e
  split at e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    exact hg
  · simp only [Option.bind_eq_some_iff] at e
    obtain ⟨bat, _, e⟩ := e
    split at e
    · simp only [Option.bind_eq_some_iff] at e
      obtain ⟨⟨co, cg⟩, hcg, e⟩ := e
      split at e
      · simp only [Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨_, rfl⟩ := e
        exact IH _ _ _ _ _ _ _ _ hg hcg
      · cases e
    · simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨_, rfl⟩ := e
      exact hg

/-- **One level of `fol-loop` keeps `GoNI`.** -/
theorem folStep_ni {tab : Tab} {go : FolGo} (htab : TabNI tab) (IH : GoNI go) :
    GoNI (folStep tab go) := by
  intro fol sub mk bc df gen out gen' hg h
  cases hs : shape fol with
  | cons a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨l, g1⟩, h1, ⟨r, g2⟩, h2, rfl, rfl⟩ := h
    exact IH _ _ _ _ _ _ _ _ (IH _ _ _ _ _ _ _ _ hg h1) h2
  | op0 p =>
    simp only [folStep, hs, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨pr, _, rfl, rfl⟩ := h
    exact hg
  | op1 p =>
    simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hg
  | op2 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff] at h
    obtain ⟨⟨s1, g1⟩, h1, ⟨f1, g2⟩, h2, h3⟩ := h
    exact callStep_ni htab IH (IH _ _ _ _ _ _ _ _ (IH _ _ _ _ _ _ _ _ hg h1) h2) h3
  | op3 a b =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, rfl, rfl⟩ := h
    exact IH _ _ _ _ _ _ _ _ hg h1
  | op4 a b =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, rfl, rfl⟩ := h
    exact IH _ _ _ _ _ _ _ _ hg h1
  | op5 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    exact IH _ _ _ _ _ _ _ _ (IH _ _ _ _ _ _ _ _ hg h1) h2
  | op6 a b q r =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, ⟨r1, g3⟩, h3, rfl, rfl⟩ := h
    exact IH _ _ _ _ _ _ _ _ (IH _ _ _ _ _ _ _ _ (IH _ _ _ _ _ _ _ _ hg h1) h2) h3
  | op7 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    exact IH _ _ _ _ _ _ _ _ (IH _ _ _ _ _ _ _ _ hg h1) h2
  | op8 a b q =>
    simp only [folStep, hs] at h
    exact IH _ _ _ _ _ _ _ _ hg h
  | op9 p a b =>
    simp only [folStep, hs] at h
    exact IH _ _ _ _ _ _ _ _ hg h
  | op10 ax don r1 r2 =>
    simp only [folStep, hs] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hg
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨dn, g1⟩, h1, ⟨rc, g2⟩, h2, s', _, rfl, rfl⟩ := h
      exact IH _ _ _ _ _ _ _ _ (IH _ _ _ _ _ _ _ _ hg h1) h2
  | op11s p a b =>
    simp only [folStep, hs] at h
    split at h
    · exact IH _ _ _ _ _ _ _ _ hg h
    · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨q1, g1⟩, h1, rfl, rfl⟩ := h
      exact IH _ _ _ _ _ _ _ _ hg h1
  | op11d tag h1 h2 f =>
    simp only [folStep, hs, Option.bind_eq_some_iff] at h
    obtain ⟨⟨hh, g1⟩, e1, h⟩ := h
    have n1 := IH _ _ _ _ _ _ _ _ hg e1
    split at h
    · exact IH _ _ _ _ _ _ _ _ n1 h
    · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨arm, ga⟩, harm, ⟨fr, g3⟩, h3, rfl, rfl⟩ := h
      exact IH _ _ _ _ _ _ _ _ (meanArm_ni IH n1 harm) h3
  | op11c x y h1 h2 f =>
    simp only [folStep, hs] at h
    exact IH _ _ _ _ _ _ _ _ hg h
  | op12 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    exact IH _ _ _ _ _ _ _ _ (IH _ _ _ _ _ _ _ _ hg h1) h2
  | other =>
    simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hg

/-- **A run with answers in `P` keeps `indi` normal**, when the answers of `P`
have a normal `indi`. -/
theorem folR_ni {P : Sock → Noun → TabEntry → Prop} (hP : ∀ tab, TabIn P tab → TabNI tab) :
    ∀ (n : Nat) {fol : Noun} {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen gen' : Gen}
      {out : FolOut}, NormCape gen.indi → FolR P n fol sub mk bc df gen out gen' → NormCape gen'.indi
  | 0, _, _, _, _, _, _, _, _, _, h => h.elim
  | n + 1, _, _, _, _, _, _, gen', _, hg, h => by
    obtain ⟨tab, go, g', ht, hgo, h, he⟩ := h
    have n1 := folStep_ni (hP tab ht)
      (fun _ _ _ _ _ _ _ _ hg' hg2 => folR_ni hP n hg' (hgo _ _ _ _ _ _ _ _ hg2)) _ _ _ _ _ _ _ _ hg h
    have e : g'.erase.indi = gen'.erase.indi := congrArg Gen.indi he
    have e2 : g'.indi = gen'.indi := e
    rw [← e2]; exact n1

/-- `+msg-sock` of a sock that is not `%void` is not `%void`. -/
theorem msgSock_ne_void' : ∀ (k : Nat) (a b m : Sock), nsize a.data < k → a ≠ Sock.void →
    msgSock a b = some m → m ≠ Sock.void := by
  intro k
  induction k with
  | zero => intro _ _ _ h; omega
  | succ k ih =>
  intro a b m hk ha hm
  unfold msgSock at hm
  split at hm
  · cases hm; exact ha
  · split at hm
    · exact absurd rfl ha
    · cases hm; exact ha
    · rename_i ah aT ad1 ad2 bh bT bd1 bd2 _
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hm
      obtain ⟨h, hh, t, ht, rfl⟩ := hm
      simp only [Sock.data, nsize] at hk
      have h1 := ih (Sock.mk ah ad1) _ _ (by simp only [Sock.data]; omega) (by simp) hh
      have h2 := ih (Sock.mk aT ad2) _ _ (by simp only [Sock.data]; omega) (by simp) ht
      cases h with
      | void => exact absurd rfl h1
      | mk c1 d1 =>
      cases t with
      | void => exact absurd rfl h2
      | mk c2 d2 =>
      unfold So.knit
      simp only
      split <;> simp [Sock.dunno]
    · cases hm
    · cases hm; simp [Sock.dunno]

theorem msgSock_ne_void {a b m : Sock} (ha : a ≠ Sock.void) (hm : msgSock a b = some m) : m ≠ Sock.void :=
  msgSock_ne_void' _ a b m (Nat.lt_succ_self _) ha hm

theorem graphNI_put {g : Graph} {i : Sock × Noun} {d : Datum} (hg : Ana.GraphNI g) (hd : NormCape d.indi) :
    Ana.GraphNI (g.put i d) := by
  intro j e hj
  unfold Graph.put at hj
  split at hj
  · cases hj; exact hd
  · exact hg j e hj

theorem graph_put_ne {g : Graph} {i j : Sock × Noun} {d e : Datum} (hne : j ≠ i) (h : g.put i d j = some e) :
    g j = some e := by
  unfold Graph.put at h
  rw [if_neg hne] at h
  exact h

theorem graph_put_eq {g : Graph} {i : Sock × Noun} {d e : Datum} (h : g.put i d i = some e) : e = d := by
  simp [Graph.put] at h; exact h.symm

namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## 2. The memo -/

theorem MemoNI.empty : MemoNI (Treap.empty : Memo M) := by
  intro f ms s e h; rw [Treap.get_empty] at h; cases h

theorem MemoNI.putMi {m : Memo M} (hm : MemoNI m) {i : Ident} {d : FDatum M}
    (hd : NormCape d.indi) : MemoNI (putMi m i d) := by
  intro f ms s e h1 h2
  unfold Ana.putMi at h1
  rw [Treap.get_put] at h1
  split at h1
  · cases h1
    rw [Treap.get_put] at h2
    split at h2
    · cases h2; exact hd
    · unfold gutMi Treap.gut at h2
      rename_i hf _
      subst hf
      cases e' : Treap.get m i.2 with
      | none => rw [e'] at h2; simp [Treap.get_empty] at h2
      | some ms' => rw [e'] at h2; exact hm _ _ _ _ e' h2
  · exact hm _ _ _ _ h1 h2

/-- A hit of `+git:mi` keeps the entry's `indi` (it patches only the product). -/
theorem gitMi_ni {m : Memo M} (hm : MemoNI m) {f : Noun} {s : Sock} {hit : Ident × FDatum M}
    (h : gitMi m f s = some (some hit)) : NormCape hit.2.indi := by
  obtain ⟨k, d0, hk, _, hd⟩ := gitLoop_hit (i := hit.1) (d := hit.2) h
  rw [hd]
  have hk' : Treap.get (gutMi m f) k = some (hit.1, d0) := (Treap.mem_tap _ _ _).mp hk
  have hg' : Treap.get m f = some (gutMi m f) ∨ gutMi m f = Treap.empty := by
    unfold gutMi Treap.gut
    cases e : Treap.get m f <;> simp
  rcases hg' with hg' | hg'
  · exact hm f _ k _ hg' hk'
  · rw [hg', Treap.get_empty] at hk'; cases hk'

/-! ## 3. The writes -/

theorem WInv.init (reg : R) : WInv (SkaState.init reg : SkaState M R) := by
  refine ⟨?_, MemoNI.empty, ?_⟩
  · intro i d h
    simp [gCore, SkaState.init, Treap.get_empty] at h
  · intro i hi
    simp [SkaState.init] at hi

theorem WInv.gitG_ni {st : SkaState M R} (h : WInv st) (i : Ident) : NormCape (gitG st.g i).indi := by
  unfold Ana.gitG Treap.gut
  cases e : Treap.get st.g i with
  | none => exact normCape_no
  | some d => exact h.g_ni i d.core (by simp [gCore, e])

theorem hit_w {memoF : Memo M} (hmN : MemoNI memoF) {st : SkaState M R} (hi : SInv st) (hw : WInv st)
    {id : Ident} {hit : Ident × FDatum M} (hg : Treap.get st.g id = none)
    (h : gitMi memoF id.2 id.1 = some (some hit)) :
    WInv { st with g := Treap.put st.g id hit.2, done := putMi st.done id hit.2 } := by
  have hn := gitMi_ni hmN h
  have hnm := hi.not_mem hg
  refine ⟨?_, hw.done_ni.putMi hn, ?_⟩
  · show GraphNI (gCore (Treap.put st.g id hit.2))
    rw [gCore_put]; exact graphNI_put hw.g_ni hn
  · intro i hi' d hd
    have hne : i ≠ id := fun e => hnm (e ▸ hi')
    have hd' : gCore (Treap.put st.g id hit.2) i = some d := hd
    rw [gCore_put] at hd'
    exact hw.stk i hi' d (graph_put_ne hne hd')

theorem push_w {st : SkaState M R} (hw : WInv st) {id : Ident} (htd : Tidy id.1) (hv : id.1 ≠ Sock.void)
    (index : Nat) :
    WInv { st with next := index + 1, order := Treap.put st.order id index, stk := id :: st.stk,
                   g := Treap.put st.g id FDatum.bunt } := by
  refine ⟨?_, hw.done_ni, ?_⟩
  · show GraphNI (gCore (Treap.put st.g id FDatum.bunt))
    rw [gCore_put, FDatum.bunt_core]; exact graphNI_put hw.g_ni normCape_no
  · intro i hi d hd
    have hd' : gCore (Treap.put st.g id FDatum.bunt) i = some d := hd
    rw [gCore_put, FDatum.bunt_core] at hd'
    by_cases e : i = id
    · subst e
      rw [graph_put_eq hd']
      exact runW_bunt htd hv
    · exact hw.stk i ((List.mem_cons.mp hi).resolve_left e) d (graph_put_ne e hd')

theorem popGo_w {id : Ident} : ∀ (l : List Ident) (st st' : SkaState M R), st.stk = l → l.Nodup →
    (∀ j ∈ l, ∃ d, Treap.get st.g j = some d) → WInv st → popGo id l st = some st' → WInv st'
  | [], _, _, _, _, _, _, h => by simp [popGo] at h
  | top :: rest, st, st', hs, hnd, hl, hw, h => by
    unfold popGo at h
    simp only at h
    obtain ⟨d0, hd0⟩ := hl top List.mem_cons_self
    have hgit : gitG st.g top = d0 := by simp [gitG, Treap.gut, hd0]
    simp only [hgit] at h
    have hn0 : NormCape d0.indi := hw.g_ni top d0.core (by simp [gCore, hd0])
    let d' : FDatum M := if d0.prod = Sock.void then { d0 with prod := Sock.dunno } else d0
    have hd' : NormCape d'.indi := by
      show NormCape (if d0.prod = Sock.void then { d0 with prod := Sock.dunno } else d0).indi
      split
      · exact hn0
      · exact hn0
    let st2 : SkaState M R :=
      { st with stk := rest, order := Treap.del st.order top, ticks := Treap.del st.ticks top,
                g := Treap.put st.g top d', done := putMi st.done top d' }
    have w2 : WInv st2 := by
      refine ⟨?_, hw.done_ni.putMi hd', ?_⟩
      · show GraphNI (gCore (Treap.put st.g top d'))
        rw [gCore_put]; exact graphNI_put hw.g_ni hd'
      · intro i hi d hd
        have hne : i ≠ top := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hi)
        have hd2 : gCore (Treap.put st.g top d') i = some d := hd
        rw [gCore_put] at hd2
        exact hw.stk i (by rw [hs]; exact List.mem_cons_of_mem _ hi) d (graph_put_ne hne hd2)
    have hl2 : ∀ j ∈ rest, ∃ d, Treap.get st2.g j = some d := by
      intro j hj
      show ∃ d, Treap.get (Treap.put st.g top d') j = some d
      rw [Treap.get_put]
      split
      · exact ⟨_, rfl⟩
      · exact hl j (List.mem_cons_of_mem _ hj)
    by_cases e : top = id
    · rw [if_pos e] at h
      cases h
      exact w2
    · rw [if_neg e] at h
      exact popGo_w rest st2 st' rfl (List.nodup_cons.mp hnd).2 hl2 w2 h

theorem pop_w {id : Ident} {st st' : SkaState M R} (hi : SInv st) (hw : WInv st) (h : pop id st = some st') :
    WInv st' :=
  popGo_w st.stk st st' rfl hi.nodup (fun _ hj => hi.mem_g hj) hw h

/-- **The write of `+run` keeps `WInv`**: the new entry of `id` is `RunW`
(`runW_runDatum`), for a tidy subject, an old `indi` and a run's `indi` that
are normal. -/
theorem runEnd_w {id : Ident} {data : FDatum M} {out : FolOut} {gs : GenS M R} (hw : WInv gs.st)
    (hb : Tidy id.1) (hin : NormCape data.indi) (hg : NormCape gs.gen.indi) :
    WInv (runEnd id data out gs).2 := by
  obtain ⟨_, hs, hd, _⟩ := runEnd_fields id data out gs
  have hR := runW_runDatum (Treap.has gs.st.moved id) out gs.gen data.core hb hin hg
  refine ⟨?_, by rw [hd]; exact hw.done_ni, ?_⟩
  · rw [runEnd_core]; exact graphNI_put hw.g_ni hR.2.1
  · intro i hi d hdd
    rw [runEnd_core] at hdd
    rw [hs] at hi
    by_cases e : i = id
    · subst e
      rw [graph_put_eq hdd]
      exact hR
    · exact hw.stk i hi d (graph_put_ne e hdd)

/-! ## 4. The arms, by induction on the fuel -/

/-- The answers of `resolve`: well formed, tidy, and with a normal `indi`. -/
def PWN : Sock → Noun → TabEntry → Prop := fun s f a => PWT s f a ∧ NormCape a.indi

theorem pwn_wf : ∀ tab, TabIn PWN tab → TabWF tab := fun _ ht s f a hs h => (ht s f a h).1.1 hs

theorem pwn_tp : ∀ tab, TabIn PWN tab → TabTP tab := fun _ ht s f a hs h => (ht s f a h).1.2 hs

theorem pwn_ni : ∀ tab, TabIn PWN tab → TabNI tab := fun _ ht s f a h => (ht s f a h).2

/-- The subject socks `resolve` is asked at: well formed, tidy, not `%void`. -/
def QSW : Sock → Prop := fun s => QST s ∧ s ≠ Sock.void

theorem qASW : ∀ a, QAT a → a.sock ≠ Sock.void → QSW a.sock := fun a h hv => ⟨qAS a h hv, hv⟩

theorem qpresW : QPres QAT PWN := fun n _ _ _ _ _ _ _ _ hs h =>
  ⟨folR_wf pwn_wf n hs.1 h, folR_tp pwn_tp n hs.2 h⟩

/-- What the `resolve` loop keeps. -/
def ResPW (res : ResGo M R) : Prop :=
  ∀ idT gs r gs', SInv gs.st → TInv gs.st → WInv gs.st → WellFormed idT.1 → Tidy idT.1 →
    idT.1 ≠ Sock.void → res idT gs = some (r, gs') → WInv gs'.st ∧ NormCape r.2.indi

/-- What `+analyze` keeps. -/
def AnaPW (ana : AnaGo M R) : Prop :=
  ∀ id st low st', SInv st → TInv st → WInv st → WellFormed id.1 → Tidy id.1 → id.1 ≠ Sock.void →
    Treap.get st.g id = none → ana id st = some (low, st') → WInv st'

/-- What the member loop keeps. -/
def MemPW (mem : MemGo M R) : Prop :=
  ∀ index pass ms st r st', SInv st → TInv st → WInv st → mem index pass ms st = some (r, st') → WInv st'

/-- What the pass loop keeps. -/
def PassPW (pass : PassGo M R) : Prop :=
  ∀ id index p st low st' (ab0 rest : List Ident), SInv st → TInv st → WInv st →
    st.stk = ab0 ++ id :: rest → pass id index p st = some (low, st') → WInv st'

/-- The invariant of a run of `fol-loop` begun in `st0`. -/
def RInvW (st0 : SkaState M R) (gs : GenS M R) : Prop := RInvT st0 gs ∧ WInv gs.st

theorem rInvW_stable (st0 : SkaState M R) : LocalStable (RInvW (M := M) st0) := by
  intro gs gs' h a b e1 e2 e3 e4 c d f g'
  exact ⟨rInvT_stable st0 gs gs' h.1 a b e1 e2 e3 e4 c d f g', h.2.congr e1 e2 e4⟩

theorem resOKQW_of {res : ResGo M R} (h : ResP res) (hT : ResPTop res) (hW : ResPW res)
    (st0 : SkaState M R) : ResOKQ QSW PWN (RInvW st0) res := by
  intro idT gs r gs' hi hw e
  obtain ⟨⟨⟨i1, s1, k1⟩, t1⟩, w1⟩ := hi
  obtain ⟨i2, s2, k2, g2, w2⟩ := h idT gs r gs' i1 hw.1.1 e
  obtain ⟨t2, p2⟩ := hT idT gs r gs' i1 t1 hw.1.1 hw.1.2 e
  obtain ⟨w3, n3⟩ := hW idT gs r gs' i1 t1 w1 hw.1.1 hw.1.2 hw.2 e
  refine ⟨⟨⟨fun _ => w2, fun _ => p2⟩, n3⟩,
    ⟨⟨⟨i2, gStepsR_trans s1 s2, k1.trans (k2.weaken k1.1 (fun j hj => ?_))⟩, t2⟩, w3⟩, g2⟩
  obtain ⟨l, el⟩ := k1.1
  rw [el]; exact List.mem_append_right _ hj

theorem resolveStep_w (env : Env R) {orig : Ident} {resolve : ResGo M R} {analyze : AnaGo M R}
    (hres : ResPW resolve) (hana : AnaPW analyze) : ResPW (resolveStep env resolve analyze orig) := by
  intro idT gs r gs' hi ht hw hwf htd hv e
  unfold resolveStep at e
  cases hg : Treap.get gs.st.g idT with
  | some d =>
    simp only [hg] at e
    have hn : NormCape d.indi := hw.g_ni idT d.core (by simp [gCore, hg])
    cases ho : Treap.get gs.st.order idT with
    | none =>
      simp only [ho, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨hw, hn⟩
    | some o =>
      simp only [ho, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨hw, hn⟩
  | none =>
    rw [hg] at e
    simp only at e
    split at e
    · cases e
    · rename_i m hm
      cases e
      exact ⟨hw, gitMi_ni hw.done_ni hm⟩
    · split at e
      · cases e
      · rename_i i hrc
        obtain ⟨hwi, hti, hvi⟩ : WellFormed i.1 ∧ Tidy i.1 ∧ i.1 ≠ Sock.void := by
          rcases recursiveCall_cases hrc with ⟨hb, _⟩ | ⟨_, j, hj, hm, _⟩
          · cases hb
          · exact ⟨wf_msgSock hwf (hi.wf_stk hj) hm, tidy_msgSock htd (ht.stk hi hj) hm,
              msgSock_ne_void hv hm⟩
        exact hres i gs r gs' hi ht hw hwi hti hvi e
      · rename_i i hrc
        simp only [Option.map_eq_some_iff] at e
        obtain ⟨o, _, e⟩ := e
        cases e
        exact ⟨hw, hw.gitG_ni i⟩
      · simp only [Option.map_eq_some_iff] at e
        obtain ⟨⟨low, st'⟩, ha, e⟩ := e
        cases e
        have w' := hana idT gs.st low st' hi ht hw hwf htd hv hg ha
        exact ⟨w', w'.gitG_ni idT⟩

theorem runStep_w (env : Env R) (memoF : Memo M) {n : Nat}
    (hres : ∀ k, k < n → ResP (resolveR env memoF k)) (hresT : ∀ k, k < n → ResPTop (resolveR env memoF k))
    (hresW : ∀ k, k < n → ResPW (resolveR env memoF k)) : RunStkW (runStep (folLoop env memoF n)) := by
  intro id index st r st' hi ht hw hid e
  unfold runStep at e
  simp only [Option.map_eq_some_iff] at e
  obtain ⟨⟨out, gs⟩, hf, e⟩ := e
  cases e
  let st0 : SkaState M R := { st with stats := { st.stats with runs := st.stats.runs + 1 } }
  have i0 : SInv st0 := hi.congr rfl rfl rfl rfl
  have r0 : RInvW st0 (genInit index st0) :=
    ⟨⟨⟨i0, GStepsR.refl _, Keep.refl' _ rfl rfl rfl⟩, ht.congr rfl rfl⟩, hw.congr rfl rfl rfl⟩
  obtain ⟨d0, hd0⟩ := hi.mem_g hid
  have hti := (ht.mem hd0).1
  obtain ⟨⟨_, w1⟩, hF⟩ := run_folTopRQ env memoF qASW qpresW (rInvW_stable st0)
    (fun k hk => resOKQW_of (hres k hk) (hresT k hk) (hresW k hk) st0) r0 ⟨hi.wf_stk hid, hti, trivial⟩ hf
  have hng : NormCape gs.gen.indi := folR_ni pwn_ni n (gen := Gen.init) normCape_no hF
  exact runEnd_w w1 hti (hw.gitG_ni id) hng

theorem member_tailW {run : RunGo M R} {mem : MemGo M R} (hrun : RunP run) (hrunT : RunPT run)
    (hrunW : RunStkW run) (hmemW : MemPW mem) {index pass : Nat} {m : Ident} {ms : List Ident}
    {st st1 st' : SkaState M R} {r : Nat × Bool} (hi : SInv st) (ht : TInv st) (hw : WInv st)
    (h1 : st1.g = st.g) (h2 : st1.done = st.done) (h3 : st1.order = st.order) (h4 : st1.stk = st.stk)
    (e : ((Treap.get st.order m).bind fun o => (run m o st1).bind fun r =>
      if r.1.1 < index then some ((r.1.1, r.1.2.2), r.2) else
      (mem index pass ms r.2).map fun t => ((min r.1.1 t.1.1, r.1.2.2 || t.1.2), t.2)) = some (r, st')) :
    WInv st' := by
  simp only [Option.bind_eq_some_iff] at e
  obtain ⟨o, ho, ⟨r1, st2⟩, hr, e⟩ := e
  have i1 : SInv st1 := hi.congr h1 h2 h3 h4
  have t1 : TInv st1 := ht.congr h1 h2
  have w1 : WInv st1 := hw.congr h1 h2 h4
  have hm1 : m ∈ st1.stk := (i1.ord_stk m).mp ⟨o, by rw [h3]; exact ho⟩
  have w2 := hrunW m o st1 r1 st2 i1 t1 w1 hm1 hr
  split at e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    exact w2
  · simp only [Option.map_eq_some_iff] at e
    obtain ⟨⟨t1', st3⟩, ht', e⟩ := e
    cases e
    exact hmemW index pass ms st2 t1' st3 (hrun m o st1 r1 st2 i1 hm1 hr).1
      (hrunT m o st1 r1 st2 i1 t1 hm1 hr) w2 ht'

theorem memberStep_w {run : RunGo M R} {mem : MemGo M R} (hrun : RunP run) (hrunT : RunPT run)
    (hrunW : RunStkW run) (hmemW : MemPW mem) : MemPW (memberStep run mem) := by
  intro index pass ms st r st' hi ht hw e
  cases ms with
  | nil =>
    simp only [memberStep, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    exact hw
  | cons m ms =>
    simp only [memberStep] at e
    split at e
    · exact hmemW index pass ms st r st' hi ht hw e
    · by_cases hp : pass > 1
      · simp only [hp, if_true] at e
        exact member_tailW (st1 := { st with stats := { st.stats with lateRuns := st.stats.lateRuns + 1 } })
          hrun hrunT hrunW hmemW hi ht hw rfl rfl rfl rfl e
      · simp only [hp, if_false] at e
        exact member_tailW (st1 := st) hrun hrunT hrunW hmemW hi ht hw rfl rfl rfl rfl e

theorem passStep_w {n : Nat} {mem : MemGo M R} {pass : PassGo M R} (hmem : MemP mem) (hmemT : MemPT mem)
    (hmemW : MemPW mem) (hpassW : PassPW pass) : PassPW (passStep n mem pass) := by
  intro id index p st low st' ab0 rest hi ht hw hs e
  unfold passStep at e
  simp only [Option.bind_eq_some_iff] at e
  obtain ⟨ab, hab, members, hsw, e⟩ := e
  obtain ⟨ab0', rest', rfl, hs', _⟩ := above_eq hab
  obtain ⟨rfl, rfl⟩ := nodup_split_unique (hs ▸ hi.nodup) (hs.symm.trans hs')
  have hnd2 : ((ab0 ++ [id]) ++ rest).Nodup := by simpa using (hs ▸ hi.nodup)
  have hms : ∀ m ∈ members, ¬ (m ∈ rest) := by
    intro m hm hr
    have hm' : m ∈ ab0 ++ [id] := by
      rcases sweep_mem hsw m hm with rfl | h
      · simp
      · exact (Treap.has_silt _ _).mp h
    exact (List.nodup_append.mp hnd2).2.2 m hm' m hr rfl
  obtain ⟨⟨r1, st2⟩, hm, e⟩ := e
  have i1 : SInv ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R) :=
    hi.congr rfl rfl rfl rfl
  have t1 : TInv ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R) :=
    ht.congr rfl rfl
  have w1 : WInv ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R) :=
    hw.congr rfl rfl rfl
  obtain ⟨i2, _, k2⟩ := hmem index p members _ r1 st2 (id :: rest) (· ∈ rest) i1 ⟨ab0, hs⟩
    (fun j hj => List.mem_cons_of_mem _ hj) hms hm
  have t2 := hmemT index p members _ r1 st2 i1 t1 hm
  have w2 := hmemW index p members _ r1 st2 i1 t1 w1 hm
  have K2 : Keep (id :: rest) (· ∈ rest) st st2 := k2
  simp only at e
  split at e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    exact w2
  · simp only [Option.bind_eq_some_iff] at e
    obtain ⟨st3, hc, e⟩ := e
    obtain ⟨l2, el2⟩ := K2.1
    obtain ⟨i3, _, k3⟩ := cull_ok i2 hc el2
    have t3 := cull_tp t2 hc
    have w3 := cull_winv w2 hc
    have K3 : Keep (id :: rest) (· ∈ rest) st st3 := K2.trans (k3.mono (fun j hj => List.mem_cons_of_mem _ hj))
    obtain ⟨l3, el3⟩ := K3.1
    split at e
    · simp only [Option.map_eq_some_iff] at e
      obtain ⟨st4, hp, e⟩ := e
      cases e
      exact pop_w i3 w3 hp
    · exact hpassW id index (p + 1) st3 low st' l3 rest i3 t3 w3 el3 e

theorem cullPass_w {n : Nat} {pass : PassGo M R} (hpassW : PassPW pass) {id : Ident} {index : Nat}
    {st st' : SkaState M R} {low : Nat} {ab0 rest : List Ident} (hi : SInv st) (ht : TInv st) (hw : WInv st)
    (hs : st.stk = ab0 ++ id :: rest) (h : cullPass n pass id index st = some (low, st')) : WInv st' := by
  unfold cullPass at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨st1, hc, h⟩ := h
  obtain ⟨i1, _, k1⟩ := cull_ok hi hc hs
  obtain ⟨l1, el1⟩ := k1.1
  exact hpassW id index 1 st1 low st' l1 rest i1 (cull_tp ht hc) (cull_winv hw hc) el1 h

theorem analyzeStep_w {n : Nat} {memoF : Memo M} (hmN : MemoNI memoF) {run : RunGo M R}
    {pass : PassGo M R} (hrun : RunP run) (hrunT : RunPT run) (hrunW : RunStkW run) (hpassW : PassPW pass) :
    AnaPW (analyzeStep n memoF run pass) := by
  intro id st low st' hi ht hw hwf htd hv hg e
  unfold analyzeStep at e
  split at e
  · cases e
  · rename_i hit hh
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    exact hit_w hmN hi hw hg hh
  · obtain ⟨i1, _, _⟩ := push_ok hi hwf hg st.next
    have t1 := push_tp ht htd st.next
    have w1 := push_w hw htd hv st.next
    simp only [Option.bind_eq_some_iff] at e
    obtain ⟨⟨r1, st2⟩, hr, e⟩ := e
    obtain ⟨i2, _, k2⟩ := hrun id st.next _ _ st2 i1 List.mem_cons_self hr
    have t2 := hrunT id st.next _ _ st2 i1 t1 List.mem_cons_self hr
    have w2 := hrunW id st.next _ _ st2 i1 t1 w1 List.mem_cons_self hr
    obtain ⟨l2, el2⟩ := k2.1
    have el2' : st2.stk = l2 ++ id :: st.stk := el2
    simp only at e
    split at e
    · simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨_, rfl⟩ := e
      exact w2
    · split at e
      · exact cullPass_w hpassW i2 t2 w2 el2' e
      · simp only [Option.bind_eq_some_iff] at e
        obtain ⟨ab, _, e⟩ := e
        split at e
        · exact cullPass_w hpassW i2 t2 w2 el2' e
        · simp only [Option.map_eq_some_iff] at e
          obtain ⟨st3, hp, e⟩ := e
          cases e
          exact pop_w i2 w2 hp

/-- The arms at the fuel `n` keep `WInv`. -/
def AllPW (env : Env R) (memoF : Memo M) (n : Nat) : Prop :=
  (∀ orig, ResPW (resolve env memoF n orig)) ∧ AnaPW (analyze env memoF n) ∧ RunStkW (run env memoF n) ∧
    PassPW (passLoop env memoF n) ∧ MemPW (memberLoop env memoF n)

theorem allPW_zero (env : Env R) (memoF : Memo M) : AllPW env memoF 0 := by
  refine ⟨fun _ _ _ _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ _ _ _ _ h => ?_,
    fun _ _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ _ _ h => ?_⟩
  · rw [resolve_zero] at h; cases h
  · rw [analyze_zero] at h; cases h
  · rw [run_zero] at h; cases h
  · rw [passLoop_zero] at h; cases h
  · rw [memberLoop_zero] at h; cases h

/-- **Every arm of the analysis keeps `WInv`** at every fuel, for a persistent
memo with well-formed and tidy entries whose `indi` is normal. -/
theorem allPW (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF) (hmN : MemoNI memoF) :
    ∀ n, ∀ k, k ≤ n → AllPW env memoF k
  | 0 => fun k hk => by rw [Nat.le_zero.mp hk]; exact allPW_zero env memoF
  | n + 1 => fun k hk => by
    rcases Nat.lt_or_ge k (n + 1) with hl | hl
    · exact allPW env memoF hmF hmT hmN n k (Nat.le_of_lt_succ hl)
    · have e : k = n + 1 := Nat.le_antisymm hk hl
      subst e
      obtain ⟨r, a, u, p, m⟩ := allPW env memoF hmF hmT hmN n n (Nat.le_refl n)
      obtain ⟨_, _, u0, _, m0⟩ := allP env memoF hmF n n (Nat.le_refl n)
      obtain ⟨_, _, uT, _, mT⟩ := allPT env memoF hmF hmT n n (Nat.le_refl n)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro orig; rw [resolve_succ]; exact resolveStep_w env (r orig) a
      · rw [analyze_succ]; exact analyzeStep_w hmN u0 uT u p
      · rw [run_succ]
        exact runStep_w env memoF
          (fun k hk => resP_of_loop (resl := resolve env memoF k) (allP env memoF hmF n k (Nat.le_of_lt hk)).1)
          (fun k hk => resPTop_of_loop (resl := resolve env memoF k) (allPT env memoF hmF hmT n k (Nat.le_of_lt hk)).1)
          (fun k hk idT gs r' gs' => (allPW env memoF hmF hmT hmN n k (Nat.le_of_lt hk)).1 idT idT gs r' gs')
      · rw [passLoop_succ]; exact passStep_w m0 mT m p
      · rw [memberLoop_succ]; exact memberStep_w u0 uT u m

/-- **`RunStkW` holds at every fuel**: the named hypothesis of `passOn_wf`. -/
theorem run_winv (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNI memoF) (k : Nat) : RunStkW (run env memoF k) :=
  (allPW env memoF hmF hmT hmN k k (Nat.le_refl k)).2.2.1

/-- **The pass loop of `+analyze` ends**, with only the bound `B` on `next`
named: there is no infinite sequence of passes of a component that go on,
from a state with `SInv`, `TInv` and `WInv`, for a persistent memo with
well-formed and tidy entries whose `indi` is normal. -/
theorem passOn_wf_W (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNI memoF) (n : Nat) (id : Ident) (index p B : Nat)
    (f : Nat → SkaState M R) (h0i : SInv (f 0)) (h0t : TInv (f 0)) (h0w : WInv (f 0))
    (hon : ∀ k, PassOn env memoF n id index (p + k) (f k) (f (k + 1)))
    (hB : ∀ k, (f k).next ≤ B) : False :=
  passOn_wf env memoF hmF hmT (run_winv env memoF hmF hmT hmN) n id index p B f h0i h0t h0w hon hB

/-- **`+ska-callgraph` keeps `WInv`**: from a root whose subject sock is well
formed, tidy and not `%void`. -/
theorem skaCallgraph_w (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNI memoF) {n : Nat} {root : Ident} {reg : R} {low : Nat} {st : SkaState M R}
    (hw : WellFormed root.1) (htd : Tidy root.1) (hv : root.1 ≠ Sock.void)
    (h : analyze env memoF n root (SkaState.init reg) = some (low, st)) : WInv st :=
  (allPW env memoF hmF hmT hmN n n (Nat.le_refl n)).2.1 root (SkaState.init reg) low st
    (SInv.init reg) (TInv.init reg) (WInv.init reg) hw htd hv (by simp [SkaState.init, Treap.get_empty]) h

end Ana

end SkaModel
end Formalization
