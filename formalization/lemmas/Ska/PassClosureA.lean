import lemmas.Ska.PassClosureF

/-!
# The closure invariant, part 4: the arm invariant and `hok` (track F, Gaps 16)

**`ClInv G st`**: every product in the graph and in the memo of the poke has
good `&` regions (`SockG G`), and every identity in `order` and on the stack
has its formula in `G` and a subject sock, not `%void`, with good regions
(`KeyG G`).  **`allCl`**: every arm keeps it at every fuel, from a persistent
memo `memoF` whose products have good regions (`MemoG G memoF`), for `G`
closed under halves and saf values.  The skeleton is the one of `allS`; the
runs use `folLoop_G` with `Inv := ClInv G ·.st`, and `resolve` answers:

* from the graph or the memo of the poke: a good product, or `+patch-prod`
  of one at the good subject sock (`gitMi_G`);
* `%he`: the next identity is `+msg-sock` of the subject and a stack member
  (`sockG_msgSock`, `msgSock_ne_void`), with the same formula;
* `%rec`: `+patch-prod` with the good `orig` (`sockG_patchProd`);
* a new function: `+analyze` pushes the good identity.

**`hok_of_clInv`**: with `G = NGood As B`, every stack member along the
chains of one pass loop is `OkId (nounsUpTo As B) (leafList As B)`
(`okId_of_good`, tidy from `ChainInv`).  **`passLoop_returns_wc`**:
`passLoop_returns_ws` with `hok` discharged.
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

variable {M : Type → Type → Type} [Treap M] {R : Type}

section Arm

variable {G : Noun → Prop}

/-! ## 1. The invariant -/

/-- Every product of the memo has good regions. -/
def MemoG (G : Noun → Prop) (m : Memo M) : Prop :=
  ∀ f ms s e, Treap.get m f = some ms → Treap.get ms s = some e → SockG G e.2.prod

theorem MemoG.putMi {m : Memo M} (hm : MemoG G m) {i : Ident} {d : FDatum M} (hd : SockG G d.prod) :
    MemoG G (putMi m i d) := by
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

/-- **A hit of `+git:mi` at a subject sock with good regions has a good
product** (`+patch-prod`). -/
theorem gitMi_G (hG : SubC G) {m : Memo M} (hm : MemoG G m) {f : Noun} {s : Sock} {hit : Ident × FDatum M}
    (hs : SockG G s) (h : gitMi m f s = some (some hit)) : SockG G hit.2.prod := by
  obtain ⟨k, d0, hk, _, hd⟩ := gitLoop_hit (i := hit.1) (d := hit.2) h
  rw [hd]
  have hk' : Treap.get (gutMi m f) k = some (hit.1, d0) := (Treap.mem_tap _ _ _).mp hk
  have hd0 : SockG G d0.prod := by
    have hg' : Treap.get m f = some (gutMi m f) ∨ gutMi m f = Treap.empty := by
      unfold gutMi Treap.gut
      cases e : Treap.get m f <;> simp
    rcases hg' with hg' | hg'
    · exact hm f _ k _ hg' hk'
    · rw [hg', Treap.get_empty] at hk'; cases hk'
  exact sockG_patchProd hG hs d0.map d0.prod hd0

/-- An identity that may be pushed: formula in `G`, subject sock good and not `%void`. -/
def KeyG (G : Noun → Prop) (i : Ident) : Prop := G i.2 ∧ SockG G i.1 ∧ i.1 ≠ Sock.void

/-- **The arm invariant.** -/
structure ClInv (G : Noun → Prop) (st : SkaState M R) : Prop where
  g_prod : ∀ i d, gCore st.g i = some d → SockG G d.prod
  done_g : MemoG G st.done
  ord_key : ∀ i o, Treap.get st.order i = some o → KeyG G i
  stk_key : ∀ i ∈ st.stk, KeyG G i

theorem ClInv.congr {st st' : SkaState M R} (h : ClInv G st) (h1 : st'.g = st.g) (h2 : st'.done = st.done)
    (h3 : st'.order = st.order) (h4 : st'.stk = st.stk) : ClInv G st' :=
  ⟨by rw [h1]; exact h.g_prod, by rw [h2]; exact h.done_g, by rw [h3]; exact h.ord_key,
    by rw [h4]; exact h.stk_key⟩

theorem ClInv.gitG {st : SkaState M R} (h : ClInv G st) (i : Ident) : SockG G (gitG st.g i).prod := by
  unfold Ana.gitG Treap.gut
  cases e : Treap.get st.g i with
  | none => trivial
  | some d => exact h.g_prod i d.core (by simp [gCore, e])

theorem gprod_put {g : Graph} (hg : ∀ i d, g i = some d → SockG G d.prod) {i : Sock × Noun} {d : Datum}
    (hd : SockG G d.prod) : ∀ j e, g.put i d j = some e → SockG G e.prod := by
  intro j e hj
  unfold Graph.put at hj
  split at hj
  · cases hj; exact hd
  · exact hg j e hj

theorem clInv_stable : LocalStable (fun gs : GenS M R => ClInv G gs.st) := by
  intro gs gs' h _ _ e3 e4 e5 e6 _ _ _ _
  exact h.congr e3 e4 e5 e6

/-! ## 2. The writes -/

theorem cullFold_C (l : List (Ident × Unit)) (st : SkaState M R) (hc : ClInv G st) :
    ClInv G (l.foldl cullStep st) := by
  obtain ⟨a1, a2, a3, a4, _⟩ := cullFold_ok l st
  refine ⟨fun i d hi => ?_, by rw [a2]; exact hc.done_g, fun i o hi => ?_, by rw [a1]; exact hc.stk_key⟩
  · simp only [gCore] at hi
    rw [a4] at hi
    split at hi
    · simp at hi
    · exact hc.g_prod i d (by simp only [gCore]; exact hi)
  · rw [a3] at hi
    split at hi
    · cases hi
    · exact hc.ord_key i o hi

theorem cull_C {n : Nat} {id : Ident} {st st' : SkaState M R} (hc : ClInv G st) (h : cull n id st = some st') :
    ClInv G st' := by
  rw [cull_eq] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨ab, _, live, _, hst⟩ := h
  split at hst
  · subst hst; exact hc
  · subst hst
    exact cullFold_C _ _ ⟨hc.g_prod, hc.done_g, hc.ord_key, fun i hi => hc.stk_key i (List.mem_filter.mp hi).1⟩

theorem popGo_C {id : Ident} : ∀ (l : List Ident) (st st' : SkaState M R),
    st.stk = l → ClInv G st → popGo id l st = some st' → ClInv G st'
  | [], _, _, _, _, h => by simp [popGo] at h
  | top :: rest, st, st', hl, hc, h => by
    unfold popGo at h
    simp only at h
    obtain ⟨d0, hgit⟩ : ∃ d0, gitG st.g top = d0 := ⟨_, rfl⟩
    simp only [hgit] at h
    have hp0 : SockG G d0.prod := hgit ▸ hc.gitG top
    let d' : FDatum M := if d0.prod = Sock.void then { d0 with prod := Sock.dunno } else d0
    have hd' : SockG G d'.prod := by
      show SockG G (if d0.prod = Sock.void then { d0 with prod := Sock.dunno } else d0).prod
      split
      · trivial
      · exact hp0
    let st2 : SkaState M R :=
      { st with stk := rest, order := Treap.del st.order top, ticks := Treap.del st.ticks top,
                g := Treap.put st.g top d', done := putMi st.done top d' }
    have c2 : ClInv G st2 := by
      refine ⟨?_, hc.done_g.putMi hd', fun i o hi => ?_, fun i hi => hc.stk_key i (by rw [hl]; exact List.mem_cons_of_mem _ hi)⟩
      · show ∀ i d, gCore (Treap.put st.g top d') i = some d → SockG G d.prod
        rw [gCore_put]
        exact gprod_put hc.g_prod hd'
      · have hi' : Treap.get (Treap.del st.order top) i = some o := hi
        rw [Treap.get_del] at hi'
        split at hi'
        · cases hi'
        · exact hc.ord_key i o hi'
    by_cases e : top = id
    · rw [if_pos e] at h
      cases h
      exact c2
    · rw [if_neg e] at h
      exact popGo_C rest st2 st' rfl c2 h

theorem pop_C {id : Ident} {st st' : SkaState M R} (hc : ClInv G st) (h : pop id st = some st') : ClInv G st' :=
  popGo_C st.stk st st' rfl hc h

/-! ## 3. The arms -/

/-- What the `resolve` loop begun with `orig` keeps, for a good `orig.1`. -/
def ResC (G : Noun → Prop) (orig : Ident) (res : ResGo M R) : Prop :=
  ∀ idT gs r gs', SockG G orig.1 → ClInv G gs.st → KeyG G idT → res idT gs = some (r, gs') →
    ClInv G gs'.st ∧ SockG G r.2.prod

def AnaC (G : Noun → Prop) (ana : AnaGo M R) : Prop :=
  ∀ id st low st', ClInv G st → KeyG G id → ana id st = some (low, st') → ClInv G st'

def RunC (G : Noun → Prop) (run : RunGo M R) : Prop :=
  ∀ id index st r st', ClInv G st → KeyG G id → run id index st = some (r, st') → ClInv G st'

def MemC (G : Noun → Prop) (mem : MemGo M R) : Prop :=
  ∀ index pass ms st r st', ClInv G st → mem index pass ms st = some (r, st') → ClInv G st'

def PassC (G : Noun → Prop) (pass : PassGo M R) : Prop :=
  ∀ id index p st low st', ClInv G st → pass id index p st = some (low, st') → ClInv G st'

theorem resolveStep_C (env : Env R) (hG : SubC G) {orig : Ident} {resolve : ResGo M R} {analyze : AnaGo M R}
    (hres : ResC G orig resolve) (hana : AnaC G analyze) : ResC G orig (resolveStep env resolve analyze orig) := by
  intro idT gs r gs' ho hc hk e
  unfold resolveStep at e
  cases hg : Treap.get gs.st.g idT with
  | some d =>
    simp only [hg] at e
    have hp : SockG G d.prod := hc.g_prod idT d.core (by simp [gCore, hg])
    cases ho' : Treap.get gs.st.order idT with
    | none =>
      simp only [ho', Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨hc, hp⟩
    | some o =>
      simp only [ho', Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨hc, hp⟩
  | none =>
    rw [hg] at e
    simp only at e
    split at e
    · cases e
    · rename_i m hm
      cases e
      exact ⟨hc, gitMi_G hG hc.done_g hk.2.1 hm⟩
    · split at e
      · cases e
      · rename_i i hrc
        have hki : KeyG G i := by
          rcases recursiveCall_cases hrc with ⟨hb, _⟩ | ⟨_, j, hj, hm, he⟩
          · cases hb
          · have hkj := hc.stk_key j hj
            exact ⟨by rw [he]; exact hk.1, sockG_msgSock hk.2.1 hkj.2.1 hm, msgSock_ne_void hk.2.2 hm⟩
        exact hres i gs r gs' ho hc hki e
      · rename_i i hrc
        simp only [Option.map_eq_some_iff] at e
        obtain ⟨o, _, e⟩ := e
        cases e
        exact ⟨hc, sockG_patchProd hG ho _ _ (hc.gitG i)⟩
      · simp only [Option.map_eq_some_iff] at e
        obtain ⟨⟨low, st'⟩, ha, e⟩ := e
        cases e
        have c' := hana idT gs.st low st' hc hk ha
        exact ⟨c', c'.gitG idT⟩

theorem runStep_C (env : Env R) (memoF : Memo M) (hG : SubC G) (hS : SafC G) {n : Nat}
    (hres : ∀ k, k < n → ∀ orig, ResC G orig (resolve env memoF k orig)) :
    RunC G (runStep (folLoop env memoF n)) := by
  intro id index st r st' hc hk e
  unfold runStep at e
  simp only [Option.map_eq_some_iff] at e
  obtain ⟨⟨out, gs⟩, hf, e⟩ := e
  cases e
  let st0 : SkaState M R := { st with stats := { st.stats with runs := st.stats.runs + 1 } }
  have c0 : ClInv G (genInit index st0).st := hc.congr rfl rfl rfl rfl
  have hRG : ∀ k, k < n → ResGG G (fun gs : GenS M R => ClInv G gs.st) (resolveR env memoF k) :=
    fun k hk idT gs r gs' hi hf' hs' hv e => hres k hk idT idT gs r gs' hs' hi ⟨hf', hs', hv⟩ e
  obtain ⟨c1, p1⟩ := run_folG env memoF hG hS clInv_stable hRG c0 hk.1 hk.2.1 hf
  obtain ⟨e1, e2, e3, _⟩ := runEnd_fields id (gitG st0.g id) out gs
  have hold : SockG G (gitG st0.g id).core.prod := hc.gitG id
  show ClInv G (runEnd id (gitG st0.g id) out gs).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [runEnd_core]
    exact gprod_put c1.g_prod (sockG_runDatum hG p1 hold)
  · rw [e3]; exact c1.done_g
  · rw [e1]; exact c1.ord_key
  · rw [e2]; exact c1.stk_key

theorem memberStep_C {run : RunGo M R} {mem : MemGo M R} (hrun : RunC G run) (hmem : MemC G mem) :
    MemC G (memberStep run mem) := by
  intro index pass ms st r st' hc e
  cases ms with
  | nil =>
    simp only [memberStep, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    exact hc
  | cons m ms =>
    have key : ∀ st1 : SkaState M R,
        ((Treap.get st.order m).bind fun o => (run m o st1).bind fun r =>
          if r.1.1 < index then some ((r.1.1, r.1.2.2), r.2) else
          (mem index pass ms r.2).map fun t => ((min r.1.1 t.1.1, r.1.2.2 || t.1.2), t.2)) = some (r, st') →
        st1.g = st.g → st1.done = st.done → st1.order = st.order → st1.stk = st.stk → ClInv G st' := by
      intro st1 e h1 h2 h3 h4
      simp only [Option.bind_eq_some_iff] at e
      obtain ⟨o, ho, ⟨r1, st2⟩, hr, e⟩ := e
      have c1 : ClInv G st1 := hc.congr h1 h2 h3 h4
      have c2 := hrun _ _ _ _ _ c1 (hc.ord_key m o ho) hr
      split at e
      · simp only [Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨_, rfl⟩ := e
        exact c2
      · simp only [Option.map_eq_some_iff] at e
        obtain ⟨⟨t1, st3⟩, ht, e⟩ := e
        cases e
        exact hmem _ _ _ _ _ _ c2 ht
    simp only [memberStep] at e
    split at e
    · exact hmem _ _ _ _ _ _ hc e
    · by_cases hp : pass > 1
      · simp only [hp, if_true] at e
        exact key _ e rfl rfl rfl rfl
      · simp only [hp, if_false] at e
        exact key _ e rfl rfl rfl rfl

theorem passStep_C {n : Nat} {mem : MemGo M R} {pass : PassGo M R} (hmem : MemC G mem)
    (hpass : PassC G pass) : PassC G (passStep n mem pass) := by
  intro id index p st low st' hc e
  unfold passStep at e
  simp only [Option.bind_eq_some_iff] at e
  obtain ⟨ab, _, members, _, ⟨r1, st2⟩, hml, e⟩ := e
  have c2 : ClInv G st2 := hmem _ _ _ _ _ _ (by exact hc.congr rfl rfl rfl rfl) hml
  simp only at e
  split at e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    exact c2
  · split at e
    · unfold passEnd at e
      simp only [Option.bind_eq_some_iff] at e
      obtain ⟨_, _, _, _, e⟩ := e
      split at e
      · exact hpass _ _ _ _ _ _ c2 e
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at e
        obtain ⟨st3, hc3, st4, hp, e⟩ := e
        cases e
        exact pop_C (cull_C c2 hc3) hp
    · exact hpass _ _ _ _ _ _ c2 e

theorem cullPass_C {n : Nat} {pass : PassGo M R} (hpass : PassC G pass) {id : Ident} {index : Nat}
    {st st' : SkaState M R} {low : Nat} (hc : ClInv G st) (h : cullPass n pass id index st = some (low, st')) :
    ClInv G st' := by
  unfold cullPass at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨st1, hc1, h⟩ := h
  exact hpass _ _ _ _ _ _ (cull_C hc hc1) h

theorem analyzeStep_C (hG : SubC G) {n : Nat} {memoF : Memo M} (hmG : MemoG G memoF) {run : RunGo M R}
    {pass : PassGo M R} (hrun : RunC G run) (hpass : PassC G pass) : AnaC G (analyzeStep n memoF run pass) := by
  intro id st low st' hc hk e
  unfold analyzeStep at e
  split at e
  · cases e
  · rename_i hit hm
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    have hp := gitMi_G hG hmG hk.2.1 hm
    refine ⟨?_, hc.done_g.putMi hp, hc.ord_key, hc.stk_key⟩
    show ∀ i d, gCore (Treap.put st.g id hit.2) i = some d → SockG G d.prod
    rw [gCore_put]
    exact gprod_put hc.g_prod hp
  · simp only [Option.bind_eq_some_iff] at e
    obtain ⟨⟨r1, st2⟩, hr, e⟩ := e
    let stp : SkaState M R := { st with next := st.next + 1, order := Treap.put st.order id st.next,
                                         stk := id :: st.stk, g := Treap.put st.g id FDatum.bunt }
    have cp : ClInv G stp := by
      refine ⟨?_, hc.done_g, fun i o hi => ?_, fun i hi => ?_⟩
      · show ∀ i d, gCore (Treap.put st.g id FDatum.bunt) i = some d → SockG G d.prod
        rw [gCore_put]
        exact gprod_put hc.g_prod (d := FDatum.bunt.core) trivial
      · have hi' : Treap.get (Treap.put st.order id st.next) i = some o := hi
        rw [Treap.get_put] at hi'
        split at hi'
        · rename_i h; rw [h]; exact hk
        · exact hc.ord_key i o hi'
      · rcases List.mem_cons.mp hi with rfl | hi
        · exact hk
        · exact hc.stk_key i hi
    have c2 : ClInv G st2 := hrun _ _ _ _ _ cp hk hr
    simp only at e
    split at e
    · simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨_, rfl⟩ := e
      exact c2
    · split at e
      · exact cullPass_C hpass c2 e
      · simp only [Option.bind_eq_some_iff] at e
        obtain ⟨ab, _, e⟩ := e
        split at e
        · exact cullPass_C hpass c2 e
        · simp only [Option.map_eq_some_iff] at e
          obtain ⟨st3, hp, e⟩ := e
          cases e
          exact pop_C c2 hp

/-- The arms at the fuel `n` keep `ClInv G`. -/
def AllCl (G : Noun → Prop) (env : Env R) (memoF : Memo M) (n : Nat) : Prop :=
  (∀ orig, ResC G orig (resolve env memoF n orig)) ∧ AnaC G (analyze env memoF n) ∧ RunC G (run env memoF n) ∧
    PassC G (passLoop env memoF n) ∧ MemC G (memberLoop env memoF n)

theorem allCl_zero (env : Env R) (memoF : Memo M) : AllCl G env memoF 0 := by
  refine ⟨fun _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ h => ?_,
    fun _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ h => ?_⟩
  · rw [resolve_zero] at h; cases h
  · rw [analyze_zero] at h; cases h
  · rw [run_zero] at h; cases h
  · rw [passLoop_zero] at h; cases h
  · rw [memberLoop_zero] at h; cases h

/-- **Every arm keeps the arm invariant**, at every fuel, from a persistent
memo with good products. -/
theorem allCl (env : Env R) (memoF : Memo M) (hG : SubC G) (hS : SafC G) (hmG : MemoG G memoF) :
    ∀ n, ∀ k, k ≤ n → AllCl G env memoF k
  | 0 => fun k hk => by rw [Nat.le_zero.mp hk]; exact allCl_zero env memoF
  | n + 1 => fun k hk => by
    rcases Nat.lt_or_ge k (n + 1) with hl | hl
    · exact allCl env memoF hG hS hmG n k (Nat.le_of_lt_succ hl)
    · have e : k = n + 1 := Nat.le_antisymm hk hl
      subst e
      obtain ⟨r, a, u, p, m⟩ := allCl env memoF hG hS hmG n n (Nat.le_refl n)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro orig; rw [resolve_succ]; exact resolveStep_C env hG (r orig) a
      · rw [analyze_succ]; exact analyzeStep_C hG hmG u p
      · rw [run_succ]
        exact runStep_C env memoF hG hS (fun k hk => (allCl env memoF hG hS hmG n k (Nat.le_of_lt hk)).1)
      · rw [passLoop_succ]; exact passStep_C m p
      · rw [memberLoop_succ]; exact memberStep_C u m

/-- A pass that goes on keeps `ClInv G`. -/
theorem passGoOn_C (env : Env R) (memoF : Memo M) (hG : SubC G) (hS : SafC G) (hmG : MemoG G memoF)
    {n : Nat} {id : Ident} {index pass : Nat} {st st' : SkaState M R} (hc : ClInv G st)
    (h : PassGoOn env memoF n id index pass st st') : ClInv G st' := by
  have key : ∀ members r, memberLoop env memoF n index pass members
      { st with stats := { st.stats with passes := st.stats.passes + 1 } } = some (r, st') → ClInv G st' :=
    fun members r hml => (allCl env memoF hG hS hmG n n (Nat.le_refl n)).2.2.2.2 _ _ _ _ _ _ (by exact hc.congr rfl rfl rfl rfl) hml
  rcases h with ⟨ab, members, r, _, _, h3, _⟩ | ⟨ab, members, r, _, _, h3, _⟩
  · exact key members r h3
  · exact key members r h3

end Arm

/-! ## 4. `OkId` of the members, and the loop of one component -/

/-- **The closure invariant as a theorem of the model**: from `ClInv` at the
loop's entry, with `G = NGood As B`, every stack member along the chains of
passes is `OkId (nounsUpTo As B) (leafList As B)`. -/
theorem hok_of_clInv (env : Env R) {memoF : Memo M} (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNorm memoF) (hmI : MemoNI memoF) {As : List Nat} {B : Nat} (hmG : MemoG (NGood As B) memoF)
    {id : Ident} {index : Nat} {rest : List Ident} {x : Nat × SkaState M R}
    (hc : ChainInv memoF id index rest x.2) (hx : ClInv (NGood As B) x.2) :
    ∀ y, PassReachQ env memoF id index x y → ∀ i ∈ y.2.stk, OkId (nounsUpTo As B) (leafList As B) i := by
  intro y hy
  have hcy : ClInv (NGood As B) y.2 := by
    induction hy with
    | refl => exact hx
    | step _ hp ih => exact passGoOn_C env memoF (subC_nGood As B) (safC_nGood As B) hmG ih hp
  have hiy := passReachQ_inv env hmF hmT hmN hmI hy hc
  intro i hi
  obtain ⟨k1, k2, k3⟩ := hcy.stk_key i hi
  exact okId_of_good k1 k3 (TInv.stk hiy.1 hiy.2.1 hi) k2

/-- **The pass loop of one component returns** from `KruskalBT`, `RunHalts`,
the width `WidthFin`, a good stack at its entry, and the arm invariant
`ClInv (NGood As B)` at its entry with a persistent memo of good products:
`passLoop_returns_ws` with `hok` discharged. -/
theorem passLoop_returns_wc (hK : KruskalBT) (env : Env R) {memoF : Memo M} (hmF : MemoWF memoF)
    (hmT : MemoTP memoF) (hmN : MemoNorm memoF) (hmI : MemoNI memoF) (hrun : RunHalts env memoF)
    (hhe : env.he = Compiler.heSock) {As : List Nat} {B : Nat} (hmG : MemoG (NGood As B) memoF)
    (id : Ident) (index : Nat) (rest : List Ident) (x : Nat × SkaState M R)
    (hc : ChainInv memoF id index rest x.2) (hsg : SG env x.2) (hx : ClInv (NGood As B) x.2)
    (hw : WidthFin env memoF id index x) :
    ∃ n r, passLoop env memoF n id index x.1 x.2 = some r :=
  passLoop_returns_ws hK env hmF hmT hmN hmI hrun hhe id index rest x hc hsg
    (hok_of_clInv env hmF hmT hmN hmI hmG hc hx) hw

end Ana
end SkaModel
end Formalization
