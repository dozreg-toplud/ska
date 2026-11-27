import lemmas.Ska.PassQuiet
import lemmas.Ska.PassIdents

/-!
# No identity leaves the graph in a pass (track F, Gaps 16)

`PassGrowG` (`Ska/PassQuiet.lean`) proved: a pass that goes on keeps every
identity of `g`, and a pass that pushes leaves in `g` an identity that was
not there (`passGoOn_grow`).  With it, `passLoop_returns_runs` needs only
`RunHalts` and `FinIdentsG` (`passLoop_returns_g`).

The argument, for every arm at every fuel (`allG`, the skeleton of `allN`):
the arms keep "every stack member is in `g`" (`Sg`), never remove an identity
of `g` they started with, and grow the stack on top by identities that were
not in `g` at their start (`GG`).  The only removal is `+cull` (at the start
of a component's pass loop, and in `passEnd`), and it removes members above
the root of the nested `+analyze`, which were all pushed inside it: so the
pass loop and `+cull` are stated against an ANCHOR `st0`, the state before
the push of the root (`PassG`, `cull_gg`, `pop_gg`).  A push (`Grow`) leaves
its root in `g` (it is never culled: it is live, and `+pop` puts it).
No invariant of the datum is needed: these are facts of the control flow and
of `Sg`.
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## 1. The relation -/

/-- `i` is in the graph of `st`. -/
def GIn (st : SkaState M R) (i : Ident) : Prop := Treap.get st.g i ≠ none

/-- Every stack member is in the graph. -/
def Sg (st : SkaState M R) : Prop := ∀ i ∈ st.stk, GIn st i

/-- From `st` to `st'`: the stack stays in the graph, no identity leaves the
graph, and the stack grows on top by identities that were not in the graph. -/
def GG (st st' : SkaState M R) : Prop :=
  Sg st' ∧ (∀ i, GIn st i → GIn st' i) ∧ ∃ N, st'.stk = N ++ st.stk ∧ ∀ i ∈ N, ¬ GIn st i

/-- A push between `st` and `st'` leaves in the graph an identity that was not in it. -/
def Grow (st st' : SkaState M R) : Prop :=
  st.next < st'.next → ∃ i, ¬ GIn st i ∧ GIn st' i

theorem get_put_ne_none {κ ν : Type} [DecidableEq κ] [TKey κ] {m : M κ ν} {k i : κ} {v : ν}
    (h : Treap.get m i ≠ none) : Treap.get (Treap.put m k v) i ≠ none := by
  rw [Treap.get_put]
  split
  · simp
  · exact h

theorem get_put_self_ne_none {κ ν : Type} [DecidableEq κ] [TKey κ] (m : M κ ν) (k : κ) (v : ν) :
    Treap.get (Treap.put m k v) k ≠ none := by
  rw [Treap.get_put, if_pos rfl]; simp

theorem GG.refl' {st st' : SkaState M R} (h : Sg st) (hg : st'.g = st.g) (hs : st'.stk = st.stk) :
    GG st st' :=
  ⟨fun i hi => by unfold GIn; rw [hg]; exact h i (hs ▸ hi), fun i hi => by unfold GIn; rw [hg]; exact hi,
    [], by rw [hs]; rfl, fun _ h => absurd h List.not_mem_nil⟩

theorem GG.trans {a b c : SkaState M R} (h1 : GG a b) (h2 : GG b c) : GG a c := by
  obtain ⟨N1, e1, f1⟩ := h1.2.2
  obtain ⟨N2, e2, f2⟩ := h2.2.2
  refine ⟨h2.1, fun i h => h2.2.1 i (h1.2.1 i h), N2 ++ N1, by rw [e2, e1, List.append_assoc],
    fun i hi => ?_⟩
  rcases List.mem_append.mp hi with hi | hi
  · exact fun hg => f2 i hi (h1.2.1 i hg)
  · exact f1 i hi

theorem GG.congr_r {a b b' : SkaState M R} (h : GG a b) (hg : b'.g = b.g) (hs : b'.stk = b.stk) : GG a b' :=
  h.trans (GG.refl' h.1 hg hs)

theorem Grow.refl' {st st' : SkaState M R} (h : st'.next = st.next) : Grow st st' :=
  fun hl => absurd hl (by rw [h]; exact Nat.lt_irrefl _)

theorem Grow.trans {a b c : SkaState M R} (g1 : GG a b) (g2 : GG b c) (h1 : Grow a b) (h2 : Grow b c) :
    Grow a c := by
  intro hl
  rcases Nat.lt_or_ge a.next b.next with h | h
  · obtain ⟨i, hi, hi'⟩ := h1 h; exact ⟨i, hi, g2.2.1 i hi'⟩
  · obtain ⟨i, hi, hi'⟩ := h2 (by omega); exact ⟨i, fun h => hi (g1.2.1 i h), hi'⟩

theorem Grow.congr_r {a b b' : SkaState M R} (h : Grow a b) (hn : b'.next = b.next) (hg : b'.g = b.g) :
    Grow a b' := fun hl => by
  obtain ⟨i, h1, h2⟩ := h (hn ▸ hl)
  exact ⟨i, h1, by unfold GIn; rw [hg]; exact h2⟩

/-- A write into the graph with the stack the same. -/
theorem gg_put {st st' : SkaState M R} (h : Sg st) {j : Ident} {d : FDatum M}
    (hg : st'.g = Treap.put st.g j d) (hs : st'.stk = st.stk) : GG st st' ∧ GIn st' j := by
  have mono : ∀ i, GIn st i → GIn st' i := fun i hi => by unfold GIn; rw [hg]; exact get_put_ne_none hi
  refine ⟨⟨fun i hi => mono i (h i (hs ▸ hi)), mono, [], by rw [hs]; rfl,
    fun _ h => absurd h List.not_mem_nil⟩, ?_⟩
  unfold GIn; rw [hg]; exact get_put_self_ne_none _ _ _

/-! ## 2. `+cull` and `+pop` against an anchor -/

/-- The first occurrence of `id` in `N ++ L`, when `id ∈ N`, is inside `N`. -/
theorem prefix_sub {id : Ident} : ∀ {ab0 rest N L : List Ident}, ab0 ++ id :: rest = N ++ L → id ∉ ab0 →
    id ∈ N → ∃ N', N = ab0 ++ id :: N' ∧ rest = N' ++ L
  | [], _, [], _, _, _, hN => absurd hN List.not_mem_nil
  | [], _, x :: N, _, e, _, _ => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨N, rfl, rfl⟩
  | _ :: _, _, [], _, _, _, hN => absurd hN List.not_mem_nil
  | a :: ab0, rest, x :: N, L, e, hn, hN => by
    simp only [List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, e⟩ := e
    have hn' : id ∉ ab0 := fun h => hn (List.mem_cons_of_mem _ h)
    have hN' : id ∈ N := by
      rcases List.mem_cons.mp hN with h | h
      · exact absurd (by rw [h]; exact List.mem_cons_self) hn
      · exact h
    obtain ⟨N', rfl, rfl⟩ := prefix_sub e hn' hN'
    exact ⟨N', rfl, rfl⟩

/-- **What `+cull` does**: it deletes from the graph and filters out of the
stack the identities of a set `d` that lies in the members strictly above
`id` (the first `id` from the top). -/
theorem cull_struct {n : Nat} {id : Ident} {st st' : SkaState M R} (h : cull n id st = some st') :
    ∃ (ab0 rest : List Ident) (d : Ident → Bool), st.stk = ab0 ++ id :: rest ∧ id ∉ ab0 ∧
      (∀ k, d k = true → k ∈ ab0) ∧
      (∀ k, Treap.get st'.g k = if d k = true then none else Treap.get st.g k) ∧
      st'.stk = st.stk.filter (fun k => !d k) := by
  rw [cull_eq] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨ab, hab, live, hlive, hst⟩ := h
  obtain ⟨ab0, rest, rfl, hs, hnin⟩ := above_eq hab
  have hmem : ∀ k, Treap.has (Treap.silt (ab0 ++ [id]) : M Ident Unit) k = true ↔ k ∈ ab0 ++ [id] :=
    fun k => Treap.has_silt _ k
  have hid : Treap.has live id = true := liveLoop_head hlive ((hmem id).mpr (by simp))
  generalize hdd : (Treap.dif (Treap.silt (ab0 ++ [id])) live : M Ident Unit) = dead at hst
  have hdead : ∀ k, Treap.has dead k = true → k ∈ ab0 := by
    intro k hk
    rw [← hdd] at hk
    have e : Treap.has (Treap.dif (Treap.silt (ab0 ++ [id]) : M Ident Unit) live) k =
        (Treap.get (Treap.dif (Treap.silt (ab0 ++ [id]) : M Ident Unit) live) k).isSome := rfl
    rw [e, Treap.get_dif] at hk
    by_cases hl : Treap.has live k = true
    · rw [if_pos hl] at hk; cases hk
    · rw [if_neg hl] at hk
      rcases List.mem_append.mp ((hmem k).mp hk) with h1 | h1
      · exact h1
      · rw [List.mem_singleton.mp h1] at hl; exact absurd hid hl
  split at hst
  · subst hst
    exact ⟨ab0, rest, fun _ => false, hs, hnin, (fun k hk => by simp at hk), (fun k => by simp), (List.filter_eq_self.mpr (fun _ _ => rfl)).symm⟩
  · subst hst
    obtain ⟨a1, _, _, a4, _⟩ := cullFold_ok (Treap.rap dead)
      { st with stats := { st.stats with culled := st.stats.culled + Treap.wyt dead },
                stk := st.stk.filter (fun i => !Treap.has dead i), moved := Treap.dif st.moved dead }
    have hL : ∀ k, k ∈ (Treap.rap dead).map (·.1) ↔ Treap.has dead k = true := mem_rap_keys dead
    refine ⟨ab0, rest, fun k => Treap.has dead k, hs, hnin, hdead, fun k => ?_, by rw [a1]⟩
    rw [a4]
    by_cases hk : Treap.has dead k = true
    · rw [if_pos ((hL k).mpr hk), if_pos hk]
    · rw [if_neg (fun h => hk ((hL k).mp h)), if_neg hk]

theorem mem_new {id : Ident} {st0 st : SkaState M R} (h0 : Sg st0) (hn : ¬ GIn st0 id) {N : List Ident}
    (eN : st.stk = N ++ st0.stk) (hm : id ∈ st.stk) : id ∈ N := by
  rw [eN] at hm
  rcases List.mem_append.mp hm with h1 | h1
  · exact h1
  · exact absurd (h0 id h1) hn

/-- **`+cull` of a root pushed after the anchor `st0`** removes no identity
of the graph of `st0` and keeps the root on the stack. -/
theorem cull_gg {n : Nat} {id : Ident} {st0 st st' : SkaState M R} (h0 : Sg st0) (hg : GG st0 st)
    (hn : ¬ GIn st0 id) (hm : id ∈ st.stk) (h : cull n id st = some st') : GG st0 st' ∧ id ∈ st'.stk := by
  obtain ⟨ab0, rest, d, hs, hnin, hd, hgk, hstk⟩ := cull_struct h
  obtain ⟨hsg, hmono, N, eN, hfr⟩ := hg
  obtain ⟨N', hN', _⟩ := prefix_sub (hs.symm.trans eN) hnin (mem_new h0 hn eN hm)
  have hd0 : ∀ k, d k = true → ¬ GIn st0 k := fun k hk =>
    hfr k (by rw [hN']; exact List.mem_append_left _ (hd k hk))
  have hst0 : ∀ k ∈ st0.stk, d k = false := fun k hk => by
    cases e : d k
    · rfl
    · exact absurd (h0 k hk) (hd0 k e)
  have gk : ∀ k, d k = false → GIn st k → GIn st' k := fun k hk hk' => by
    unfold GIn; rw [hgk k, hk]; exact hk'
  refine ⟨⟨fun k hk => ?_, fun k hk => ?_, N.filter (fun k => !d k), ?_, fun k hk => ?_⟩, ?_⟩
  · rw [hstk, List.mem_filter] at hk
    exact gk k (by simpa using hk.2) (hsg k hk.1)
  · cases e : d k
    · exact gk k e (hmono k hk)
    · exact absurd hk (hd0 k e)
  · rw [hstk, eN, List.filter_append]
    congr 1
    exact List.filter_eq_self.mpr (fun k hk => by simp [hst0 k hk])
  · exact hfr k (List.mem_filter.mp hk).1
  · rw [hstk, List.mem_filter]
    refine ⟨hm, ?_⟩
    cases e : d id
    · rfl
    · exact absurd (hd id e) hnin

theorem popGo_g {id : Ident} : ∀ (l : List Ident) (st st' : SkaState M R),
    popGo id l st = some st' → ∃ pre, l = pre ++ id :: st'.stk ∧ id ∉ pre ∧ ∀ i, GIn st i → GIn st' i
  | [], _, _, h => by simp [popGo] at h
  | top :: rest, st, st', h => by
    unfold popGo at h
    simp only at h
    split at h
    · rename_i e
      cases h
      subst e
      exact ⟨[], rfl, List.not_mem_nil, fun i hi => get_put_ne_none hi⟩
    · rename_i e
      obtain ⟨pre, h1, h2, h3⟩ := popGo_g rest _ st' h
      refine ⟨top :: pre, by rw [h1]; rfl, ?_, fun i hi => h3 i (get_put_ne_none hi)⟩
      simp only [List.mem_cons, not_or]
      exact ⟨fun h => e h.symm, h2⟩

/-- **`+pop` of a root pushed after the anchor `st0`.** -/
theorem pop_gg {id : Ident} {st0 st st' : SkaState M R} (h0 : Sg st0) (hg : GG st0 st)
    (hn : ¬ GIn st0 id) (hm : id ∈ st.stk) (h : pop id st = some st') : GG st0 st' ∧ GIn st' id := by
  obtain ⟨pre, hl, hnin, hmono⟩ := popGo_g st.stk st st' h
  obtain ⟨hsg, hm0, N, eN, hfr⟩ := hg
  obtain ⟨N', hN', hrest⟩ := prefix_sub (hl.symm.trans eN) hnin (mem_new h0 hn eN hm)
  refine ⟨⟨fun k hk => hmono k (hsg k (by rw [hl]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hk))),
    fun k hk => hmono k (hm0 k hk), N', hrest, fun k hk => hfr k ?_⟩, hmono id (hsg id hm)⟩
  rw [hN']; exact List.mem_append_right _ (List.mem_cons_of_mem _ hk)

/-! ## 3. The arms -/

/-- What `resolve` keeps. -/
def ResG (res : ResGo M R) : Prop :=
  ∀ idT gs r gs', Sg gs.st → res idT gs = some (r, gs') → GG gs.st gs'.st ∧ Grow gs.st gs'.st ∧ gs'.gen = gs.gen

/-- What `+analyze` of an identity not in the graph keeps; it leaves the identity in the graph. -/
def AnaG (ana : AnaGo M R) : Prop :=
  ∀ id st low st', Sg st → Treap.get st.g id = none → ana id st = some (low, st') →
    GG st st' ∧ Grow st st' ∧ GIn st' id

def RunG (run : RunGo M R) : Prop :=
  ∀ id index st r st', Sg st → run id index st = some (r, st') → GG st st' ∧ Grow st st'

def MemG (mem : MemGo M R) : Prop :=
  ∀ index pass ms st r st', Sg st → mem index pass ms st = some (r, st') → GG st st' ∧ Grow st st'

/-- The pass loop of a root `id` pushed after the anchor `st0` (its `+cull`
removes members pushed after `st0`): it keeps `GG` from the anchor and leaves
the root in the graph. -/
def PassG (pass : PassGo M R) : Prop :=
  ∀ id index p st low st' (st0 : SkaState M R), Sg st0 → GG st0 st → ¬ GIn st0 id → id ∈ st.stk →
    pass id index p st = some (low, st') → GG st0 st' ∧ GIn st' id

theorem resolveStep_g (env : Env R) {orig : Ident} {resolve : ResGo M R} {analyze : AnaGo M R}
    (hres : ResG resolve) (hana : AnaG analyze) : ResG (resolveStep env resolve analyze orig) := by
  intro idT gs r gs' hs e
  have same : GG gs.st gs.st ∧ Grow gs.st gs.st := ⟨GG.refl' hs rfl rfl, Grow.refl' rfl⟩
  unfold resolveStep at e
  cases hg : Treap.get gs.st.g idT with
  | some d =>
    simp only [hg] at e
    cases ho : Treap.get gs.st.order idT with
    | none =>
      simp only [ho, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨same.1, same.2, rfl⟩
    | some o =>
      simp only [ho, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨same.1, same.2, rfl⟩
  | none =>
    rw [hg] at e
    simp only at e
    split at e
    · cases e
    · cases e; exact ⟨same.1, same.2, rfl⟩
    · split at e
      · cases e
      · exact hres _ _ _ _ hs e
      · simp only [Option.map_eq_some_iff] at e
        obtain ⟨o, _, e⟩ := e
        cases e
        exact ⟨same.1, same.2, rfl⟩
      · simp only [Option.map_eq_some_iff] at e
        obtain ⟨⟨low, st'⟩, ha, e⟩ := e
        cases e
        obtain ⟨a, b, _⟩ := hana _ _ _ _ hs hg ha
        exact ⟨a, b, rfl⟩

theorem runStep_g (env : Env R) (memoF : Memo M) {n : Nat}
    (hres : ∀ k, k < n → ResG (resolveR env memoF k)) : RunG (runStep (folLoop env memoF n)) := by
  intro id index st r st' hs e
  unfold runStep at e
  simp only [Option.map_eq_some_iff] at e
  obtain ⟨⟨out, gs⟩, hf, e⟩ := e
  cases e
  let st0 : SkaState M R := { st with stats := { st.stats with runs := st.stats.runs + 1 } }
  have hL : LocalStable (fun gs : GenS M R => GG st0 gs.st ∧ Grow st0 gs.st) := by
    intro gs gs' h _ _ e3 _ _ e6 e7 _ _ _
    exact ⟨h.1.congr_r e3 e6, h.2.congr_r e7 e3⟩
  have h00 : GG st0 st0 := GG.refl' hs rfl rfl
  obtain ⟨i1, _⟩ := run_folTopRQ (P := fun _ _ _ => True) (QA := fun _ => True) (QS := fun _ => True)
    env memoF (fun _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ _ => trivial) hL
    (fun k hk idT gs r gs' hi _ e => by
      obtain ⟨a, b, c⟩ := hres k hk idT gs r gs' hi.1.1 e
      exact ⟨trivial, ⟨hi.1.trans a, Grow.trans hi.1 a hi.2 b⟩, c⟩)
    (Inv := fun gs : GenS M R => GG st0 gs.st ∧ Grow st0 gs.st)
    (index := index) (st := st0) ⟨h00, Grow.refl' rfl⟩ trivial hf
  obtain ⟨_, hs', _, dn, hg⟩ := runEnd_fields id (gitG st0.g id) out gs
  have e2 := gg_put i1.1.1 hg hs'
  have g0 : GG st st0 := GG.refl' hs rfl rfl
  have g1 : GG st (runEnd id (gitG st0.g id) out gs).2 := (g0.trans i1.1).trans e2.1
  refine ⟨g1, Grow.trans g0 (i1.1.trans e2.1) (Grow.refl' rfl) ?_⟩
  exact Grow.trans i1.1 e2.1 i1.2 (Grow.refl' (runEnd_next id _ out gs))

theorem memberStep_g {run : RunGo M R} {mem : MemGo M R} (hrun : RunG run) (hmem : MemG mem) :
    MemG (memberStep run mem) := by
  intro index pass ms st r st' hs e
  cases ms with
  | nil =>
    simp only [memberStep, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    exact ⟨GG.refl' hs rfl rfl, Grow.refl' rfl⟩
  | cons m ms =>
    have key : ∀ st1 : SkaState M R,
        ((Treap.get st.order m).bind fun o => (run m o st1).bind fun r =>
          if r.1.1 < index then some ((r.1.1, r.1.2.2), r.2) else
          (mem index pass ms r.2).map fun t => ((min r.1.1 t.1.1, r.1.2.2 || t.1.2), t.2)) = some (r, st') →
        st1.next = st.next → st1.stk = st.stk → st1.g = st.g → GG st st' ∧ Grow st st' := by
      intro st1 e h1 h2 h3
      simp only [Option.bind_eq_some_iff] at e
      obtain ⟨o, _, ⟨r1, st2⟩, hr, e⟩ := e
      have g0 : GG st st1 := GG.refl' hs h3 h2
      have w0 : Grow st st1 := Grow.refl' h1
      obtain ⟨a, b⟩ := hrun _ _ _ _ _ g0.1 hr
      split at e
      · simp only [Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨_, rfl⟩ := e
        exact ⟨g0.trans a, Grow.trans g0 a w0 b⟩
      · simp only [Option.map_eq_some_iff] at e
        obtain ⟨⟨t1, st3⟩, ht, e⟩ := e
        cases e
        obtain ⟨c, d⟩ := hmem _ _ _ _ _ _ a.1 ht
        exact ⟨(g0.trans a).trans c, Grow.trans (g0.trans a) c (Grow.trans g0 a w0 b) d⟩
    simp only [memberStep] at e
    split at e
    · exact hmem _ _ _ _ _ _ hs e
    · by_cases hp : pass > 1
      · simp only [hp, if_true] at e
        exact key _ e rfl rfl rfl
      · simp only [hp, if_false] at e
        exact key _ e rfl rfl rfl

theorem passStep_g {n : Nat} {mem : MemGo M R} {pass : PassGo M R} (hmem : MemG mem) (hpass : PassG pass) :
    PassG (passStep n mem pass) := by
  intro id index p st low st' st0 h0 hg hn hm e
  unfold passStep at e
  simp only [Option.bind_eq_some_iff] at e
  obtain ⟨ab, _, members, _, ⟨r1, st2⟩, hml, e⟩ := e
  have g1 : GG st { st with stats := { st.stats with passes := st.stats.passes + 1 } } :=
    GG.refl' hg.1 rfl rfl
  obtain ⟨a, _⟩ := hmem _ _ _ _ _ _ g1.1 hml
  have g2 : GG st0 st2 := (hg.trans g1).trans a
  have hm2 : id ∈ st2.stk := by
    obtain ⟨N, eN, _⟩ := (g1.trans a).2.2
    rw [eN]; exact List.mem_append_right _ hm
  have fin : GG st0 st2 ∧ GIn st2 id := ⟨g2, g2.1 id hm2⟩
  simp only at e
  split at e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    exact fin
  · split at e
    · unfold passEnd at e
      simp only [Option.bind_eq_some_iff] at e
      obtain ⟨_, _, _, _, e⟩ := e
      split at e
      · exact hpass _ _ _ _ _ _ st0 h0 g2 hn hm2 e
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at e
        obtain ⟨st3, hc, st4, hp, e⟩ := e
        cases e
        obtain ⟨c1, c2⟩ := cull_gg h0 g2 hn hm2 hc
        exact pop_gg h0 c1 hn c2 hp
    · exact hpass _ _ _ _ _ _ st0 h0 g2 hn hm2 e

theorem cullPass_g {n : Nat} {pass : PassGo M R} (hpass : PassG pass) {id : Ident} {index : Nat}
    {st0 st st' : SkaState M R} {low : Nat} (h0 : Sg st0) (hg : GG st0 st) (hn : ¬ GIn st0 id)
    (hm : id ∈ st.stk) (h : cullPass n pass id index st = some (low, st')) : GG st0 st' ∧ GIn st' id := by
  unfold cullPass at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨st1, hc, h⟩ := h
  obtain ⟨c1, c2⟩ := cull_gg h0 hg hn hm hc
  exact hpass _ _ _ _ _ _ st0 h0 c1 hn c2 h

theorem analyzeStep_g {n : Nat} {memoF : Memo M} {run : RunGo M R} {pass : PassGo M R}
    (hrun : RunG run) (hpass : PassG pass) : AnaG (analyzeStep n memoF run pass) := by
  intro id st low st' hs hg0 e
  have hn : ¬ GIn st id := fun h => h hg0
  unfold analyzeStep at e
  split at e
  · cases e
  · rename_i hit _
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    obtain ⟨a, b⟩ := gg_put (st' := { st with g := Treap.put st.g id hit.2, done := putMi st.done id hit.2 })
      (j := id) (d := hit.2) hs rfl rfl
    exact ⟨a, Grow.refl' rfl, b⟩
  · simp only [Option.bind_eq_some_iff] at e
    obtain ⟨⟨r1, st2⟩, hr, e⟩ := e
    let stp : SkaState M R := { st with next := st.next + 1, order := Treap.put st.order id st.next,
                                         stk := id :: st.stk, g := Treap.put st.g id FDatum.bunt }
    have gp : GG st stp := by
      have mono : ∀ i, GIn st i → GIn stp i := fun i hi => get_put_ne_none hi
      refine ⟨fun i hi => ?_, mono, [id], rfl, fun i hi => ?_⟩
      · rcases List.mem_cons.mp hi with rfl | hi
        · exact get_put_self_ne_none _ _ _
        · exact mono i (hs i hi)
      · rw [List.mem_singleton.mp hi]; exact hn
    obtain ⟨a, _⟩ := hrun _ _ _ _ _ gp.1 hr
    have g2 : GG st st2 := gp.trans a
    have hm2 : id ∈ st2.stk := by
      obtain ⟨N, eN, _⟩ := a.2.2
      rw [eN]; exact List.mem_append_right _ List.mem_cons_self
    have fin : ∀ st', GG st st' ∧ GIn st' id → GG st st' ∧ Grow st st' ∧ GIn st' id :=
      fun st' h => ⟨h.1, fun _ => ⟨id, hn, h.2⟩, h.2⟩
    simp only at e
    split at e
    · simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨_, rfl⟩ := e
      exact fin _ ⟨g2, g2.1 id hm2⟩
    · split at e
      · exact fin _ (cullPass_g hpass hs g2 hn hm2 e)
      · simp only [Option.bind_eq_some_iff] at e
        obtain ⟨ab, _, e⟩ := e
        split at e
        · exact fin _ (cullPass_g hpass hs g2 hn hm2 e)
        · simp only [Option.map_eq_some_iff] at e
          obtain ⟨st3, hp, e⟩ := e
          cases e
          exact fin _ (pop_gg hs g2 hn hm2 hp)

/-- The arms at the fuel `n` keep `GG`. -/
def AllG (env : Env R) (memoF : Memo M) (n : Nat) : Prop :=
  (∀ orig, ResG (resolve env memoF n orig)) ∧ AnaG (analyze env memoF n) ∧ RunG (run env memoF n) ∧
    PassG (passLoop env memoF n) ∧ MemG (memberLoop env memoF n)

theorem allG_zero (env : Env R) (memoF : Memo M) : AllG env memoF 0 := by
  refine ⟨fun _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ h => ?_,
    fun _ _ _ _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ h => ?_⟩
  · rw [resolve_zero] at h; cases h
  · rw [analyze_zero] at h; cases h
  · rw [run_zero] at h; cases h
  · rw [passLoop_zero] at h; cases h
  · rw [memberLoop_zero] at h; cases h

/-- **Every arm keeps `GG`**, at every fuel. -/
theorem allG (env : Env R) (memoF : Memo M) : ∀ n, ∀ k, k ≤ n → AllG env memoF k
  | 0 => fun k hk => by rw [Nat.le_zero.mp hk]; exact allG_zero env memoF
  | n + 1 => fun k hk => by
    rcases Nat.lt_or_ge k (n + 1) with hl | hl
    · exact allG env memoF n k (Nat.le_of_lt_succ hl)
    · have e : k = n + 1 := Nat.le_antisymm hk hl
      subst e
      obtain ⟨r, a, u, p, m⟩ := allG env memoF n n (Nat.le_refl n)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro orig; rw [resolve_succ]; exact resolveStep_g env (r orig) a
      · rw [analyze_succ]; exact analyzeStep_g u p
      · rw [run_succ]
        exact runStep_g env memoF (fun k hk => fun idT gs r' gs' hs e =>
          (allG env memoF n k (Nat.le_of_lt hk)).1 idT idT gs r' gs' hs e)
      · rw [passLoop_succ]; exact passStep_g m p
      · rw [memberLoop_succ]; exact memberStep_g u m

/-! ## 4. `PassGrowG` -/

theorem SInv.sg {st : SkaState M R} (h : SInv st) : Sg st := fun i hi => by
  obtain ⟨d, hd⟩ := h.mem_g hi
  unfold GIn; rw [hd]; simp

/-- **`PassGrowG` holds of every pass that goes on**, from a state whose
stack is in the graph. -/
theorem passGoOn_grow (env : Env R) (memoF : Memo M) {n : Nat} {id : Ident} {index pass : Nat}
    {st st' : SkaState M R} (hs : Sg st) (h : PassGoOn env memoF n id index pass st st') :
    PassGrowG st st' := by
  have key : ∀ members r, memberLoop env memoF n index pass members
      { st with stats := { st.stats with passes := st.stats.passes + 1 } } = some (r, st') →
      PassGrowG st st' := by
    intro members r hml
    have hs' : Sg { st with stats := { st.stats with passes := st.stats.passes + 1 } } := hs
    obtain ⟨a, b⟩ := (allG env memoF n n (Nat.le_refl n)).2.2.2.2 _ _ _ _ _ _ hs' hml
    exact ⟨fun i hi => a.2.1 i hi, fun hl => by
      obtain ⟨i, h1, h2⟩ := b hl
      exact ⟨i, Classical.byContradiction fun h => h1 h, h2⟩⟩
  rcases h with ⟨ab, members, r, _, _, h3, _⟩ | ⟨ab, members, r, _, _, h3, _⟩
  · exact key members r h3
  · exact key members r h3

/-- **The pass loop of one component returns**, from a state with
`ChainInv`, when each run of `+run` returns and the identities of the graph
along every chain of passes lie in a finite list: `PassGrowG` is discharged. -/
theorem passLoop_returns_g (env : Env R) {memoF : Memo M} (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNorm memoF) (hmI : MemoNI memoF) (hrun : RunHalts env memoF) (id : Ident) (index : Nat)
    (rest : List Ident) (x : Nat × SkaState M R) (hc : ChainInv memoF id index rest x.2)
    (hI : ∀ f : Nat → Nat × SkaState M R, (∀ k, PassNextQ env memoF id index x (f (k + 1)) (f k)) →
      FinIdentsG f) :
    ∃ n r, passLoop env memoF n id index x.1 x.2 = some r := by
  refine passLoop_returns_runs env hmF hmT hmN hmI hrun id index rest x hc (finPushesQ_of_grow ?_ hI)
  intro a b hab
  obtain ⟨hr, m, _, hp⟩ := hab
  exact passGoOn_grow env memoF ((passReachQ_inv env hmF hmT hmN hmI hr hc).1.sg) hp

/-! ## 5. `FinIdentsG` from the push tree -/

/-- **`FinIdentsG` from a push tree**: if every identity of the graph at
every pass of the chain was in the graph at a base state `stb` or is reached
from `root` by `P`-steps, `P` branches finitely and has no infinite path from
`root`, the identities of the graph lie in one finite list (the keys of the
graph of `stb`, then what `root` reaches). -/
theorem finIdentsG_of_tree (stb : SkaState M R) (f : Nat → Nat × SkaState M R) (P : Ident → Ident → Prop)
    (root : Ident) (hfb : FinBranch P) (hreach : ∀ k i, GIn (f k).2 i → GIn stb i ∨ PReach P root i)
    (hpath : ¬ ∃ p : Nat → Ident, p 0 = root ∧ ∀ n, P (p n) (p (n + 1))) : FinIdentsG f := by
  by_cases hc : Covered P root
  · obtain ⟨I, hI⟩ := hc
    refine ⟨(Treap.tap stb.g).map (·.1) ++ I, fun k i hi => ?_⟩
    rcases hreach k i hi with h | h
    · apply List.mem_append_left
      cases e : Treap.get stb.g i with
      | none => exact absurd e h
      | some d => exact List.mem_map.mpr ⟨(i, d), (Treap.mem_tap _ _ _).mpr e, rfl⟩
    · exact List.mem_append_right _ (hI i h)
  · exact absurd (konig P hfb root hc) hpath

/-- **`FinIdentsG` from Kruskal**: `finIdents_of_kruskal` for the identities
of the graph, over the same ingredients (a push relation `P` that branches
finitely, formulas among finitely many, the `%he` guard past some point of a
path, `KruskalBT`), with every identity of the graph in the graph of `stb` or
reached from `root`. -/
theorem finIdentsG_of_kruskal {L : Type} (hK : KruskalBT) (ls : List L) (hls : ∀ a : L, a ∈ ls)
    (stb : SkaState M R) (f : Nat → Nat × SkaState M R) (P : Ident → Ident → Prop) (root : Ident)
    (sub : Ident → BT L) (hfb : FinBranch P)
    (hreach : ∀ k i, GIn (f k).2 i → GIn stb i ∨ PReach P root i)
    (hforms : ∃ Fs : List Nock.Noun, ∀ x, PReach P root x → x.2 ∈ Fs)
    (hguard : ∀ p : Nat → Ident, p 0 = root → (∀ n, P (p n) (p (n + 1))) →
      ∃ N, ∀ i j, N ≤ i → i < j → (p i).2 = (p j).2 → ¬ BTEmb (sub (p i)) (sub (p j))) :
    FinIdentsG f :=
  finIdentsG_of_tree stb f P root hfb hreach
    (noPath_of_kruskal hK ls hls P (fun x => x.2) sub root hforms hguard)

/-- **The pass loop of one component returns from `KruskalBT`**, `RunHalts`
and a push tree: a relation `P` that branches finitely (`FinBranch`), whose
formulas from `root` are among finitely many and obey the `%he` guard of
`+recursive-call` past some point of each path, and that reaches from `root`
every identity that enters the graph in the passes from `x`. -/
theorem passLoop_returns_k {L : Type} (hK : KruskalBT) (ls : List L) (hls : ∀ a : L, a ∈ ls)
    (env : Env R) {memoF : Memo M} (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNorm memoF) (hmI : MemoNI memoF) (hrun : RunHalts env memoF) (id : Ident) (index : Nat)
    (rest : List Ident) (x : Nat × SkaState M R) (hc : ChainInv memoF id index rest x.2)
    (P : Ident → Ident → Prop) (root : Ident) (sub : Ident → BT L) (hfb : FinBranch P)
    (hreach : ∀ y i, PassReachQ env memoF id index x y → GIn y.2 i → GIn x.2 i ∨ PReach P root i)
    (hforms : ∃ Fs : List Nock.Noun, ∀ x, PReach P root x → x.2 ∈ Fs)
    (hguard : ∀ p : Nat → Ident, p 0 = root → (∀ n, P (p n) (p (n + 1))) →
      ∃ N, ∀ i j, N ≤ i → i < j → (p i).2 = (p j).2 → ¬ BTEmb (sub (p i)) (sub (p j))) :
    ∃ n r, passLoop env memoF n id index x.1 x.2 = some r :=
  passLoop_returns_g env hmF hmT hmN hmI hrun id index rest x hc fun f hf =>
    finIdentsG_of_kruskal hK ls hls x.2 f P root sub hfb (fun k i hi => hreach (f k) i (hf k).1 hi)
      hforms hguard

end Ana
end SkaModel
end Formalization
