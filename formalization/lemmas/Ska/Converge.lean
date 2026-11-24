import lemmas.Ska.FolLoopRel
import lemmas.Ska.Prov

/-!
# A converged call graph: the table is right relative to its call sites

`rtab_of_answers`: if every answer of the table comes from the final graph
(`Answers`: an entry's own identity, a `+git:mi` or `%rec` hit patched for
the call's subject sock, or a `%he` generalization), then the table is
`RTab`, given what each entry gives on its own subjects:

* `LessRel`: the code requirement of an entry holds of every noun that fits
  it cut down to its own subject sock (true of an entry made by a run,
  `lessRel_of_run`);
* `ProdRel`: on every subject of its code requirement, the entry's product
  satisfies the provenance invariant and the static condition on its
  subject sock.  For an entry made by a run with a table that is `RTab`,
  this is `folLoop_relProd`; at convergence the table is made of the
  entries themselves, so `ProdRel` needs an induction on the runs of
  `+mink` (the fuel induction), which `ConvergeProd.lean` does
  (`prodRel_of_converged`).

`codeOK_of_converged`: from a converged graph, `CodeOK`, with `ProdRel`,
`CodeHas`, `CodeIs` and well-formed subject socks as the only assumptions
besides convergence.  `converged_agree`: the analysis output of an entry
then agrees with `+mink` on every subject of its code requirement.
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## Code requirements -/

/-- **The code requirement of a run, cut down to its own cape, is the code
requirement.** -/
theorem app_cape_fits : ∀ (W : Cape) (s : Sock) (lc : Cape) (dl : Noun) (o : Option Noun),
    Ca.app W s = Sock.mk lc dl → FitsOpt (Ca.app lc s) o → FitsOpt (Ca.app W s) o := by
  intro W
  induction W with
  | yes =>
    intro s lc dl o he h
    cases s with
    | void => rw [app_void] at he; cases he
    | mk cs d =>
      by_cases h3 : cs = Cape.no
      · subst h3
        rw [show Ca.app Cape.yes (Sock.mk Cape.no d) = Sock.dunno by simp [Ca.app]]
        exact fitsOpt_dunno o
      have e : Ca.app Cape.yes (Sock.mk cs d) = Sock.mk cs d := by simp [Ca.app, h3]
      rw [e] at he ⊢
      cases he
      rwa [app_self] at h
  | no =>
    intro s lc dl o he h
    cases s with
    | void => rw [app_void] at he; cases he
    | mk cs d => exact app_no_fitsOpt (by simp) o
  | cell wh wt ih1 ih2 =>
    intro s lc dl o he h
    cases s with
    | void => rw [app_void] at he; cases he
    | mk cs d =>
    by_cases h1 : Cape.cell wh wt = cs
    · subst h1; rw [app_self] at he ⊢; cases he; rwa [app_self] at h
    by_cases h3 : cs = Cape.no
    · subst h3; exact app_fitsOpt _ (fitsOpt_blank ⟨_, _, rfl, rfl⟩ o)
    have e : Ca.app (Cape.cell wh wt) (Sock.mk cs d) =
        So.knit (Ca.app wh (So.hed (Sock.mk cs d))) (Ca.app wt (So.tel (Sock.mk cs d))) := by
      simp [Ca.app, h1, h3]
    rw [e] at he ⊢
    have hA := app_ne_void wh (hed_ne_void (s := Sock.mk cs d) (by simp))
    have hB := app_ne_void wt (tel_ne_void (s := Sock.mk cs d) (by simp))
    obtain ⟨la, dA, hAe⟩ : ∃ la dA, Ca.app wh (So.hed (Sock.mk cs d)) = Sock.mk la dA := by
      cases h' : Ca.app wh (So.hed (Sock.mk cs d)) with
      | void => exact absurd h' hA
      | mk la dA => exact ⟨la, dA, rfl⟩
    obtain ⟨lb, dB, hBe⟩ : ∃ lb dB, Ca.app wt (So.tel (Sock.mk cs d)) = Sock.mk lb dB := by
      cases h' : Ca.app wt (So.tel (Sock.mk cs d)) with
      | void => exact absurd h' hB
      | mk lb dB => exact ⟨lb, dB, rfl⟩
    rw [hAe, hBe] at he
    by_cases hc : Ca.con la lb = Cape.no
    · rw [hAe, hBe]; simp only [So.knit, if_pos hc]; exact fitsOpt_dunno o
    have hlc : lc = Cape.cell la lb := by
      simp only [So.knit, if_neg hc] at he
      rw [con_ne_no hc] at he; cases he; rfl
    subst hlc
    by_cases h4 : Cape.cell la lb = cs
    · subst h4
      rw [app_self] at h
      exact knit_fitsOpt_of (app_fitsOpt _ (fitsOpt_hed h)) (app_fitsOpt _ (fitsOpt_tel h))
    have e2 : Ca.app (Cape.cell la lb) (Sock.mk cs d) =
        So.knit (Ca.app la (So.hed (Sock.mk cs d))) (Ca.app lb (So.tel (Sock.mk cs d))) := by
      simp [Ca.app, h4, h3]
    rw [e2] at h
    obtain ⟨p1, p2⟩ := knit_fitsOpt_inv h
    exact knit_fitsOpt_of (ih1 _ la dA _ hAe p1) (ih2 _ lb dB _ hBe p2)

/-! ## `+huge:so` -/

theorem hugeMk_fitsOpt {c1 c2 : Cape} {d1 d2 : Noun} {o : Option Noun}
    (h : So.hugeMk c1 d1 c2 d2 = some true) (hf : FitsOpt (Sock.mk c2 d2) o) :
    FitsOpt (Sock.mk c1 d1) o := by
  cases o with
  | none => exact ⟨_, _, rfl, hugeMk_blank d1 c1 c2 d2 h (by obtain ⟨_, _, e, hn⟩ := hf; cases e; exact hn)⟩
  | some n => exact hugeMk_sound d1 c1 c2 d2 n h hf

/-- **A hit's code requirement holds of every noun that fits it cut down to
the call's subject sock**, when the call's subject sock nests under it. -/
theorem huge_app_fits : ∀ (d1 : Noun) (c1 c2 : Cape) (d2 : Noun) (o : Option Noun),
    So.hugeMk c1 d1 c2 d2 = some true → FitsOpt (Ca.app c1 (Sock.mk c2 d2)) o →
    FitsOpt (Sock.mk c1 d1) o := by
  intro d1
  induction d1 with
  | atom k =>
    intro c1 c2 d2 o h hf
    rw [So.hugeMk.eq_def] at h
    split at h
    · rename_i he; obtain ⟨rfl, rfl⟩ := he; rwa [app_self] at hf
    · cases c1 with
      | cell _ _ => simp at h
      | no => exact fitsOpt_blank ⟨_, _, rfl, rfl⟩ o
      | yes =>
        simp only [Option.some.injEq, decide_eq_true_eq] at h
        obtain ⟨rfl, rfl⟩ := h
        rwa [app_self] at hf
  | cell d1h d1t ih1 ih2 =>
    intro c1 c2 d2 o h hf
    have hb := hugeMk_blank _ _ _ _ h
    by_cases h1 : c1 = c2
    · subst h1; rw [app_self] at hf; exact hugeMk_fitsOpt h hf
    by_cases hn1 : c1 = Cape.no
    · subst hn1; exact fitsOpt_blank ⟨_, _, rfl, rfl⟩ o
    by_cases hn2 : c2 = Cape.no
    · subst hn2; exact fitsOpt_blank ⟨_, _, rfl, hb rfl⟩ o
    rw [So.hugeMk.eq_def] at h
    split at h
    · rename_i he; exact absurd he.1 h1
    cases d2 with
    | atom _ =>
      simp only at h
      cases c2 with
      | cell _ _ => simp at h
      | yes => split at h <;> simp at h
      | no => exact absurd rfl hn2
    | cell d2h d2t =>
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨l, hl, h⟩ := h
      cases l with
      | false => simp at h
      | true =>
        simp only [if_true] at h
        cases c1 with
        | no => exact absurd rfl hn1
        | yes =>
          have e : Ca.app Cape.yes (Sock.mk c2 (C d2h d2t)) = Sock.mk c2 (C d2h d2t) := by
            simp [Ca.app, hn2]
          rw [e] at hf
          exact hugeMk_fitsOpt (c1 := Cape.yes) (d1 := C d1h d1t) (by
            rw [So.hugeMk.eq_def]; simp only [h1, false_and, if_false]; rw [hl]; simp [h]) hf
        | cell ch ct =>
          have e : Ca.app (Cape.cell ch ct) (Sock.mk c2 (C d2h d2t)) =
              So.knit (Ca.app ch (So.hed (Sock.mk c2 (C d2h d2t))))
                (Ca.app ct (So.tel (Sock.mk c2 (C d2h d2t)))) := by
            simp [Ca.app, h1, hn2]
          rw [e] at hf
          obtain ⟨p1, p2⟩ := knit_fitsOpt_inv hf
          have eh : So.hed (Sock.mk c2 (C d2h d2t)) = Sock.mk (Ca.hed c2) d2h := by
            cases c2 with
            | no => exact absurd rfl hn2
            | yes => rfl
            | cell _ _ => rfl
          have et : So.tel (Sock.mk c2 (C d2h d2t)) = Sock.mk (Ca.tel c2) d2t := by
            cases c2 with
            | no => exact absurd rfl hn2
            | yes => rfl
            | cell _ _ => rfl
          rw [eh] at p1
          rw [et] at p2
          exact fitsOpt_of_parts trivial (ih1 _ _ _ _ hl p1) (ih2 _ _ _ _ h p2)

theorem huge_less {e : Entry} {s : Sock} {lc : Cape} {dl : Noun} (hs : s ≠ Sock.void)
    (ht : hitTest e s = some true) (he : e.d.less = Sock.mk lc dl) {y : Noun}
    (hy : Fits (Ca.app lc s) y) : Fits e.d.less y := by
  simp only [hitTest, Option.bind_eq_some_iff] at ht
  obtain ⟨h1, hh, ht⟩ := ht
  cases h1 with
  | false => simp at ht
  | true =>
    rw [he] at hh ⊢
    cases s with
    | void => exact absurd rfl hs
    | mk cs d => exact huge_app_fits dl lc cs d (some y) hh hy

/-! ## `+patch-prod` keeps the invariant -/

/-- **A patched product keeps the provenance invariant** on a subject
of the entry's code requirement. -/
theorem provO_patchProd {y : Noun} {new : Sock} (hn : new ≠ Sock.void) :
    ∀ (σ : Noun) (S : Sock) (o : Option Noun), ProvO y S σ o →
      ProvO y (patchProd S σ new).sock (patchProd S σ new).src o := by
  intro σ
  induction σ with
  | atom a =>
    intro S o hp
    by_cases ha : a = 0
    · subst ha; rw [patchProd_zero]; exact hp
    rw [patchProd_atom new ha hp.nonvoid]
    obtain ⟨q, hq⟩ := axisPath_pos a (by omega)
    rw [pull_eq_sockAt (by omega) hq]
    refine ⟨sockAt_ne_void q hn, hp.exact, fun π e => ?_⟩
    rw [springAt_atom a π ha] at e
    injection e with e'
    exact absurd e' (pegPath_ne_zero a π ha)
  | cell h t ih1 ih2 =>
    intro S o hp
    rw [patchProd_cell new hp.nonvoid]
    exact provO_knit (ih1 _ _ (hp.part [false])) (ih2 _ _ (hp.part [true]))

/-! ## `+msg-sock` generalizes -/

theorem msgSock_genLe' : ∀ (k : Nat) (a b m : Sock), nsize a.data < k → a ≠ Sock.void →
    msgSock a b = some m → GenLe a m := by
  intro k
  induction k with
  | zero => intro _ _ _ h; omega
  | succ k ih =>
  intro a b m hk ha hm
  unfold msgSock at hm
  split at hm
  · cases hm; exact GenLe.refl _
  · split at hm
    · exact absurd rfl ha
    · cases hm; exact GenLe.refl _
    · rename_i ah aT ad1 ad2 bh bT bd1 bd2 _
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hm
      obtain ⟨h, hh, t, ht, rfl⟩ := hm
      simp only [Sock.data, nsize] at hk
      exact GenLe.knit (ih (Sock.mk ah ad1) _ _ (by simp only [Sock.data]; omega) (by simp) hh)
        (ih (Sock.mk aT ad2) _ _ (by simp only [Sock.data]; omega) (by simp) ht)
    · cases hm
    · cases hm; exact GenLe.no _ _

/-- **`+msg-sock` generalizes its first argument by forgetting.** -/
theorem msgSock_genLe {a b m : Sock} (ha : a ≠ Sock.void) (hm : msgSock a b = some m) : GenLe a m :=
  msgSock_genLe' _ a b m (Nat.lt_succ_self _) ha hm

/-- The static condition on a generalization of the subject sock holds on
the subject sock. -/
theorem StatOK.base {s m P : Sock} {σ : Noun} (hg : GenLe s m) (h : StatOK m P σ) : StatOK s P σ where
  stat := fun hne π b e hb =>
    let ⟨q, hq, h'⟩ := h.stat hne π b e hb
    ⟨q, hq, (hg.part q).trans h'⟩
  shape := h.shape

/-! ## The table of a converged run -/

/-- Every entry's code requirement holds of every noun that fits it cut
down to the entry's subject sock. -/
def LessRel (G : Entry → Prop) : Prop :=
  ∀ e lc dl, G e → e.d.less = Sock.mk lc dl → ∀ y, Fits (Ca.app lc e.more) y → Fits e.d.less y

/-- **The relative product soundness of the entries** (proved at
convergence in `ConvergeProd.lean`, `prodRel_of_converged`):
on every subject of its code requirement, an entry's product satisfies the
provenance invariant and the static condition on its subject sock. -/
def ProdRel (lib : Lib) (G : Entry → Prop) : Prop :=
  ∀ e, G e → ∀ y gul p, Fits e.d.less y → Mink lib gul [] y e.fol (Tone.zero p) →
    ProvR y e.d.prod e.d.map p ∧ StatOK e.more e.d.prod e.d.map

theorem answers_rel {lib : Lib} {G : Entry → Prop} (hL : LessRel G) (hP : ProdRel lib G)
    {s : Sock} {f : Noun} {a : TabEntry} (h : Answers G s f a) : s ≠ Sock.void →
    (∀ lc dl, a.less = Sock.mk lc dl → ∀ y, Fits (Ca.app lc s) y → Fits a.less y) ∧
    (∀ y gul p, Fits a.less y → Mink lib gul [] y f (Tone.zero p) →
      ProvR y a.prod a.map p ∧ StatOK s a.prod a.map) := by
  induction h with
  | exact he =>
    intro _
    exact ⟨fun lc dl hl y hy => hL _ lc dl he hl y hy, fun y gul p hy hm => hP _ he y gul p hy hm⟩
  | @hit e s he ht =>
    intro hs
    refine ⟨fun lc dl hl y hy => huge_less hs ht hl hy, fun y gul p hy hm => ?_⟩
    obtain ⟨hR, _⟩ := hP _ he y gul p hy hm
    exact ⟨provO_iff.mp (provO_patchProd hs _ _ _ (provO_iff.mpr hR)), statOK_patchProd _ _⟩
  | @hitGen e s s0 he ht hg =>
    intro hs0
    have hs : s ≠ Sock.void := fun e' => hs0 (hg.void_inv e')
    refine ⟨fun lc dl hl y hy => huge_less hs ht hl (hg.appFits lc (some y) hy), fun y gul p hy hm => ?_⟩
    obtain ⟨hR, _⟩ := hP _ he y gul p hy hm
    exact ⟨provO_iff.mp (provO_patchProd hs0 _ _ _ (provO_iff.mpr hR)), statOK_patchProd _ _⟩
  | @gen s s' m f a hm _ ih =>
    intro hs
    have hg := msgSock_genLe hs hm
    have hmv : m ≠ Sock.void := fun e => hs (hg.void_inv e)
    obtain ⟨i1, i2⟩ := ih hmv
    refine ⟨fun lc dl hl y hy => i1 lc dl hl y ?_, fun y gul p hy hmk => ?_⟩
    · have := hg.appFits lc (some y) hy
      exact this
    · obtain ⟨hR, hS⟩ := i2 y gul p hy hmk
      exact ⟨hR, hS.base hg⟩

/-- **The table of a converged run is right relative to its call sites.** -/
theorem rtab_of_answers {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} {G : Entry → Prop}
    (hL : LessRel G) (hP : ProdRel lib G) (hc : CodeHas code G)
    (hans : ∀ s f a, tab s f = some a → Answers G s f a) : RTab lib code tab where
  less := fun s f d lc dl h hs hl y hy => (answers_rel hL hP (hans s f d h) hs).1 lc dl hl y hy
  code := fun s f d h => answers_code hc (hans s f d h)
  prod := fun s f d h hs y gul p hy hm => (answers_rel hL hP (hans s f d h) hs).2 y gul p hy hm

/-- **A code requirement united with another cape restricts the subjects**:
a noun that fits `app:ca (uni:ca want w) s` fits `app:ca want s`, on a
well-formed sock. -/
theorem fits_app_uni {want w : Cape} {s : Sock} {x : Noun} (hwf : WellFormed s)
    (h : Fits (Ca.app (Ca.uni want w) s) x) : Fits (Ca.app want s) x :=
  app_mono_cape want (Ca.uni want w) s (some x) hwf (fun r hr => (uni_has want w r).mpr (Or.inl hr)) h

/-- With `WantSound`, an entry made by a run on a well-formed subject sock
satisfies `EntriesOK`: its code requirement, `want` united with a cape,
restricts the subjects of `app:ca want more` (`fits_app_uni`). -/
theorem entry_ok_of_run {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} {e : Entry}
    (hw : WantSound lib code tab) (hr : RunEntry tab e) (hwf : WellFormed e.more) :
    Annot lib code (Fits e.d.less) e.fol e.d.nomm := by
  obtain ⟨n, out, gen', h, hn, w, hl⟩ := hr
  rw [hn, hl]
  exact (hw n e.more e.fol out gen' h).mono (fun x hx => fits_app_uni hwf hx)

/-- An entry made by a run satisfies `LessRel`. -/
theorem lessRel_of_run {tab : Tab} {G : Entry → Prop} (hr : ∀ e, G e → RunEntry tab e) : LessRel G := by
  intro e lc dl he hl y hy
  obtain ⟨_, _, gen', _, _, w, hle⟩ := hr e he
  rw [hle] at hl ⊢
  exact app_cape_fits (Ca.uni gen'.want w) e.more lc dl (some y) hl hy

/-! ## `CodeOK` at convergence -/

/-- **A converged call graph gives `CodeOK`.**  Every entry is made by the
last run of `fol-loop` on its identity with the final table (`hr`), every
answer of the table comes from the graph (`hans`), the code table holds the
entries' nomms under their bells (`hc`, `hhas`), every entry's subject sock
is well formed (`hwf`), and the entries are right on products relative to
their code requirements (`hP`, the fuel induction, not done here). -/
theorem codeOK_of_converged {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} {G : Entry → Prop}
    (hr : ∀ e, G e → RunEntry tab e) (hans : ∀ s f a, tab s f = some a → Answers G s f a)
    (hc : CodeIs code G) (hhas : CodeHas code G) (hwf : ∀ e, G e → WellFormed e.more)
    (hP : ProdRel lib G) : CodeOK lib code := by
  have hT := rtab_of_answers (lessRel_of_run hr) hP hhas hans
  refine codeOK_of_entries hc fun e he => ?_
  obtain ⟨n, out, gen', h, hn, w, hl⟩ := hr e he
  rw [hn, hl]
  exact (folLoop_wantSound hT (hwf e he) h).mono (fun x hx => fits_app_uni (hwf e he) hx)

/-- **The analysis output of an entry of a converged graph agrees with
`+mink` on every subject of its code requirement**, under the assumptions
of `codeOK_of_converged`. -/
theorem converged_agree {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} {G : Entry → Prop}
    (hr : ∀ e, G e → RunEntry tab e) (hans : ∀ s f a, tab s f = some a → Answers G s f a)
    (hc : CodeIs code G) (hhas : CodeHas code G) (hwf : ∀ e, G e → WellFormed e.more)
    (hP : ProdRel lib G) {e : Entry} (he : G e) {x : Noun} (hx : Fits e.d.less x) (gul : Noun)
    (t : Trace) (r : Tone) :
    Mink lib gul t x e.fol r ↔ ∃ m, nommF lib gul code m t x e.d.nomm = some r := by
  have hok := codeOK_of_converged hr hans hc hhas hwf hP
  have hT := rtab_of_answers (lessRel_of_run hr) hP hhas hans
  obtain ⟨n, out, gen', h, hn, w, hl⟩ := hr e he
  rw [hl] at hx
  rw [hn]
  exact nomm_agree lib gul code hok (folLoop_wantSound hT (hwf e he) h) (fits_app_uni (hwf e he) hx) t r

/-! ## Where `ProdRel` comes from -/

/-- An entry made by a converged run whose product did not move: its
product sock and provenance are those of the run. -/
def RunEntryP (tab : Tab) (e : Entry) : Prop :=
  ∃ n out gen', folLoopTop tab n e.more e.fol = some (out, gen') ∧
    e.d.nomm = out.nomm ∧ (∃ w, e.d.less = Ca.app (Ca.uni gen'.want w) e.more) ∧
    e.d.prod = out.prod.sock ∧ e.d.map = out.prod.src

theorem RunEntryP.run {tab : Tab} {e : Entry} (h : RunEntryP tab e) : RunEntry tab e :=
  let ⟨n, out, gen', h1, h2, h3, _⟩ := h
  ⟨n, out, gen', h1, h2, h3⟩

/-- **`ProdRel` from a table that is right relative to its call sites.**
At convergence the table's `exact` answers are the entries themselves, so
this and `rtab_of_answers` only show that `ProdRel` and `RTab` follow from
each other; breaking the circle is the induction on the runs of `+mink`
that `ProdRel` still needs. -/
theorem prodRel_of_rtab {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} {G : Entry → Prop}
    (hT : RTab lib code tab) (hr : ∀ e, G e → RunEntryP tab e) (hwf : ∀ e, G e → WellFormed e.more) :
    ProdRel lib G := by
  intro e he y gul p hy hm
  obtain ⟨n, out, gen', h, _, ⟨w, hl⟩, hp, hmap⟩ := hr e he
  rw [hl] at hy
  rw [hp, hmap]
  exact folLoop_relProd hT (hwf e he) h (fits_app_uni (hwf e he) hy) hm

end SkaModel
end Formalization
