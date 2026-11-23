import lemmas.Ska.Stat

/-!
# `+app:ca` under a mask: the subject half of a call site

`sub_fits`: at a direct call in a function on the subject sock `bus`, the
call's subject `y'` satisfies the provenance invariant on a subject `X'` of
the code requirement `app:ca W bus`, with the static condition; if `W`
covers `distribute lc σ`, where `lc` is the cape of the callee's code
requirement and `σ` the provenance of the call's subject, then `y'` fits
`app:ca lc S`, the callee's code requirement cut down to what it uses of the
call's subject sock `S`.

`known_part'`: a part that the analysis knows fully is the same on every
subject of the code requirement, if `W` covers its provenance (`known_part`
of `AppPath.lean` for a part that may be absent, from `StatOK`).

The lemmas on `+app:ca` need the subject sock to be well formed
(`WellFormed`): no part is a cell cape over atom data that knows something.
Without it the subject half is false: on the sock `[[& |] 5]`, which no noun
fits, `+app:ca [& &]` knows nothing while `+app:ca [& |]` is the sock
itself.  `+app:ca` commutes with generalization (`GenLe.appFits`) without
any such condition, since a generalization's knits are well formed.
-/

namespace Formalization
namespace SkaModel

open Nock

/-- **A well-formed sock**: no part is a cell cape over atom data, unless it
knows nothing. -/
def WellFormed (S : Sock) : Prop :=
  ∀ ρ c1 c2 k, sockAt S ρ = Sock.mk (Cape.cell c1 c2) (A k) → (Cape.cell c1 c2).isNo = true

theorem WellFormed.part {S : Sock} (h : WellFormed S) (π : List Bool) : WellFormed (sockAt S π) :=
  fun ρ c1 c2 k e => h (π ++ ρ) c1 c2 k (by rw [sockAt_app]; exact e)

/-! ## Parts and wholes -/

theorem app_fitsOpt (c : Cape) {s : Sock} {o : Option Noun} (h : FitsOpt s o) :
    FitsOpt (Ca.app c s) o := by
  cases o with
  | none => exact app_blank c s h
  | some n => exact app_fits c s n h

theorem fitsOpt_hed {s : Sock} {o : Option Noun} (h : FitsOpt s o) : FitsOpt (So.hed s) (slotO o [false]) := by
  cases o with
  | none => exact hed_blank h
  | some n =>
    cases n with
    | cell a b => simpa [slotO, slotAtPath, FitsOpt] using hed_fits h
    | atom k =>
      cases s with
      | void => exact absurd h id
      | mk c d => simpa [slotO, slotAtPath, FitsOpt] using (hed_tel_blank_of_atom (k := k) h).1

theorem fitsOpt_tel {s : Sock} {o : Option Noun} (h : FitsOpt s o) : FitsOpt (So.tel s) (slotO o [true]) := by
  cases o with
  | none => exact tel_blank h
  | some n =>
    cases n with
    | cell a b => simpa [slotO, slotAtPath, FitsOpt] using tel_fits h
    | atom k =>
      cases s with
      | void => exact absurd h id
      | mk c d => simpa [slotO, slotAtPath, FitsOpt] using (hed_tel_blank_of_atom (k := k) h).2

theorem knit_fitsOpt_inv {A B : Sock} {o : Option Noun} (h : FitsOpt (So.knit A B) o) :
    FitsOpt A (slotO o [false]) ∧ FitsOpt B (slotO o [true]) := by
  cases A with
  | void => cases B <;> exact absurd h (fun h => fitsOpt_void_false h)
  | mk l d1 =>
    cases B with
    | void => exact absurd h (fun h => fitsOpt_void_false h)
    | mk r d2 =>
      simp only [So.knit] at h
      split at h
      · rename_i hc
        unfold Ca.con at hc
        split at hc
        · rename_i hh
          obtain ⟨rfl, rfl⟩ := hh
          exact ⟨fitsOpt_blank ⟨_, _, rfl, rfl⟩ _, fitsOpt_blank ⟨_, _, rfl, rfl⟩ _⟩
        · cases hc
      · rename_i hc
        rw [con_ne_no hc] at h
        cases o with
        | none =>
          obtain ⟨c, d, he, hn⟩ := h
          cases he
          simp only [Cape.isNo, Bool.and_eq_true] at hn
          exact ⟨⟨_, _, rfl, hn.1⟩, ⟨_, _, rfl, hn.2⟩⟩
        | some n =>
          simp only [FitsOpt, Fits, FitsCape] at h
          rcases h with hn | ⟨dh, dt, nh, nt, hd, rfl, hh, ht⟩
          · simp only [Bool.and_eq_true] at hn
            exact ⟨fitsOpt_blank ⟨_, _, rfl, hn.1⟩ _, fitsOpt_blank ⟨_, _, rfl, hn.2⟩ _⟩
          · cases hd
            exact ⟨by simpa [slotO, slotAtPath, FitsOpt, Fits] using hh,
              by simpa [slotO, slotAtPath, FitsOpt, Fits] using ht⟩

theorem knit_fitsOpt_of {A B : Sock} {o : Option Noun} (hA : FitsOpt A (slotO o [false]))
    (hB : FitsOpt B (slotO o [true])) : FitsOpt (So.knit A B) o := by
  cases o with
  | none => exact knit_blank hA hB
  | some n =>
    cases n with
    | cell a b =>
      exact knit_fits (by simpa [slotO, slotAtPath, FitsOpt] using hA)
        (by simpa [slotO, slotAtPath, FitsOpt] using hB)
    | atom k =>
      exact Sock.Blank.fits (knit_blank (by simpa [slotO, slotAtPath, FitsOpt] using hA)
        (by simpa [slotO, slotAtPath, FitsOpt] using hB)) _

theorem fitsOpt_of_app_yes {s : Sock} {o : Option Noun} (h : FitsOpt (Ca.app Cape.yes s) o) :
    FitsOpt s o := by
  cases s with
  | void => exact absurd h (fun h => fitsOpt_void_false (by rwa [app_void] at h))
  | mk cs d =>
    simp only [Ca.app] at h
    split at h
    · exact h
    · split at h
      · rename_i _ h2
        rcases h2 with h2 | h2
        · cases h2
        · subst h2; exact fitsOpt_blank ⟨_, _, rfl, rfl⟩ o
      · exact h

theorem app_self (c : Cape) (d : Noun) : Ca.app c (Sock.mk c d) = Sock.mk c d := by
  unfold Ca.app; simp

theorem app_no_fitsOpt {s : Sock} (hs : s ≠ Sock.void) (o : Option Noun) : FitsOpt (Ca.app Cape.no s) o := by
  cases s with
  | void => exact absurd rfl hs
  | mk cs d =>
    simp only [Ca.app]
    split
    · rename_i h; subst h; exact fitsOpt_blank ⟨_, _, rfl, rfl⟩ o
    · rw [if_pos (by simp)]; exact fitsOpt_dunno o

/-- What `+app:ca` says of a part, from what it says of the whole. -/
theorem app_parts (c : Cape) {T : Sock} {o : Option Noun} (h : FitsOpt (Ca.app c T) o) :
    FitsOpt (Ca.app (Ca.hed c) (So.hed T)) (slotO o [false]) ∧
      FitsOpt (Ca.app (Ca.tel c) (So.tel T)) (slotO o [true]) := by
  cases T with
  | void => exact absurd h (fun h => fitsOpt_void_false (by rwa [app_void] at h))
  | mk cs d =>
    have hT : ∀ (e : Ca.app c (Sock.mk cs d) = Sock.mk cs d), _ := fun e => by
      rw [e] at h
      exact (⟨app_fitsOpt _ (fitsOpt_hed h), app_fitsOpt _ (fitsOpt_tel h)⟩ :
        FitsOpt (Ca.app (Ca.hed c) (So.hed (Sock.mk cs d))) (slotO o [false]) ∧
          FitsOpt (Ca.app (Ca.tel c) (So.tel (Sock.mk cs d))) (slotO o [true]))
    by_cases h1 : c = cs
    · exact hT (by subst h1; exact app_self _ _)
    by_cases h2 : c = Cape.no
    · subst h2
      exact ⟨app_no_fitsOpt (hed_ne_void (by simp)) _, app_no_fitsOpt (tel_ne_void (by simp)) _⟩
    by_cases h3 : cs = Cape.no
    · subst h3
      exact ⟨app_fitsOpt _ (fitsOpt_blank (hed_blank ⟨_, _, rfl, rfl⟩) _),
        app_fitsOpt _ (fitsOpt_blank (tel_blank ⟨_, _, rfl, rfl⟩) _)⟩
    cases c with
    | no => exact absurd rfl h2
    | yes => exact hT (by simp [Ca.app, h1, h3])
    | cell ch ct =>
      have e : Ca.app (Cape.cell ch ct) (Sock.mk cs d) =
          So.knit (Ca.app ch (So.hed (Sock.mk cs d))) (Ca.app ct (So.tel (Sock.mk cs d))) := by
        simp [Ca.app, h1, h3]
      rw [e] at h
      exact knit_fitsOpt_inv h

/-- What `+app:ca` says of the whole, from what it says of the parts, on a
sock that may stand for a cell. -/
theorem app_of_parts (c : Cape) {K : Sock} {o : Option Noun} (hK : Cellish K)
    (hh : FitsOpt (Ca.app (Ca.hed c) (So.hed K)) (slotO o [false]))
    (ht : FitsOpt (Ca.app (Ca.tel c) (So.tel K)) (slotO o [true])) : FitsOpt (Ca.app c K) o := by
  match K, hK with
  | Sock.mk Cape.no d, _ => exact app_fitsOpt c (fitsOpt_blank ⟨_, _, rfl, rfl⟩ o)
  | Sock.mk Cape.yes (Noun.cell d1 d2), hK =>
    cases c with
    | no => exact app_no_fitsOpt (by simp) o
    | yes =>
      rw [app_self]
      exact fitsOpt_of_parts hK (by simpa [Ca.hed, So.hed, app_self] using hh)
        (by simpa [Ca.tel, So.tel, app_self] using ht)
    | cell ch ct =>
      have e : Ca.app (Cape.cell ch ct) (Sock.mk Cape.yes (C d1 d2)) =
          So.knit (Ca.app ch (So.hed (Sock.mk Cape.yes (C d1 d2))))
            (Ca.app ct (So.tel (Sock.mk Cape.yes (C d1 d2)))) := by simp [Ca.app]
      rw [e]; exact knit_fitsOpt_of hh ht
  | Sock.mk (Cape.cell c1 c2) (Noun.cell d1 d2), hK =>
    by_cases h1 : c = Cape.cell c1 c2
    · subst h1
      rw [app_self]
      exact fitsOpt_of_parts hK (by simpa [Ca.hed, So.hed, app_self] using hh)
        (by simpa [Ca.tel, So.tel, app_self] using ht)
    cases c with
    | no => exact app_no_fitsOpt (by simp) o
    | yes =>
      have e : Ca.app Cape.yes (Sock.mk (Cape.cell c1 c2) (C d1 d2)) = Sock.mk (Cape.cell c1 c2) (C d1 d2) := by
        simp [Ca.app]
      rw [e]
      exact fitsOpt_of_parts hK (fitsOpt_of_app_yes hh) (fitsOpt_of_app_yes ht)
    | cell ch ct =>
      have e : Ca.app (Cape.cell ch ct) (Sock.mk (Cape.cell c1 c2) (C d1 d2)) =
          So.knit (Ca.app ch (So.hed (Sock.mk (Cape.cell c1 c2) (C d1 d2))))
            (Ca.app ct (So.tel (Sock.mk (Cape.cell c1 c2) (C d1 d2)))) := by
        simp [Ca.app, h1]
      rw [e]; exact knit_fitsOpt_of hh ht

/-! ## Monotonicity of `+app:ca` -/

/-- **`+app:ca` commutes with generalization.** -/
theorem GenLe.appFits {T S : Sock} (h : GenLe T S) :
    ∀ c o, FitsOpt (Ca.app c T) o → FitsOpt (Ca.app c S) o := by
  induction h with
  | refl => exact fun _ _ h => h
  | no T d => intro c o _; exact app_fitsOpt c (fitsOpt_blank ⟨_, _, rfl, rfl⟩ o)
  | @knit T S1 S2 h1 h2 ih1 ih2 =>
    intro c o hf
    by_cases hv : S1 = Sock.void ∨ S2 = Sock.void
    · have hT : T = Sock.void := by
        rcases hv with e | e
        · exact hed_void_inv (h1.void_inv e)
        · exact tel_void_inv (h2.void_inv e)
      subst hT; rw [app_void] at hf; exact absurd hf (fun h => fitsOpt_void_false h)
    simp only [not_or] at hv
    obtain ⟨p1, p2⟩ := app_parts c hf
    have q1 := ih1 _ _ p1
    have q2 := ih2 _ _ p2
    rcases knit_parts hv.1 hv.2 with he | ⟨eh, et⟩
    · rw [he]; exact app_fitsOpt c (fitsOpt_dunno o)
    · apply app_of_parts c (knit_cellish hv.1 hv.2)
      · rw [eh]; exact q1
      · rw [et]; exact q2

/-- **A larger mask knows more**, on a well-formed sock. -/
theorem app_mono_cape : ∀ (c W : Cape) (s : Sock) (o : Option Noun), WellFormed s →
    (∀ r, c.Has r → W.Has r) → FitsOpt (Ca.app W s) o → FitsOpt (Ca.app c s) o := by
  intro c
  induction c with
  | no =>
    intro W s o _ _ hf
    cases s with
    | void => rw [app_void] at hf; exact absurd hf (fun h => fitsOpt_void_false h)
    | mk cs d => exact app_no_fitsOpt (by simp) o
  | yes =>
    intro W s o _ hc hf
    have := has_nil_yes (hc [] trivial)
    subst this; exact hf
  | cell ch ct ih1 ih2 =>
    intro W s o hwf hc hf
    cases s with
    | void => rw [app_void] at hf; exact absurd hf (fun h => fitsOpt_void_false h)
    | mk cs d =>
    -- what W says of the parts
    have hparts : FitsOpt (Ca.app ch (So.hed (Sock.mk cs d))) (slotO o [false]) ∧
        FitsOpt (Ca.app ct (So.tel (Sock.mk cs d))) (slotO o [true]) := by
      obtain ⟨p1, p2⟩ := app_parts W hf
      cases W with
      | no =>
        exact ⟨ih1 Cape.no _ _ (hwf.part [false]) (fun r h => hc (false :: r) h) p1,
          ih2 Cape.no _ _ (hwf.part [true]) (fun r h => hc (true :: r) h) p2⟩
      | yes => exact ⟨app_fitsOpt _ (fitsOpt_of_app_yes p1), app_fitsOpt _ (fitsOpt_of_app_yes p2)⟩
      | cell wh wt =>
        exact ⟨ih1 wh _ _ (hwf.part [false]) (fun r h => hc (false :: r) h) p1,
          ih2 wt _ _ (hwf.part [true]) (fun r h => hc (true :: r) h) p2⟩
    by_cases h1 : Cape.cell ch ct = cs
    · subst h1
      rw [app_self]
      cases d with
      | atom k => exact fitsOpt_blank ⟨_, _, rfl, hwf [] ch ct k rfl⟩ o
      | cell d1 d2 =>
        exact fitsOpt_of_parts trivial (by simpa [So.hed, app_self] using hparts.1)
          (by simpa [So.tel, app_self] using hparts.2)
    by_cases h3 : cs = Cape.no
    · subst h3; exact app_fitsOpt _ (fitsOpt_blank ⟨_, _, rfl, rfl⟩ o)
    have e : Ca.app (Cape.cell ch ct) (Sock.mk cs d) =
        So.knit (Ca.app ch (So.hed (Sock.mk cs d))) (Ca.app ct (So.tel (Sock.mk cs d))) := by
      simp [Ca.app, h1, h3]
    rw [e]
    exact knit_fitsOpt_of hparts.1 hparts.2

/-- **`+app:ca` below a path, under a mask**: below the path `q`, a noun of
`app:ca W s` fits `app:ca c` of what `s` knows there, for every mask `c`
that `W` covers at `q`.  `fitsOpt_app_part` is the case `c = &`. -/
theorem fitsOpt_app_mask : ∀ (q : List Bool) (W c : Cape) (s : Sock) (o : Option Noun), WellFormed s →
    (∀ r, c.Has r → W.Has (q ++ r)) → FitsOpt (sockAt (Ca.app W s) q) o →
    FitsOpt (Ca.app c (sockAt s q)) o := by
  intro q
  induction q with
  | nil => intro W c s o hwf hc h; exact app_mono_cape c W s o hwf (by simpa using hc) h
  | cons b q ih =>
    intro W c s o hwf hc h
    cases s with
    | void => rw [app_void, sockAt_void] at h; exact absurd h (fun h => fitsOpt_void_false h)
    | mk cs d =>
    by_cases h1 : W = cs
    · subst h1; rw [app_self] at h; exact app_fitsOpt c h
    by_cases h3 : cs = Cape.no
    · subst h3
      exact app_fitsOpt c (fitsOpt_blank (sockAt_blank _ ⟨_, _, rfl, rfl⟩) o)
    cases W with
    | no =>
      exact app_mono_cape c Cape.no _ o (hwf.part _) (fun r h => absurd (hc r h) id)
        (app_no_fitsOpt (sockAt_ne_void _ (by simp)) o)
    | yes =>
      have e : Ca.app Cape.yes (Sock.mk cs d) = Sock.mk cs d := by simp [Ca.app, h3]
      rw [e] at h; exact app_fitsOpt c h
    | cell wh wt =>
      have e : Ca.app (Cape.cell wh wt) (Sock.mk cs d) =
          So.knit (Ca.app wh (So.hed (Sock.mk cs d))) (Ca.app wt (So.tel (Sock.mk cs d))) := by
        simp [Ca.app, h1, h3]
      rw [e] at h
      have hA := app_ne_void wh (hed_ne_void (s := Sock.mk cs d) (by simp))
      have hB := app_ne_void wt (tel_ne_void (s := Sock.mk cs d) (by simp))
      rcases knit_parts hA hB with hk | ⟨eh, et⟩
      · -- the knit knows nothing: neither do its parts
        have hb : (So.knit (Ca.app wh (So.hed (Sock.mk cs d))) (Ca.app wt (So.tel (Sock.mk cs d)))).Blank := by
          rw [hk]; exact dunno_blank
        obtain ⟨b1, b2⟩ := knit_blank_inv hb
        apply fitsOpt_blank
        cases b
        · exact ih wh c _ none (hwf.part [false]) (fun r h => hc r h) (sockAt_blank q b1)
        · exact ih wt c _ none (hwf.part [true]) (fun r h => hc r h) (sockAt_blank q b2)
      · cases b
        · have h' : FitsOpt (sockAt (So.hed (So.knit _ _)) q) o := h
          rw [eh] at h'
          exact ih wh c _ o (hwf.part [false]) (fun r h => hc r h) h'
        · have h' : FitsOpt (sockAt (So.tel (So.knit _ _)) q) o := h
          rw [et] at h'
          exact ih wt c _ o (hwf.part [true]) (fun r h => hc r h) h'

/-! ## The subject half of a call site -/

theorem distribute_no : ∀ (s : Noun), distribute Cape.no s = Cape.no
  | Noun.atom 0 => rfl
  | Noun.atom (_ + 1) => by simp [distribute]
  | Noun.cell _ _ => by simp [distribute]

theorem distribute_hed (c : Cape) (h t : Noun) (q : List Bool) (hq : (distribute (Ca.hed c) h).Has q) :
    (distribute c (C h t)).Has q := by
  cases c with
  | no => rw [show Ca.hed Cape.no = Cape.no from rfl, distribute_no] at hq; exact absurd hq id
  | yes => simp only [distribute]; rw [if_neg (by simp), uni_has]; exact Or.inl hq
  | cell p r => simp only [distribute]; rw [if_neg (by simp), uni_has]; exact Or.inl hq

theorem distribute_tel (c : Cape) (h t : Noun) (q : List Bool) (hq : (distribute (Ca.tel c) t).Has q) :
    (distribute c (C h t)).Has q := by
  cases c with
  | no => rw [show Ca.tel Cape.no = Cape.no from rfl, distribute_no] at hq; exact absurd hq id
  | yes => simp only [distribute]; rw [if_neg (by simp), uni_has]; exact Or.inr hq
  | cell p r => simp only [distribute]; rw [if_neg (by simp), uni_has]; exact Or.inr hq

/-- **The subject half of a call site.**  The call's subject `y'`
satisfies the invariant on a subject `X'` of `app:ca W bus` with the sock
`S` and the provenance `σ`, and `[S σ]` the static condition; `bus` is well
formed.  Then for every mask `lc` whose `distribute` along `σ` the code
requirement `W` covers, `y'` fits `app:ca lc S`. -/
theorem sub_fits {X' : Noun} {o : Option Noun} {bus S : Sock} {σ : Noun} {W : Cape}
    (hp : ProvO X' S σ o) (hst : StatOK bus S σ) (hwf : WellFormed bus)
    (hX : Fits (Ca.app W bus) X') :
    ∀ σ' π c, springAt σ π = σ' → (∀ q, (distribute c σ').Has q → W.Has q) →
      FitsOpt (Ca.app c (sockAt S π)) (slotO o π) := by
  intro σ'
  induction σ' with
  | atom b =>
    intro π c e hW
    by_cases hb : b = 0
    · subst hb
      exact app_fitsOpt c (hp.const π e)
    · obtain ⟨q, hq, hg⟩ := hst.stat hp.nonvoid π b e hb
      rw [hp.exact π b e hb]
      have h1 : FitsOpt (sockAt (Ca.app W bus) q) (slotO (some X') q) := fitsOpt_sockAt q hX
      have h2 := fitsOpt_app_mask q W c bus _ hwf
        (fun r hr => hW _ (distribute_has (A b) c [] r b q (by simpa using hr) rfl hb hq)) h1
      have h3 := hg.appFits c _ h2
      simpa [slot?, hq, slotO] using h3
  | cell h t ih1 ih2 =>
    intro π c e hW
    have hc := hst.shape hp.nonvoid π (by rw [e]; rfl)
    apply app_of_parts c hc
    · have := ih1 (π ++ [false]) (Ca.hed c) (by rw [springAt_app, e]; rfl)
        (fun q hq => hW q (distribute_hed c h t q hq))
      rw [sockAt_app, slotO_app] at this
      exact this
    · have := ih2 (π ++ [true]) (Ca.tel c) (by rw [springAt_app, e]; rfl)
        (fun q hq => hW q (distribute_tel c h t q hq))
      rw [sockAt_app, slotO_app] at this
      exact this

/-- The call's subject fits the callee's code requirement cut down to the
call's subject sock. -/
theorem call_sub_fits {X' y' : Noun} {bus S : Sock} {σ : Noun} {W lc : Cape}
    (hp : ProvO X' S σ (some y')) (hst : StatOK bus S σ) (hwf : WellFormed bus)
    (hX : Fits (Ca.app W bus) X') (hW : ∀ q, (distribute lc σ).Has q → W.Has q) :
    Fits (Ca.app lc S) y' := by
  have := sub_fits hp hst hwf hX σ [] lc rfl hW
  simpa [slotO, sockAt, FitsOpt, slotAtPath] using this

/-! ## Known parts -/

/-- **A part that the analysis knows fully is the same on every subject of
the code requirement**, for a part that may be absent, from the static
condition. -/
theorem known_part' {x : Noun} {o : Option Noun} {bus S : Sock} {σ : Noun} {W : Cape}
    (hp : ProvO x S σ o) (hst : StatOK bus S σ) (hX : Fits (Ca.app W bus) x) (π0 : List Bool)
    (hW : ∀ q, (distribute Cape.yes (springAt σ π0)).Has q → W.Has q) :
    ∀ σ' ρ F, springAt σ (π0 ++ ρ) = σ' → sockAt S (π0 ++ ρ) = Sock.mk Cape.yes F →
      slotO o (π0 ++ ρ) = some F := by
  intro σ'
  induction σ' with
  | atom b =>
    intro ρ F e hs
    by_cases hb : b = 0
    · subst hb
      have := hp.const _ e
      rw [hs] at this
      exact fitsOpt_yes this
    · obtain ⟨q, hq, hg⟩ := hst.stat hp.nonvoid _ b e hb
      have hx := hp.exact _ b e hb
      have h1 : FitsOpt (sockAt (Ca.app W bus) q) (slotO (some x) q) := fitsOpt_sockAt q hX
      have e' : springAt (springAt σ π0) ρ = A b := by rw [← springAt_app]; exact e
      have h2 := fitsOpt_app_part q W bus _
        (fun r => hW _ (distribute_has (springAt σ π0) Cape.yes ρ r b q trivial e' hb hq)) h1
      have h3 := hg.toPosLe [] _ h2
      rw [show sockAt (sockAt S (π0 ++ ρ)) [] = sockAt S (π0 ++ ρ) from rfl, hs] at h3
      have h4 := fitsOpt_yes h3
      rw [hx]
      simpa [slot?, hq, slotO] using h4
  | cell h t ih1 ih2 =>
    intro ρ F e hs
    have hc := hst.shape hp.nonvoid _ (by rw [e]; rfl)
    rw [hs] at hc
    cases F with
    | atom _ => exact absurd hc id
    | cell F1 F2 =>
      have a1 := ih1 (ρ ++ [false]) F1 (by rw [← List.append_assoc, springAt_app, e]; rfl)
        (by rw [← List.append_assoc, sockAt_app, hs]; rfl)
      have a2 := ih2 (ρ ++ [true]) F2 (by rw [← List.append_assoc, springAt_app, e]; rfl)
        (by rw [← List.append_assoc, sockAt_app, hs]; rfl)
      rw [← List.append_assoc, slotO_app] at a1 a2
      exact slotO_eq_cell a1 a2

/-- The case of `known_part'` at the path where the sock knows the part. -/
theorem known_at {x : Noun} {o : Option Noun} {bus S : Sock} {σ : Noun} {W : Cape} {F : Noun}
    (hp : ProvO x S σ o) (hst : StatOK bus S σ) (hX : Fits (Ca.app W bus) x) (π : List Bool)
    (hW : ∀ q, (distribute Cape.yes (springAt σ π)).Has q → W.Has q)
    (hs : sockAt S π = Sock.mk Cape.yes F) : slotO o π = some F := by
  have := known_part' hp hst hX π hW (springAt σ π) [] F (by simp) (by simpa using hs)
  simpa using this

end SkaModel
end Formalization
