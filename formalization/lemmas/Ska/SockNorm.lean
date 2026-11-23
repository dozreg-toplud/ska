import lemmas.Ska.RunStep

/-!
# Normal capes: no cell of a cape knows nothing

`+axe-in-less-cape` of `+comp` reads a cell cape as "the axis exists", so the
compilation track assumes of a bell's cape that it has no cell whose two
halves both know nothing (`[| |]`, or deeper cells of such).  `+con:ca` and
`+knit:so` normalize such a cell to `|`.  `NormCape` is that condition; it is
the same as `CapeNorm` of `CompTopOK.lean` (same clauses), stated here so that
the analysis files do not import the compilation track.  `NormSock` is
`NormCape` of the cape of a sock (`%void` is normal).

Here: every cape and sock operation of the analysis keeps it: `+con:ca`,
`+uni:ca`, `+int:ca`, `+lack:ca`, `+dif:ca`, `+pat:ca`, `+msg-ca`,
`+knit:so`, `+hed:so`, `+tel:so`, `+pull:so`, `+darn:so`, `+purr:so`,
`+app:ca` (whatever the mask), `+double-int`, `+msg-anno`, `+msg-sock`,
`+patch-prod`, the product of an autocons, the merge of `+run`, and the datum
`+run` writes (`runDatum_norm`).  The root sock `&+sub` of a poke is normal.
-/

namespace Formalization
namespace SkaModel

open Nock

/-- **A normal cape**: no cell knows nothing (`[| |]` is normalized to `|`). -/
def NormCape : Cape → Prop
  | Cape.cell h t => (h.isNo && t.isNo) = false ∧ NormCape h ∧ NormCape t
  | _ => True

/-- A normal sock: its cape is normal. -/
def NormSock : Sock → Prop
  | Sock.void => True
  | Sock.mk c _ => NormCape c

theorem normCape_yes : NormCape Cape.yes := trivial
theorem normCape_no : NormCape Cape.no := trivial
theorem normSock_void : NormSock Sock.void := trivial
theorem normSock_dunno : NormSock Sock.dunno := trivial
theorem normSock_yes (d : Noun) : NormSock (Sock.mk Cape.yes d) := trivial

theorem NormCape.hed {h t : Cape} (n : NormCape (Cape.cell h t)) : NormCape h := n.2.1
theorem NormCape.tel {h t : Cape} (n : NormCape (Cape.cell h t)) : NormCape t := n.2.2

/-- A normal cape that knows nothing is `|`. -/
theorem NormCape.eq_no {c : Cape} (n : NormCape c) (h : c.isNo = true) : c = Cape.no := by
  cases c with
  | yes => simp [Cape.isNo] at h
  | no => rfl
  | cell a b =>
    have h1 : (a.isNo && b.isNo) = false := n.1
    simp only [Cape.isNo] at h
    rw [h] at h1; cases h1

/-! ## `+ca` -/

theorem normCape_con {h t : Cape} (hh : NormCape h) (ht : NormCape t) : NormCape (Ca.con h t) := by
  unfold Ca.con
  split
  · exact normCape_no
  · rename_i hn
    refine ⟨?_, hh, ht⟩
    cases e1 : h.isNo <;> cases e2 : t.isNo <;> simp
    exact hn ⟨hh.eq_no e1, ht.eq_no e2⟩

theorem normCape_hed {c : Cape} (h : NormCape c) : NormCape (Ca.hed c) := by
  cases c with
  | cell a b => exact h.hed
  | _ => exact h

theorem normCape_tel {c : Cape} (h : NormCape c) : NormCape (Ca.tel c) := by
  cases c with
  | cell a b => exact h.tel
  | _ => exact h

theorem normCape_uni : ∀ {a b : Cape}, NormCape a → NormCape b → NormCape (Ca.uni a b)
  | a, b, ha, hb => by
    unfold Ca.uni
    split
    · exact ha
    · split
      · exact normCape_yes
      · exact hb
      · exact normCape_yes
      · exact ha
      · exact normCape_con (normCape_uni ha.hed hb.hed) (normCape_uni ha.tel hb.tel)

theorem normCape_int : ∀ {a b : Cape}, NormCape a → NormCape b → NormCape (Ca.int a b)
  | a, b, ha, hb => by
    unfold Ca.int
    split
    · exact ha
    · split
      · exact normCape_no
      · exact hb
      · exact normCape_no
      · exact ha
      · exact normCape_con (normCape_int ha.hed hb.hed) (normCape_int ha.tel hb.tel)

theorem normCape_lack : ∀ {a b : Cape}, NormCape a → NormCape (Ca.lack a b)
  | a, b, ha => by
    unfold Ca.lack
    split
    · exact normCape_no
    · exact normCape_no
    · exact ha
    · split
      · exact normCape_no
      · exact normCape_con (normCape_lack (normCape_hed ha)) (normCape_lack (normCape_tel ha))

theorem normCape_dif : ∀ {a b c : Cape}, NormCape a → Ca.dif a b = some c → NormCape c
  | a, b, c, ha, h => by
    unfold Ca.dif at h
    split at h
    · cases h; exact normCape_no
    · split at h
      all_goals first
        | (simp only [Option.some.injEq] at h; subst h; first | exact normCape_no | exact ha)
        | (simp at h; done)
        | (simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, bind] at h
           obtain ⟨l, hl, r, hr, rfl⟩ := h
           exact normCape_con (normCape_dif ha.hed hl) (normCape_dif ha.tel hr))

theorem normCape_patLoop (c : Cape) (hc : c ≠ Cape.no) (hn : NormCape c) :
    ∀ a, NormCape (Ca.patLoop c a) ∧ Ca.patLoop c a ≠ Cape.no := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
  rw [Ca.patLoop]
  split
  · exact ⟨hn, hc⟩
  · have ih' := ih (mas a) (mas_lt a (by omega))
    have hk : (Ca.patLoop c (mas a)).isNo = false := by
      cases e : (Ca.patLoop c (mas a)).isNo
      · rfl
      · exact absurd (ih'.1.eq_no e) ih'.2
    split
    · exact ⟨⟨by simp [hk], ih'.1, normCape_no⟩, by simp⟩
    · exact ⟨⟨by simp [hk], normCape_no, ih'.1⟩, by simp⟩

theorem normCape_pat {c c' : Cape} {a : Nat} (hn : NormCape c) (h : Ca.pat c a = some c') : NormCape c' := by
  unfold Ca.pat at h
  split at h
  · cases h
  · split at h
    · cases h; exact normCape_no
    · cases h; exact (normCape_patLoop c ‹_› hn a).1

/-- `+msg-ca` of two normal capes is normal: where they differ it is `&` or a
cell that knows something. -/
theorem normCape_msgCa : ∀ {a b : Cape}, NormCape a → NormCape b → NormCape (msgCa a b) ∧ (a ≠ b → (msgCa a b).isNo = false)
  | a, b, ha, hb => by
    unfold msgCa
    split
    · rename_i e; exact ⟨ha, fun h => absurd e h⟩
    · rename_i hne
      split
      · rename_i ah aT bh bT
        have i1 := normCape_msgCa ha.hed hb.hed
        have i2 := normCape_msgCa ha.tel hb.tel
        have hk : ((msgCa ah bh).isNo && (msgCa aT bT).isNo) = false := by
          by_cases e1 : ah = bh
          · have e2 : aT ≠ bT := fun e2 => hne (by rw [e1, e2])
            simp [i2.2 e2]
          · simp [i1.2 e1]
        exact ⟨⟨hk, i1.1, i2.1⟩, fun _ => by simpa [Cape.isNo] using hk⟩
      · exact ⟨normCape_yes, fun _ => rfl⟩

/-! ## `+so` -/

theorem normSock_knit {S1 S2 : Sock} (h1 : NormSock S1) (h2 : NormSock S2) : NormSock (So.knit S1 S2) := by
  cases S1 with
  | void => exact normSock_void
  | mk l d1 =>
  cases S2 with
  | void => exact normSock_void
  | mk r d2 =>
  simp only [So.knit]
  split
  · exact normSock_dunno
  · exact normCape_con h1 h2

theorem normSock_hed {S : Sock} (h : NormSock S) : NormSock (So.hed S) := by
  cases S with
  | void => exact normSock_void
  | mk c d =>
    cases c <;> cases d <;> first | exact normSock_dunno | exact normSock_yes _ | exact h.hed

theorem normSock_tel {S : Sock} (h : NormSock S) : NormSock (So.tel S) := by
  cases S with
  | void => exact normSock_void
  | mk c d =>
    cases c <;> cases d <;> first | exact normSock_dunno | exact normSock_yes _ | exact h.tel

theorem normSock_pullLoop : ∀ (axe : Nat) (c : Cape) (d : Noun), NormCape c → NormSock (So.pullLoop c d axe) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
  intro c d hc
  rw [So.pullLoop.eq_def]
  split
  · exact hc
  · split
    · exact normSock_dunno
    · split
      · exact normSock_dunno
      · split
        · split
          · exact ih _ (mas_lt axe (by omega)) _ _ hc.hed
          · exact ih _ (mas_lt axe (by omega)) _ _ hc.tel
        · split
          · exact ih _ (mas_lt axe (by omega)) _ _ hc
          · exact ih _ (mas_lt axe (by omega)) _ _ hc

theorem normSock_pull {S s : Sock} {a : Nat} (h : NormSock S) (hp : So.pull S a = some s) : NormSock s := by
  unfold So.pull at hp
  split at hp
  · cases hp
  · split at hp
    · cases hp; exact normSock_void
    · cases hp; exact normSock_pullLoop a _ _ h

theorem normSock_darnUp : ∀ (acc : List (Nat × Sock)) (two : Sock), NormSock two →
    (∀ p ∈ acc, NormSock p.2) → NormSock (So.darnUp two acc)
  | [], two, h, _ => h
  | (n, s) :: acc, two, h, ha => by
    have hs : NormSock s := ha (n, s) (by simp)
    have ht : ∀ p ∈ acc, NormSock p.2 := fun p hp => ha p (by simp [hp])
    rw [darnUp_eq]
    split
    · exact normSock_darnUp _ _ (normSock_knit h hs) ht
    · exact normSock_darnUp _ _ (normSock_knit hs h) ht

theorem normSock_darnDown : ∀ (ax : Nat) (one two : Sock) (acc : List (Nat × Sock)) (s : Sock),
    NormSock one → NormSock two → (∀ p ∈ acc, NormSock p.2) →
    So.darnDown one ax two acc = some s → NormSock s := by
  intro ax
  induction ax using Nat.strongRecOn with
  | _ ax ih =>
  intro one two acc s h1 h2 ha hd
  rw [So.darnDown] at hd
  split at hd
  · cases hd; exact normSock_darnUp acc two h2 ha
  · split at hd
    · cases hd
    · split at hd
      · exact ih (mas ax) (mas_lt ax (by omega)) _ _ _ _ (normSock_hed h1) h2
          (fun p hp => by
            simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact normSock_tel h1
            · exact ha p hp) hd
      · exact ih (mas ax) (mas_lt ax (by omega)) _ _ _ _ (normSock_tel h1) h2
          (fun p hp => by
            simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact normSock_hed h1
            · exact ha p hp) hd

theorem normSock_darn {one two s : Sock} {ax : Nat} (h1 : NormSock one) (h2 : NormSock two)
    (hd : So.darn one ax two = some s) : NormSock s := by
  unfold So.darn at hd
  split at hd
  · cases hd; exact h2
  · split at hd
    · cases hd; exact normSock_void
    · split at hd
      · cases hd; exact normSock_dunno
      · exact normSock_darnDown ax one two [] s h1 h2 (by simp) hd

theorem normSock_purrData (d1 d2 : Noun) : NormSock (So.purrData d1 d2) := by
  fun_induction So.purrData d1 d2 with
  | case1 => exact normSock_yes _
  | case2 _ _ _ _ _ ih1 ih2 => exact normSock_knit ih1 ih2
  | case3 => exact normSock_dunno

theorem normSock_purr (one two : Sock) (h1 : NormSock one) (h2 : NormSock two) :
    NormSock (So.purr one two) := by
  fun_induction So.purr one two with
  | case1 => exact h1
  | case2 => exact h2
  | case3 => exact h1
  | case4 => exact normSock_dunno
  | case5 => exact normSock_purrData _ _
  | case6 _ _ _ _ _ _ _ ih1 ih2 =>
    exact normSock_knit (ih1 (normSock_hed h1) (normSock_hed h2)) (ih2 (normSock_tel h1) (normSock_tel h2))
  | case7 _ _ _ _ _ _ _ _ ih1 ih2 =>
    exact normSock_knit (ih1 (normSock_hed h1) (normSock_hed h2)) (ih2 (normSock_tel h1) (normSock_tel h2))
  | case8 => exact normSock_dunno

/-- **`+app:ca` keeps a normal sock normal, whatever the mask.** -/
theorem normSock_app : ∀ (c : Cape) (s : Sock), NormSock s → NormSock (Ca.app c s)
  | c, s, h => by
    unfold Ca.app
    split
    · exact normSock_void
    · split
      · exact h
      · split
        · exact normSock_dunno
        · split
          · exact h
          · exact normSock_knit (normSock_app _ _ (normSock_hed h)) (normSock_app _ _ (normSock_tel h))
          · exact h

/-! ## The merges and the products -/

theorem normSock_doubleInt' : ∀ (k : Nat) (a b : Anno), Sock.msr a.sock + Sock.msr b.sock < k →
    NormSock a.sock → NormSock b.sock → NormSock (doubleInt a b).sock := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk ha hb
  by_cases hab : a = b
  · subst hab; rw [doubleInt_self]; exact ha
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  cases sa with
  | void => rw [doubleInt_void_left rfl hab]; exact hb
  | mk ca da =>
  cases sb with
  | void => rw [doubleInt_void_right rfl (by simp) hab]; exact ha
  | mk cb db =>
    apply doubleInt_cases (fun r => NormSock r.sock) hab normSock_dunno
    intro hno
    simp only [not_or] at hno
    have h1 : Sock.msr (So.hed (Sock.mk ca da)) + Sock.msr (So.hed (Sock.mk cb db)) < k := by
      have := msr_hed_lt hno.1 da; have := msr_hed_lt hno.2 db; simp only at hk; omega
    have h2 : Sock.msr (So.tel (Sock.mk ca da)) + Sock.msr (So.tel (Sock.mk cb db)) < k := by
      have := msr_tel_lt hno.1 da; have := msr_tel_lt hno.2 db; simp only at hk; omega
    exact normSock_knit (ih _ _ h1 (normSock_hed ha) (normSock_hed hb)) (ih _ _ h2 (normSock_tel ha) (normSock_tel hb))

theorem normSock_doubleInt {a b : Anno} (ha : NormSock a.sock) (hb : NormSock b.sock) :
    NormSock (doubleInt a b).sock :=
  normSock_doubleInt' _ a b (Nat.lt_succ_self _) ha hb

theorem normSock_msgAnno (a b : Anno) (ha : NormSock a.sock) (hb : NormSock b.sock) :
    NormSock (msgAnno a b).sock := by
  fun_induction msgAnno a b with
  | case1 => exact ha
  | case2 => exact hb
  | case3 => exact ha
  | case4 _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    exact normSock_knit (ih1 (normSock_hed ha) (normSock_hed hb)) (ih2 (normSock_tel ha) (normSock_tel hb))
  | case5 => exact normSock_dunno

theorem normSock_mergeProd (moved : Bool) {a b : Anno} (ha : NormSock a.sock) (hb : NormSock b.sock) :
    NormSock (mergeProd moved a b).sock := by
  unfold mergeProd
  split
  · exact normSock_msgAnno a b ha hb
  · exact normSock_doubleInt ha hb

theorem normSock_msgSock' : ∀ (k : Nat) (a b m : Sock), nsize a.data < k → NormSock a → NormSock b →
    msgSock a b = some m → NormSock m := by
  intro k
  induction k with
  | zero => intro _ _ _ h; omega
  | succ k ih =>
  intro a b m hk ha hb hm
  unfold msgSock at hm
  split at hm
  · cases hm; exact ha
  · split at hm
    · cases hm; exact hb
    · cases hm; exact ha
    · rename_i ah aT ad1 ad2 bh bT bd1 bd2 _
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hm
      obtain ⟨h, hh, t, ht, rfl⟩ := hm
      simp only [Sock.data, nsize] at hk
      exact normSock_knit (ih (Sock.mk ah ad1) _ _ (by simp only [Sock.data]; omega) (normSock_hed ha) (normSock_hed hb) hh)
        (ih (Sock.mk aT ad2) _ _ (by simp only [Sock.data]; omega) (normSock_tel ha) (normSock_tel hb) ht)
    · cases hm
    · cases hm; exact normSock_dunno

/-- **`+msg-sock` keeps normal socks normal.** -/
theorem normSock_msgSock {a b m : Sock} (ha : NormSock a) (hb : NormSock b) (hm : msgSock a b = some m) :
    NormSock m :=
  normSock_msgSock' _ a b m (Nat.lt_succ_self _) ha hb hm

/-- **`+patch-prod` keeps normal socks normal.** -/
theorem normSock_patchProd {new : Sock} (hn : NormSock new) :
    ∀ (σ : Noun) (S : Sock), NormSock S → NormSock (patchProd S σ new).sock := by
  intro σ
  induction σ with
  | atom a =>
    intro S hS
    by_cases ha : a = 0
    · subst ha; rw [patchProd_zero]; exact hS
    by_cases hv : S = Sock.void
    · subst hv; rw [patchProd]; simp only [if_neg (by simp [ha] : ¬ A a = A 0), if_true]; exact normSock_void
    rw [patchProd_atom new ha hv]
    cases hp : So.pull new a with
    | none => exact normSock_void
    | some s' => exact normSock_pull hn hp
  | cell h t ih1 ih2 =>
    intro S hS
    by_cases hv : S = Sock.void
    · subst hv; rw [patchProd]; simp; exact normSock_void
    rw [patchProd_cell new hv]
    exact normSock_knit (ih1 _ (normSock_hed hS)) (ih2 _ (normSock_tel hS))

theorem normSock_patchDatum {d : Datum} {s : Sock} (hd : NormSock d.prod) (hs : NormSock s) :
    NormSock (patchDatum d s).prod :=
  normSock_patchProd hs d.map d.prod hd

theorem normSock_consProd {l r : FolOut} (hl : NormSock l.prod.sock) (hr : NormSock r.prod.sock) :
    NormSock (consProd l r).1.sock := by
  unfold consProd
  split
  · exact normSock_yes _
  · exact normSock_knit hl hr

/-- **The datum `+run` writes**: its code requirement `app:ca want bus` is
normal for a normal `bus`, and its product for normal products. -/
theorem runDatum_norm {moved : Bool} {bus : Sock} {out : FolOut} {gen' : Gen} {old : Datum}
    (hb : NormSock bus) (ho : NormSock out.prod.sock) (hd : NormSock old.prod) :
    NormSock (runDatum moved bus out gen' old).1.less ∧ NormSock (runDatum moved bus out gen' old).1.prod :=
  ⟨normSock_app _ _ hb, normSock_mergeProd moved (b := ⟨old.prod, old.map⟩) ho hd⟩

/-- The root sock of a poke, `&+sub`, is normal. -/
theorem normSock_root (sub : Noun) : NormSock (Sock.mk Cape.yes sub) := trivial

end SkaModel
end Formalization
