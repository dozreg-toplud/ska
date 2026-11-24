import lemmas.Ska.SockFacts

/-!
# The bake of a callee variant

`+bake-graph` gives each callee code bell `c` of a poke a variant whose
subject sock (its bake) is `less.c` when it is fixed (the root, a jetted
arm, frozen mode) or no site informs it, and otherwise
`norm-sock (uni-sock less.c meet)`, `meet` the `+purr:so` of the socks `k`
that the sites calling `c` know of their subjects; a bake that would not be a
loss is intersected with the old one (`+purr:so` and `+norm-sock` again).
The final pass sends each site `[c k]` to an existing variant `v` that
`+pick` finds (`huge:so less.c k` and `huge:so less.v k`), or to the bake of
`c`, with no check that `k` provides the bake.

This file models `+uni-sock` (`uniSock`), `+norm-sock` (`normSockH`, `none`
its crash on a cell cape over atom data) and the bake (`meet`, `bakeOf`,
`rebake`), and proves what makes the choice of a site's variant sound: a
subject that fits both `less.c` and the site's `k` fits the variant's bell
(`bakeOf_fits`, `rebake_fits`, `pick_fits`).

It also shows (`uniSock_drops_less`) that a bake need not imply `less.c`:
`+uni-sock` returns its second sock whole when that one is fully known, so
where `meet` contradicts `less.c` the bake admits subjects that `less.c` does
not.  A site's subject fits both, so this is sound for the sites of the poke;
the bell of such a variant promises more than its code keeps.
-/

namespace Formalization
namespace SkaModel

open Nock

namespace Bake

/-- `+uni-sock`: what two socks know together, the first one winning where
it is fully known, the second where it is and the first is not. -/
def uniSock (a b : Sock) : Sock :=
  if a = b then a else
  match a, b with
  | Sock.void, b => b
  | a, Sock.void => a
  | Sock.mk ca da, Sock.mk cb db =>
    if Ca.all ca = true then Sock.mk ca da else
    if Ca.all cb = true then Sock.mk cb db else
    if ca = Cape.no then Sock.mk cb db else
    if cb = Cape.no then Sock.mk ca da else
    match ca, cb with
    | Cape.cell ah aT, Cape.cell bh bT =>
      So.knit (uniSock (So.hed (Sock.mk (Cape.cell ah aT) da)) (So.hed (Sock.mk (Cape.cell bh bT) db)))
        (uniSock (So.tel (Sock.mk (Cape.cell ah aT) da)) (So.tel (Sock.mk (Cape.cell bh bT) db)))
    | _, _ => Sock.mk ca da
termination_by So.depth a + So.depth b
decreasing_by
  all_goals simp_wf
  · exact Nat.add_lt_add So.depth_hed_lt So.depth_hed_lt
  · exact Nat.add_lt_add So.depth_tel_lt So.depth_tel_lt

theorem isNo_all {c : Cape} (h : c.isNo = true) : Ca.all c = false := by
  induction c with
  | yes => simp [Cape.isNo] at h
  | no => rfl
  | cell h t ih1 ih2 =>
    simp only [Cape.isNo, Bool.and_eq_true] at h
    simp [Ca.all, ih1 h.1, ih2 h.2]

/-- The three outcomes of `+uni-sock`: one of its socks, or the cons of the
unions of the heads and of the tails of two cell capes. -/
theorem uniSock_cases (a b : Sock) (P : Sock → Prop) (h1 : P a) (h2 : P b)
    (h3 : ∀ ah aT da bh bT db, a = Sock.mk (Cape.cell ah aT) da → b = Sock.mk (Cape.cell bh bT) db →
      P (So.knit (uniSock (So.hed a) (So.hed b)) (uniSock (So.tel a) (So.tel b)))) :
    P (uniSock a b) := by
  rw [uniSock.eq_def]
  by_cases hab : a = b
  · rw [if_pos hab]; exact h1
  rw [if_neg hab]
  cases a with
  | void => exact h2
  | mk ca da =>
  cases b with
  | void => exact h1
  | mk cb db =>
  dsimp only
  by_cases e1 : Ca.all ca = true
  · rw [if_pos e1]; exact h1
  rw [if_neg e1]
  by_cases e2 : Ca.all cb = true
  · rw [if_pos e2]; exact h2
  rw [if_neg e2]
  by_cases e3 : ca = Cape.no
  · rw [if_pos e3]; exact h2
  rw [if_neg e3]
  by_cases e4 : cb = Cape.no
  · rw [if_pos e4]; exact h1
  rw [if_neg e4]
  cases ca with
  | yes => exact h1
  | no => exact absurd rfl e3
  | cell ah aT =>
    cases cb with
    | yes => exact h1
    | no => exact absurd rfl e4
    | cell bh bT => exact h3 ah aT da bh bT db rfl rfl

theorem uniSock_blank : ∀ (k : Nat) (a b : Sock), So.depth a + So.depth b < k → a.Blank → b.Blank →
    (uniSock a b).Blank := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk ha hb
  refine uniSock_cases a b Sock.Blank ha hb fun ah aT da bh bT db ea eb => ?_
  subst ea eb
  have h1 := So.depth_hed_lt (ch := ah) (ct := aT) (d := da)
  have h2 := So.depth_hed_lt (ch := bh) (ct := bT) (d := db)
  have h3 := So.depth_tel_lt (ch := ah) (ct := aT) (d := da)
  have h4 := So.depth_tel_lt (ch := bh) (ct := bT) (d := db)
  exact knit_blank (ih _ _ (by omega) (hed_blank ha) (hed_blank hb)) (ih _ _ (by omega) (tel_blank ha) (tel_blank hb))

/-- **`+uni-sock` keeps what both know**: a noun of both socks is a noun of
their union. -/
theorem uniSock_fits : ∀ (k : Nat) (a b : Sock), So.depth a + So.depth b < k → ∀ x, Fits a x → Fits b x →
    Fits (uniSock a b) x := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk x ha hb
  refine uniSock_cases a b (fun u => Fits u x) ha hb fun ah aT da bh bT db ea eb => ?_
  subst ea eb
  have h1 := So.depth_hed_lt (ch := ah) (ct := aT) (d := da)
  have h2 := So.depth_hed_lt (ch := bh) (ct := bT) (d := db)
  have h3 := So.depth_tel_lt (ch := ah) (ct := aT) (d := da)
  have h4 := So.depth_tel_lt (ch := bh) (ct := bT) (d := db)
  cases x with
  | cell x1 x2 =>
    exact knit_fits (ih _ _ (by omega) x1 (hed_fits ha) (hed_fits hb))
      (ih _ _ (by omega) x2 (tel_fits ha) (tel_fits hb))
  | atom n =>
    simp only [Fits, FitsCape] at ha hb
    rcases ha with ha | ⟨_, _, _, _, _, hn, _⟩
    · rcases hb with hb | ⟨_, _, _, _, _, hn, _⟩
      · have ba : (Sock.mk (Cape.cell ah aT) da).Blank := ⟨Cape.cell ah aT, da, rfl, ha⟩
        have bb : (Sock.mk (Cape.cell bh bT) db).Blank := ⟨Cape.cell bh bT, db, rfl, hb⟩
        exact (knit_blank (uniSock_blank _ _ _ (Nat.lt_succ_self _) (hed_blank ba) (hed_blank bb))
          (uniSock_blank _ _ _ (Nat.lt_succ_self _) (tel_blank ba) (tel_blank bb))).fits _
      · cases hn
    · cases hn

/-! ## `+norm-sock` -/

/-- `+norm-sock` on a cape and its data: `|` where nothing is known, `&`
where all is (a cell of two `&` becomes `&`).  `none` is the crash of
`-.data` on a cell cape over atom data. -/
def normCD : Cape → Noun → Option (Cape × Noun)
  | Cape.no, _ => some (Cape.no, A 0)
  | Cape.yes, d => some (Cape.yes, d)
  | Cape.cell _ _, Noun.atom _ => none
  | Cape.cell h t, Noun.cell dh dt =>
    (normCD h dh).bind fun l => (normCD t dt).map fun r =>
      if l.1 = Cape.no ∧ r.1 = Cape.no then (Cape.no, A 0) else
      (if (l.1 = Cape.yes ∨ l.1 = Cape.no) ∧ l.1 = r.1 then l.1 else Cape.cell l.1 r.1, C l.2 r.2)

/-- `+norm-sock`. -/
def normSockH : Sock → Option Sock
  | Sock.void => some Sock.void
  | Sock.mk c d => (normCD c d).map fun p => Sock.mk p.1 p.2

theorem normCD_isNo : ∀ {c : Cape} {d : Noun} {p : Cape × Noun}, c.isNo = true → normCD c d = some p →
    p.1 = Cape.no
  | Cape.no, _, _, _, h => by simp only [normCD, Option.some.injEq] at h; rw [← h]
  | Cape.yes, _, _, hc, _ => by simp [Cape.isNo] at hc
  | Cape.cell _ _, Noun.atom _, _, _, h => by simp [normCD] at h
  | Cape.cell h t, Noun.cell dh dt, p, hc, e => by
    simp only [Cape.isNo, Bool.and_eq_true] at hc
    simp only [normCD, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e
    obtain ⟨l, hl, r, hr, rfl⟩ := e
    rw [if_pos ⟨normCD_isNo hc.1 hl, normCD_isNo hc.2 hr⟩]

theorem normCD_fits : ∀ {c : Cape} {d x : Noun} {p : Cape × Noun}, FitsCape c d x → normCD c d = some p →
    FitsCape p.1 p.2 x
  | Cape.no, _, _, _, _, h => by simp only [normCD, Option.some.injEq] at h; rw [← h]; trivial
  | Cape.yes, _, _, _, hf, h => by simp only [normCD, Option.some.injEq] at h; rw [← h]; exact hf
  | Cape.cell _ _, Noun.atom _, _, _, _, h => by simp [normCD] at h
  | Cape.cell h t, Noun.cell dh dt, x, p, hf, e => by
    have e' := e
    simp only [normCD, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e
    obtain ⟨l, hl, r, hr, rfl⟩ := e
    simp only [FitsCape] at hf
    rcases hf with hno | ⟨dh', dt', xh, xt, hd, rfl, fh, ft⟩
    · rw [normCD_isNo (c := Cape.cell h t) hno e']; trivial
    · cases hd
      have fl := normCD_fits fh hl
      have fr := normCD_fits ft hr
      split
      · trivial
      · rename_i hnn
        dsimp only
        split
        · rename_i hy
          obtain ⟨hy1 | hy1, hy2⟩ := hy
          · rw [hy1] at fl ⊢; rw [← hy2, hy1] at fr
            simp only [FitsCape] at fl fr ⊢
            rw [fl, fr]
          · exact absurd ⟨hy1, hy2 ▸ hy1⟩ hnn
        · simp only [FitsCape]
          exact Or.inr ⟨l.2, r.2, xh, xt, rfl, rfl, fl, fr⟩

/-- **`+norm-sock` keeps the nouns of a sock.** -/
theorem normSockH_fits {s s' : Sock} {x : Noun} (hf : Fits s x) (h : normSockH s = some s') : Fits s' x := by
  cases s with
  | void => exact absurd hf id
  | mk c d =>
    simp only [normSockH, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, rfl⟩ := h
    exact normCD_fits hf hp

/-! ## The bake and the choice of a site's variant -/

/-- The meet of what the sites know, as the `roll` of `+bake-graph`. -/
def meet (k : Sock) (ks : List Sock) : Sock := ks.foldl (fun acc k' => So.purr k' acc) k

theorem meet_fits : ∀ (ks : List Sock) (k : Sock) (x : Noun), (Fits k x ∨ ∃ k' ∈ ks, Fits k' x) →
    Fits (meet k ks) x
  | [], k, x, h => by
    rcases h with h | ⟨_, h, _⟩
    · exact h
    · simp at h
  | k' :: ks, k, x, h => by
    unfold meet
    simp only [List.foldl_cons]
    refine meet_fits ks (So.purr k' k) x ?_
    rcases h with h | ⟨k'', hk, hf⟩
    · exact Or.inl (purr_fits_right _ _ _ h)
    · rcases List.mem_cons.mp hk with rfl | hk
      · exact Or.inl (purr_fits_left _ _ _ hf)
      · exact Or.inr ⟨k'', hk, hf⟩

/-- The bake of a callee from what its sites know (`ks`, what the callers
evaluated last say), or its code requirement `lessc` when fixed or when no
site informs it.  `none` is a crash.  With the guard of the Hoon (commit
8f2162e): `both` is `norm-sock (uni-sock less.c meet)`, and when
`(huge:so less.c both)` says no, the bake is `less.c` alone. -/
def bakeOf (fixed : Bool) (lessc : Sock) (ks : List Sock) : Option Sock :=
  if fixed then some lessc else
  match ks with
  | [] => some lessc
  | k :: ks => (normSockH (uniSock lessc (meet k ks))).bind fun both =>
      (So.huge lessc both).map fun h => if h then both else lessc

/-- A new bake against the old one: kept if it is a loss (`huge:so bake
old`), intersected with the old one otherwise. -/
def rebake (bake : Sock) (old : Option Sock) : Option Sock :=
  match old with
  | none => some bake
  | some o => (So.huge bake o).bind fun h => if h then some bake else normSockH (So.purr bake o)

/-- **A site's subject fits the bake of its callee**: a subject that fits
the callee's code requirement and what one of the sites knows fits the bake. -/
theorem bakeOf_fits {fixed : Bool} {lessc s k : Sock} {ks : List Sock} {x : Noun} (hl : Fits lessc x)
    (hk : Fits k x) (hm : k ∈ ks) (h : bakeOf fixed lessc ks = some s) : Fits s x := by
  unfold bakeOf at h
  split at h
  · cases h; exact hl
  · split at h
    · cases h; exact hl
    · rename_i k0 ks0
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨both, hb, hv, _, rfl⟩ := h
      split
      · refine normSockH_fits (uniSock_fits _ _ _ (Nat.lt_succ_self _) x hl (meet_fits ks0 k0 x ?_)) hb
        rcases List.mem_cons.mp hm with rfl | hm
        · exact Or.inl hk
        · exact Or.inr ⟨k, hm, hk⟩
      · exact hl

theorem rebake_fits {bake s : Sock} {old : Option Sock} {x : Noun} (hb : Fits bake x)
    (h : rebake bake old = some s) : Fits s x := by
  unfold rebake at h
  split at h
  · cases h; exact hb
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨b, _, h⟩ := h
    split at h
    · cases h; exact hb
    · exact normSockH_fits (purr_fits_left _ _ _ hb) h

/-- **A variant that `+pick` finds fits the site's subject.** -/
theorem pick_fits {lessv k : Sock} {x : Noun} (hh : So.huge lessv k = some true) (hk : Fits k x) :
    Fits lessv x :=
  huge_sound hh hk

/-! ## A bake need not imply the code requirement -/

/-- **`+uni-sock` drops the first sock where the second is fully known**:
`less.c` knows the head `5`, the meet knows the whole subject `[6 7]`, and
their union is `[6 7]`. -/
theorem uniSock_drops_less :
    uniSock (Sock.mk (Cape.cell Cape.yes Cape.no) (C (A 5) (A 0))) (Sock.mk Cape.yes (C (A 6) (A 7))) =
      Sock.mk Cape.yes (C (A 6) (A 7)) := by
  rw [uniSock.eq_def]
  rw [if_neg (by simp)]
  dsimp only
  rw [if_neg (by simp [Ca.all])]
  rw [if_pos (by rfl)]

/-- The subject `[6 7]` fits that bake and not that code requirement. -/
theorem uniSock_drops_less_fits :
    Fits (Sock.mk Cape.yes (C (A 6) (A 7))) (C (A 6) (A 7)) ∧
      ¬ Fits (Sock.mk (Cape.cell Cape.yes Cape.no) (C (A 5) (A 0))) (C (A 6) (A 7)) := by
  refine ⟨rfl, ?_⟩
  simp [Fits, FitsCape, Cape.isNo]

end Bake

end SkaModel
end Formalization
