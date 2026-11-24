import lemmas.Compiler.HeSock

/-!
# A `%he` turn of `resolve` moves to a smaller identity

`+recursive-call` answers `%he` for the identity `[a f]` and a frame `[b f]`
when `(he-sock a b)` holds, and `resolve` goes on with `[(msg-sock a b) f]`.

Proved here: `knit_eq_cell` (a knit that is a cell sock is the knit of its
halves), `heSock_size` (`+he-sock` never grows the cape), `msgSock_cases`
(`+msg-sock` of two different socks with capes is `|+~` or the knit of the
`+msg-sock` of the halves of two cells over cells), `msgSock_le` (its result
has a cape no larger than either sock and no more leaves `&` than the first),
`msgSock_left_size` (if it gives `a` back, the cape of `b` is no smaller than
that of `a`), and the `%he` lemma in its strong form, `msgSock_he_lt`: if
`heSock a b` and `a ≠ b` then `msgSock a b` has a smaller `heMeasure` (cape
size plus leaves `&`) than `a`, so `msgSock_ne_of_he`: it is not `a`.  The
induction is on the cape of `a`: in `couple` one half differs and shrinks,
the other stays; when `b` embeds in a half of `a`, the result is no larger
than `b`, which is smaller than `a`; a cape `|` or `&` embeds no other sock.
The bound on the turns of the loop is in `HeBound.lean`.
-/

namespace Formalization
namespace SkaModel

open Nock Compiler

theorem knit_eq_cell {h t : Sock} {ah aT : Cape} {d1 d2 : Noun}
    (e : So.knit h t = Sock.mk (Cape.cell ah aT) (C d1 d2)) :
    h = Sock.mk ah d1 ∧ t = Sock.mk aT d2 := by
  cases h with
  | void => simp [So.knit] at e
  | mk l x1 =>
  cases t with
  | void => simp [So.knit] at e
  | mk r x2 =>
  have key : ∀ c : Cape, (if c = Cape.no then Sock.dunno else Sock.mk c (C x1 x2)) =
      Sock.mk (Cape.cell ah aT) (C d1 d2) → c = Cape.cell ah aT ∧ x1 = d1 ∧ x2 = d2 := by
    intro c hc
    by_cases h0 : c = Cape.no
    · rw [if_pos h0] at hc; simp [Sock.dunno] at hc
    · rw [if_neg h0] at hc
      simp only [Sock.mk.injEq, Noun.cell.injEq] at hc
      exact ⟨hc.1, hc.2.1, hc.2.2⟩
  simp only [So.knit] at e
  obtain ⟨hc, rfl, rfl⟩ := key _ e
  unfold Ca.con at hc
  split at hc
  · simp at hc
  · simp only [Cape.cell.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨rfl, rfl⟩

/-- **`+he-sock` never grows the cape**: if it holds of two different socks,
both are socks with capes and the second cape is no larger. -/
theorem heSock_size {x y : Sock} (h : heSock x y = true) (hne : x ≠ y) :
    ∃ cx dx cy dy, x = Sock.mk cx dx ∧ y = Sock.mk cy dy ∧ capeSize cy ≤ capeSize cx := by
  rw [heSock.eq_def, if_neg hne] at h
  cases x with
  | void => simp at h
  | mk cx dx =>
  cases y with
  | void => simp at h
  | mk cy dy =>
  refine ⟨cx, dx, cy, dy, rfl, rfl, ?_⟩
  simp only at h
  apply Classical.byContradiction
  intro hlt
  rw [if_pos (by omega)] at h
  simp at h

/-! ## The measure of a `%he` turn -/

/-- The number of leaves `&` of a cape. -/
def yesCount : Cape → Nat
  | Cape.yes => 1
  | Cape.no => 0
  | Cape.cell a b => yesCount a + yesCount b

/-- `yesCount` of a sock, `0` for `%void`. -/
def sockYes : Sock → Nat
  | Sock.void => 0
  | Sock.mk c _ => yesCount c

/-- **The measure that a `%he` turn cuts**: the size of the cape plus its
number of leaves `&`, `0` for `%void`. -/
def heMeasure (s : Sock) : Nat := sockSize s + sockYes s

theorem sockSize_mk (c : Cape) (d : Noun) : sockSize (Sock.mk c d) = capeSize c := rfl
theorem sockYes_mk (c : Cape) (d : Noun) : sockYes (Sock.mk c d) = yesCount c := rfl

theorem yesCount_le : ∀ c : Cape, yesCount c ≤ capeSize c
  | Cape.yes => by simp [yesCount, capeSize]
  | Cape.no => by simp [yesCount, capeSize]
  | Cape.cell a b => by
    have := yesCount_le a; have := yesCount_le b
    simp only [yesCount, capeSize]; omega

theorem heMeasure_le (s : Sock) : heMeasure s ≤ 2 * sockSize s := by
  cases s with
  | void => simp [heMeasure, sockSize, sockYes]
  | mk c d => have := yesCount_le c; simp only [heMeasure, sockSize, sockYes]; omega

/-- A knit of two socks with capes has a cape, no larger than the two, and no
more leaves `&`. -/
theorem knit_le (l r : Cape) (d1 d2 : Noun) :
    So.knit (Sock.mk l d1) (Sock.mk r d2) ≠ Sock.void ∧
    sockSize (So.knit (Sock.mk l d1) (Sock.mk r d2)) ≤ capeSize l + capeSize r ∧
    sockYes (So.knit (Sock.mk l d1) (Sock.mk r d2)) ≤ yesCount l + yesCount r := by
  have hl := capeSize_pos l
  have hr := capeSize_pos r
  simp only [So.knit]
  by_cases hc : Ca.con l r = Cape.no
  · rw [if_pos hc]
    simp only [Sock.dunno, sockSize, sockYes, capeSize, yesCount, ne_eq, reduceCtorEq, not_false_eq_true,
      true_and]
    omega
  · rw [if_neg hc]
    unfold Ca.con at hc ⊢
    by_cases h2 : l = Cape.no ∧ r = Cape.no
    · rw [if_pos h2] at hc; exact absurd rfl hc
    · rw [if_neg h2]
      simp [sockSize, sockYes, capeSize, yesCount]

theorem msgSock_self (a : Sock) : msgSock a a = some a := by
  rw [msgSock.eq_def, if_pos rfl]

/-- The two ways `+msg-sock` of two different socks with capes returns: `|+~`,
or the knit of the `+msg-sock` of the halves of two cells over cells. -/
theorem msgSock_cases {ca cb : Cape} {da db : Noun} {c : Sock} (hne : Sock.mk ca da ≠ Sock.mk cb db)
    (hm : msgSock (Sock.mk ca da) (Sock.mk cb db) = some c) :
    c = Sock.dunno ∨ ∃ ah aT ad1 ad2 bh bT bd1 bd2 h t, ca = Cape.cell ah aT ∧ da = C ad1 ad2 ∧
      cb = Cape.cell bh bT ∧ db = C bd1 bd2 ∧ msgSock (Sock.mk ah ad1) (Sock.mk bh bd1) = some h ∧
      msgSock (Sock.mk aT ad2) (Sock.mk bT bd2) = some t ∧ c = So.knit h t := by
  unfold msgSock at hm
  split at hm
  · exact absurd ‹_› hne
  · split at hm
    · rename_i heq; cases heq
    · rename_i heq _; cases heq
    · rename_i ah aT ad1 ad2 bh bT bd1 bd2 heq1 heq2
      cases heq1; cases heq2
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hm
      obtain ⟨h, hh, t, ht, rfl⟩ := hm
      exact Or.inr ⟨ah, aT, ad1, ad2, bh, bT, bd1, bd2, h, t, rfl, rfl, rfl, rfl, hh, ht, rfl⟩
    · cases hm
    · cases hm; exact Or.inl rfl

/-- **`+msg-sock` never grows the cape nor the leaves `&` of its first sock,
and its cape is no larger than that of its second**: for a sock with a cape
and a sock that is not `%void`, the result has a cape no larger than either
and no more leaves `&` than the first. -/
theorem msgSock_le : ∀ (ca : Cape) (da : Noun) (b c : Sock), b ≠ Sock.void →
    msgSock (Sock.mk ca da) b = some c →
    c ≠ Sock.void ∧ sockSize c ≤ capeSize ca ∧ sockSize c ≤ sockSize b ∧ sockYes c ≤ yesCount ca := by
  intro ca
  induction ca with
  | yes =>
    intro da b c hb hm
    cases b with
    | void => exact absurd rfl hb
    | mk cb db =>
    have := capeSize_pos cb
    by_cases e : Sock.mk Cape.yes da = Sock.mk cb db
    · rw [← e, msgSock_self] at hm; cases hm; cases e; simp [sockSize, sockYes]
    · rcases msgSock_cases e hm with rfl | ⟨_, _, _, _, _, _, _, _, _, _, h1, _⟩
      · simp [Sock.dunno, sockSize, sockYes, capeSize, yesCount]; omega
      · cases h1
  | no =>
    intro da b c hb hm
    cases b with
    | void => exact absurd rfl hb
    | mk cb db =>
    have := capeSize_pos cb
    by_cases e : Sock.mk Cape.no da = Sock.mk cb db
    · rw [← e, msgSock_self] at hm; cases hm; cases e; simp [sockSize, sockYes]
    · rcases msgSock_cases e hm with rfl | ⟨_, _, _, _, _, _, _, _, _, _, h1, _⟩
      · simp [Sock.dunno, sockSize, sockYes, capeSize, yesCount]; omega
      · cases h1
  | cell ah aT ih1 ih2 =>
    intro da b c hb hm
    cases b with
    | void => exact absurd rfl hb
    | mk cb db =>
    have := capeSize_pos cb
    have p1 := capeSize_pos ah
    have p2 := capeSize_pos aT
    by_cases e : Sock.mk (Cape.cell ah aT) da = Sock.mk cb db
    · rw [← e, msgSock_self] at hm; cases hm; cases e; simp [sockSize, sockYes]
    · rcases msgSock_cases e hm with rfl | ⟨ah', aT', ad1, ad2, bh, bT, bd1, bd2, h0, t0, h1, rfl, rfl, rfl, hh, ht, rfl⟩
      · simp [Sock.dunno, sockSize, sockYes, capeSize, yesCount]; omega
      · cases h1
        obtain ⟨n1, s1, s1', y1⟩ := ih1 ad1 _ _ (by simp) hh
        obtain ⟨n2, s2, s2', y2⟩ := ih2 ad2 _ _ (by simp) ht
        cases h0 with
        | void => exact absurd rfl n1
        | mk l d1 =>
        cases t0 with
        | void => exact absurd rfl n2
        | mk r d2 =>
        obtain ⟨k1, k2, k3⟩ := knit_le l r d1 d2
        simp only [sockSize, sockYes, capeSize, yesCount] at s1 s1' y1 s2 s2' y2 k2 k3 ⊢
        exact ⟨k1, by omega, by omega, by omega⟩

/-- **`msgSock_left_size`**: if `+msg-sock` of `a` and `b` gives `a` back,
the cape of `b` is no smaller than that of `a` (`b` not `%void`). -/
theorem msgSock_left_size {a b : Sock} (hb : b ≠ Sock.void) (h : msgSock a b = some a) :
    sockSize a ≤ sockSize b := by
  cases a with
  | void => exact Nat.zero_le _
  | mk ca da => exact (msgSock_le ca da b _ hb h).2.2.1

/-- `heMeasure` of a sock with a cape. -/
theorem heMeasure_mk (c : Cape) (d : Noun) : heMeasure (Sock.mk c d) = capeSize c + yesCount c := rfl

/-- The `%he` lemma on socks with capes, by induction on the cape of `a`. -/
theorem msgSock_he_lt_mk : ∀ (ca : Cape) (da : Noun) (cb : Cape) (db : Noun) (c : Sock),
    heSock (Sock.mk ca da) (Sock.mk cb db) = true → Sock.mk ca da ≠ Sock.mk cb db →
    msgSock (Sock.mk ca da) (Sock.mk cb db) = some c → heMeasure c < capeSize ca + yesCount ca := by
  intro ca
  induction ca with
  | yes =>
    intro da cb db c hh hne hm
    obtain ⟨_, _, _, _, h3, h4, hsz⟩ := heSock_size hh hne
    cases h3; cases h4
    rw [heSock.eq_def, if_neg hne] at hh
    simp only at hh
    rw [if_neg (by omega)] at hh
    cases cb <;> simp at hh
  | no =>
    intro da cb db c hh hne hm
    obtain ⟨_, _, _, _, h3, h4, hsz⟩ := heSock_size hh hne
    cases h3; cases h4
    rw [heSock.eq_def, if_neg hne] at hh
    simp only at hh
    rw [if_neg (by omega)] at hh
    cases cb <;> simp at hh
  | cell ah aT ih1 ih2 =>
    intro da cb db c hh hne hm
    obtain ⟨_, _, _, _, h3, h4, hsz⟩ := heSock_size hh hne
    cases h3; cases h4
    have p1 := capeSize_pos ah
    have p2 := capeSize_pos aT
    obtain ⟨nc, sc1, sc2, yc⟩ := msgSock_le _ da _ c (by simp) hm
    simp only [heMeasure, sockSize_mk, capeSize, yesCount] at sc1 sc2 yc hsz ⊢
    -- when `b` sits inside a half of `a`, the result is no larger than `b`
    have half : ∀ x : Sock, sockSize x < capeSize ah + capeSize aT → heSock x (Sock.mk cb db) = true →
        sockSize c + sockYes c < capeSize ah + capeSize aT + (yesCount ah + yesCount aT) := by
      intro x hx hx'
      by_cases e : x = Sock.mk cb db
      · subst e; simp only [sockSize_mk] at hx; omega
      · obtain ⟨cx, dx, cy, dy, rfl, hy, hs⟩ := heSock_size hx' e
        cases hy; simp only [sockSize_mk] at hx; omega
    rw [heSock.eq_def, if_neg hne] at hh
    simp only at hh
    rw [if_neg (by simp only [capeSize]; omega)] at hh
    cases cb with
    | yes =>
      simp only [Bool.or_eq_true] at hh
      rcases hh with hh | hh
      · exact half _ (sockSize_hed_lt ah aT da) hh
      · exact half _ (sockSize_tel_lt ah aT da) hh
    | no =>
      simp only [Bool.or_eq_true] at hh
      rcases hh with hh | hh
      · exact half _ (sockSize_hed_lt ah aT da) hh
      · exact half _ (sockSize_tel_lt ah aT da) hh
    | cell bh bT =>
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hh
      rcases hh with ⟨h1, h2⟩ | hh | hh
      · -- `couple`: then `a` and `b` are cells over cells, else the result is `|+~` or a crash
        rcases msgSock_cases hne hm with rfl | ⟨ah', aT', ad1, ad2, bh', bT', bd1, bd2, h0, t0, e1, rfl, e2, rfl, hh0, ht0, rfl⟩
        · simp [Sock.dunno, sockSize, sockYes, capeSize, yesCount]; omega
        cases e1; cases e2
        simp only [So.hed, So.tel] at h1 h2
        obtain ⟨n1, -, -, -⟩ := msgSock_le ah ad1 _ h0 (by simp) hh0
        obtain ⟨n2, -, -, -⟩ := msgSock_le aT ad2 _ t0 (by simp) ht0
        have m1 : heMeasure h0 ≤ capeSize ah + yesCount ah ∧
            (Sock.mk ah ad1 ≠ Sock.mk bh bd1 → heMeasure h0 < capeSize ah + yesCount ah) := by
          by_cases e : Sock.mk ah ad1 = Sock.mk bh bd1
          · rw [← e, msgSock_self] at hh0; cases hh0
            exact ⟨Nat.le_refl _, fun e' => absurd e e'⟩
          · have := ih1 ad1 bh bd1 h0 h1 e hh0
            exact ⟨Nat.le_of_lt this, fun _ => this⟩
        have m2 : heMeasure t0 ≤ capeSize aT + yesCount aT ∧
            (Sock.mk aT ad2 ≠ Sock.mk bT bd2 → heMeasure t0 < capeSize aT + yesCount aT) := by
          by_cases e : Sock.mk aT ad2 = Sock.mk bT bd2
          · rw [← e, msgSock_self] at ht0; cases ht0
            exact ⟨Nat.le_refl _, fun e' => absurd e e'⟩
          · have := ih2 ad2 bT bd2 t0 h2 e ht0
            exact ⟨Nat.le_of_lt this, fun _ => this⟩
        have hor : Sock.mk ah ad1 ≠ Sock.mk bh bd1 ∨ Sock.mk aT ad2 ≠ Sock.mk bT bd2 := by
          by_cases e1 : Sock.mk ah ad1 = Sock.mk bh bd1
          · refine Or.inr fun e2 => hne ?_
            cases e1; cases e2; rfl
          · exact Or.inl e1
        cases h0 with
        | void => exact absurd rfl n1
        | mk l d1 =>
        cases t0 with
        | void => exact absurd rfl n2
        | mk r d2 =>
        obtain ⟨-, k2, k3⟩ := knit_le l r d1 d2
        simp only [heMeasure, sockSize_mk, sockYes_mk] at m1 m2 k2 k3 ⊢
        rcases hor with e | e
        · have := m1.2 e; omega
        · have := m2.2 e; omega
      · exact half _ (sockSize_hed_lt ah aT da) hh
      · exact half _ (sockSize_tel_lt ah aT da) hh

/-- **Each `%he` turn strictly cuts `heMeasure`**: if `+he-sock` holds of two
different socks `a` and `b`, then `(msg-sock a b)` has a smaller measure than
`a`.  For example `a = [[& |] [5 ~]]` and `b = &+[5 6]` give `|+~`: from `4`
to `1`. -/
theorem msgSock_he_lt {a b c : Sock} (hh : heSock a b = true) (hne : a ≠ b) (hm : msgSock a b = some c) :
    heMeasure c < heMeasure a := by
  obtain ⟨ca, da, cb, db, rfl, rfl, -⟩ := heSock_size hh hne
  exact msgSock_he_lt_mk ca da cb db c hh hne hm

/-- **The `%he` lemma**: if `+he-sock` holds of two different socks, their
`+msg-sock` is not the first, so a `%he` turn of `resolve` moves to another
identity. -/
theorem msgSock_ne_of_he {a b : Sock} (hh : heSock a b = true) (hne : a ≠ b) : msgSock a b ≠ some a :=
  fun hm => Nat.lt_irrefl _ (msgSock_he_lt hh hne hm)

end SkaModel
end Formalization
