import lemmas.Ska.PassClosureR

/-!
# The closure invariant, part 3: `fol-loop` keeps good regions (track F, Gaps 16)

**`folLoop_G`**: a formula with the formula invariant `FormG G` on a subject
whose `&` regions are in `G` gives a product whose `&` regions are in `G`, at
every fuel, for any invariant `Inv` of `gen` that depends only on the parts
`LocalStable` names, given that `resolve`, asked at a call whose formula is in
`G` and whose subject sock has good regions, keeps `Inv` and answers a product
with good regions (`ResGG`).  `G` is closed under halves (`SubC`) and saf
values (`SafC`): `NGood As B` is.

The case split is the one of `folStep_saf`; `Inv` is carried as in
`bridge_stepQ`.  The `&` data a product can get, case by case: the saf value
of a `%1` or of a cons of two safe sides (in `G` by `FormG`, through
`folLoop_saf`), a part of the subject (`+pull:so`), a `+knit:so`, `+darn:so`
or `+double-int` of good socks, or the answer of `resolve`.  A call inlined
(`[2 s [1 f]]` with `f` known) analyses `f`, which is in `G` as a region of
the formula's product, so it satisfies `FormG` (`formG_of`).
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

variable {M : Type → Type → Type} [Treap M] {R : Type}

section FolG

variable {G : Noun → Prop} {Inv : GenS M R → Prop}

/-- What `resolve` must give at a call whose formula is in `G` and whose
subject sock (not `%void`) has good regions: it keeps `Inv`, and its product
has good regions. -/
def ResGG (G : Noun → Prop) (Inv : GenS M R → Prop) (res : ResGo M R) : Prop :=
  ∀ idT gs r gs', Inv gs → G idT.2 → SockG G idT.1 → idT.1 ≠ Sock.void → res idT gs = some (r, gs') →
    Inv gs' ∧ SockG G r.2.prod

/-- What the recursion of `fol-loop` gives on a `FormG` formula and a good
subject: it keeps `Inv`, and its product has good regions. -/
def GoGG (G : Noun → Prop) (Inv : GenS M R → Prop) (go : FolGoS M R) : Prop :=
  ∀ fol sub seat mk bc df gs out gs', Inv gs → FormG G fol → AnnoG G sub →
    go fol sub seat mk bc df gs = some (out, gs') → Inv gs' ∧ AnnoG G out.prod

/-- The `%2` case keeps good regions. -/
theorem callStep_G (hG : SubC G) (hS : SafC G) (hL : LocalStable Inv) {res : ResGo M R} {go : FolGoS M R}
    (hres : ResGG G Inv res) (hgo : GoGG G Inv go) {seat mk : Option Noun} {bc df : Bool}
    {s f out : FolOut} {g g' : GenS M R} (hi : Inv g) (hs : AnnoG G s.prod) (hf : AnnoG G f.prod)
    (h : callStep res go seat mk bc df s f g = some (out, g')) : Inv g' ∧ AnnoG G out.prod := by
  unfold callStep at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hi, trivial⟩
  · rename_i hnv
    split at h
    · rename_i fa fb heq
      have hfab : G (C fa fb) := by
        have h' : SockG G f.prod.sock := hf
        rw [heq] at h'; exact h'
      split at h
      · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨i, g3⟩, h4, rfl, rfl⟩ := h
        have i' : Inv ({ g with want := Ca.uni g.want (distribute Cape.yes f.prod.src) } : GenS M R) :=
          hL.app hi rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        obtain ⟨i3, p3⟩ := hgo _ _ _ _ _ _ _ _ _ i' (formG_of hG hS _ hfab) hs h4
        exact ⟨i3, p3⟩
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨⟨r1, g3⟩, h4, h⟩ := h
        obtain ⟨i3, p3⟩ := hres (s.prod.sock, C fa fb) _ _ _ hi hfab hs (fun e => hnv (Or.inl e)) h4
        split at h
        · cases h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hL.app i3 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, p3⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hL.app hi rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, trivial⟩

/-- **One level of `fol-loop` keeps good regions**, from the recursion. -/
theorem folStep_G (env : Env R) (hG : SubC G) (hS : SafC G) (hL : LocalStable Inv)
    {res : ResGo M R} {go : FolGoS M R} (hres : ResGG G Inv res) (hgo : GoGG G Inv go)
    (hsaf : ∀ fol sub seat mk bc df gs out gs', go fol sub seat mk bc df gs = some (out, gs') →
      out.saf = true → SafP fol out)
    {fol : Noun} {sub : Anno} {seat mk : Option Noun} {bc df : Bool} {gs gs' : GenS M R} {out : FolOut}
    (hi : Inv gs) (hf : FormG G fol) (hs : AnnoG G sub)
    (h : folStep env res go fol sub seat mk bc df gs = some (out, gs')) : Inv gs' ∧ AnnoG G out.prod := by
  cases hsh : shape fol with
  | cons a b q =>
    rw [shape_cons hsh] at hf
    simp only [folStep, hsh, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨l, g1⟩, h1, ⟨r, g2⟩, h2, rfl, rfl⟩ := h
    obtain ⟨i1, p1⟩ := hgo _ _ _ _ _ _ _ _ _ hi hf.2.1 hs h1
    obtain ⟨i2, p2⟩ := hgo _ _ _ _ _ _ _ _ _ i1 hf.2.2 hs h2
    refine ⟨i2, ?_⟩
    show SockG G (consProd l r).1.sock
    unfold consProd
    split
    · rename_i hc
      have e1 := (hsaf _ _ _ _ _ _ _ _ _ h1 hc.1).1
      have e2 := (hsaf _ _ _ _ _ _ _ _ _ h2 hc.2.1).1
      have ev : safV (C (C a b) q) = some (C l.prod.sock.data r.prod.sock.data) := by
        simp only [safV, e1, e2, Option.bind_some, Option.map_some]
      exact (formG_loc hf).1 _ ev
    · exact sockG_knit p1 p2
  | op0 p =>
    simp only [folStep, hsh, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨pr, hpr, rfl, rfl⟩ := h
    refine ⟨hi, ?_⟩
    show SockG G pr.sock
    split at hpr
    · cases hpr; trivial
    · split at hpr
      · cases hpr; exact hs
      · simp only [Option.map_eq_some_iff] at hpr
        obtain ⟨s', hp, rfl⟩ := hpr
        exact sockG_pull hG hs hp
  | op1 p =>
    simp only [folStep, hsh, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [shape_op1C hsh] at hf
    exact ⟨hi, (formG_loc hf).1 p (by simp [safV])⟩
  | op2 a b q =>
    rw [shape_op2 hsh] at hf
    simp only [folStep, hsh, Option.bind_eq_some_iff] at h
    obtain ⟨⟨s1, g1⟩, h1, ⟨f1, g2⟩, h2, h3⟩ := h
    obtain ⟨i1, p1⟩ := hgo _ _ _ _ _ _ _ _ _ hi hf.2.2.2.1 hs h1
    obtain ⟨i2, p2⟩ := hgo _ _ _ _ _ _ _ _ _ i1 hf.2.2.2.2 hs h2
    exact callStep_G hG hS hL hres hgo i2 p1 p2 h3
  | op3 a b =>
    rw [shape_op3 hsh] at hf
    simp only [folStep, hsh, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, rfl, rfl⟩ := h
    exact ⟨(hgo _ _ _ _ _ _ _ _ _ hi hf.2.2 hs h1).1, trivial⟩
  | op4 a b =>
    rw [shape_op4 hsh] at hf
    simp only [folStep, hsh, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, rfl, rfl⟩ := h
    exact ⟨(hgo _ _ _ _ _ _ _ _ _ hi hf.2.2 hs h1).1, trivial⟩
  | op5 a b q =>
    rw [shape_op5 hsh] at hf
    simp only [folStep, hsh, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    have i1 := (hgo _ _ _ _ _ _ _ _ _ hi hf.2.2.2.1 hs h1).1
    exact ⟨(hgo _ _ _ _ _ _ _ _ _ i1 hf.2.2.2.2 hs h2).1, trivial⟩
  | op6 a b q r =>
    rw [shape_op6 hsh] at hf
    simp only [folStep, hsh, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, ⟨r1, g3⟩, h3, rfl, rfl⟩ := h
    have i1 := (hgo _ _ _ _ _ _ _ _ _ hi hf.2.2.2.1 hs h1).1
    obtain ⟨i2, pq⟩ := hgo _ _ _ _ _ _ _ _ _ i1 hf.2.2.2.2.2.1 hs h2
    obtain ⟨i3, pr⟩ := hgo _ _ _ _ _ _ _ _ _ i2 hf.2.2.2.2.2.2 hs h3
    exact ⟨i3, sockG_doubleInt hG pq pr⟩
  | op7 a b q =>
    rw [shape_op7 hsh] at hf
    simp only [folStep, hsh, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    obtain ⟨i1, pp⟩ := hgo _ _ _ _ _ _ _ _ _ hi hf.2.2.2.1 hs h1
    obtain ⟨i2, p2⟩ := hgo _ _ _ _ _ _ _ _ _ i1 hf.2.2.2.2 pp h2
    exact ⟨i2, p2⟩
  | op8 a b q =>
    rw [shape_op8 hsh] at hf
    simp only [folStep, hsh] at h
    exact hgo _ _ _ _ _ _ _ _ _ hi (formG_op8 hf) hs h
  | op9 p a b =>
    rw [shape_op9 hsh] at hf
    simp only [folStep, hsh] at h
    exact hgo _ _ _ _ _ _ _ _ _ hi (formG_op9 hf) hs h
  | op10 ax don r1 r2 =>
    rw [shape_op10 hsh] at hf
    simp only [folStep, hsh] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hi, trivial⟩
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨dn, g1⟩, h1, ⟨rc, g2⟩, h2, s', hd, rfl, rfl⟩ := h
      obtain ⟨i1, p1⟩ := hgo _ _ _ _ _ _ _ _ _ hi hf.2.2.2.1.2.2 hs h1
      obtain ⟨i2, p2⟩ := hgo _ _ _ _ _ _ _ _ _ i1 hf.2.2.2.2 hs h2
      exact ⟨i2, sockG_darn hG p2 p1 hd⟩
  | op11s p a b =>
    rw [shape_op11s hsh] at hf
    simp only [folStep, hsh] at h
    split at h
    · rename_i hp
      exact hgo _ _ _ _ _ _ _ _ _ hi (formG_bare hf hp) hs h
    · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨q1, g1⟩, h1, rfl, rfl⟩ := h
      obtain ⟨i1, p1⟩ := hgo _ _ _ _ _ _ _ _ _ hi hf.2.2.2.2 hs h1
      exact ⟨i1, p1⟩
  | op11d tag h1 h2 f =>
    rw [shape_op11d hsh] at hf
    simp only [folStep, hsh, Option.bind_eq_some_iff] at h
    obtain ⟨⟨hh, g1⟩, hh1, h⟩ := h
    have isg := spotHint_inv hL env tag h1 h2 seat hi
    obtain ⟨i1, ph⟩ := hgo _ _ _ _ _ _ _ _ _ isg hf.2.2.2.1.2.2 hs hh1
    split at h
    · rename_i hc
      exact hgo _ _ _ _ _ _ _ _ _ i1 (formG_memo hf hc.1) hs h
    · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨arm, g2⟩, harm, ⟨fr, g3⟩, h3, gfin, h4, rfl, rfl⟩ := h
      have iA : Inv g2 := by
        rcases meanArm_cases harm with ⟨rfl, _⟩ | ⟨cg, hcg, rfl, _⟩
        · exact i1
        · exact (hgo _ _ _ _ _ _ _ _ _ i1 (formG_two_slot 2) ph hcg).1
      obtain ⟨i3, p3⟩ := hgo _ _ _ _ _ _ _ _ _ iA hf.2.2.2.2 hs h3
      exact ⟨(fastHint_inv hL i3 h4).1, p3⟩
  | op11c x y h1 h2 f =>
    rw [shape_op11c hsh] at hf
    simp only [folStep, hsh] at h
    exact hgo _ _ _ _ _ _ _ _ _ hi (formG_op11c hf) hs h
  | op12 a b q =>
    rw [shape_op12 hsh] at hf
    simp only [folStep, hsh, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    have i1 := (hgo _ _ _ _ _ _ _ _ _ hi hf.2.2.2.1 hs h1).1
    exact ⟨(hgo _ _ _ _ _ _ _ _ _ i1 hf.2.2.2.2 hs h2).1, trivial⟩
  | other =>
    simp only [folStep, hsh, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hi, trivial⟩

/-- **`fol-loop` keeps good regions**, at every fuel, given `ResGG` of
`resolve` at every fuel below. -/
theorem folLoop_G (env : Env R) (memoF : Memo M) (hG : SubC G) (hS : SafC G) (hL : LocalStable Inv) :
    ∀ n, (∀ k, k < n → ResGG G Inv (resolveR env memoF k)) → GoGG G Inv (folLoop env memoF n)
  | 0 => fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => by rw [folLoop_zero] at h; cases h
  | n + 1 => fun hres _ _ _ _ _ _ _ _ _ hi hf hs h => by
    rw [folLoop_succ] at h
    exact folStep_G env hG hS hL (hres n (Nat.lt_succ_self n))
      (folLoop_G env memoF hG hS hL n (fun k hk => hres k (Nat.lt_succ_of_lt hk)))
      (folLoop_saf env memoF n) hi hf hs h

/-- **The run of `+run` on an identity whose formula is in `G` and whose
subject sock has good regions** ends with a product with good regions. -/
theorem run_folG (env : Env R) (memoF : Memo M) (hG : SubC G) (hS : SafC G) (hL : LocalStable Inv)
    {n index : Nat} (hres : ∀ k, k < n → ResGG G Inv (resolveR env memoF k)) {id : Ident}
    {st : SkaState M R} {out : FolOut} {gs' : GenS M R} (hi : Inv (genInit index st))
    (hf : G id.2) (hs : SockG G id.1)
    (h : folLoop env memoF n id.2 ⟨id.1, A 1⟩ none none false false (genInit index st) = some (out, gs')) :
    Inv gs' ∧ AnnoG G out.prod :=
  folLoop_G env memoF hG hS hL n hres id.2 ⟨id.1, A 1⟩ none none false false _ _ _ hi (formG_of hG hS _ hf) hs h

end FolG

end Ana
end SkaModel
end Formalization
