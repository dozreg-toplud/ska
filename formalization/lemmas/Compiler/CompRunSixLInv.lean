import lemmas.Compiler.CompLeapGate
import lemmas.Compiler.CompRunRegs

/-!
# What `+leap` keeps of the invariant (`LeapInv`)

`leapInv`: on a lazy need with `LInv kr kb` and branches with `Bake.NoAx0`,
what `+leap` returns (the rest and every `by`) meets `LInv kr kb`, no
register is in two of them or twice in one, and every register is one of
the goal's need: the hypothesis `LeapInv` of `comp_run_n6_l`.

The registers are counted (`List.count`): each register of the need goes to
the `by` or to the rest of each `+lazy-leap` (`+need-cut` splits the need,
`+need-from` and `+cons-need` keep the registers, `+lazy-prune` drops only
forks and bonds), so the counts of the outputs add up to at most the count
of the input (`lzl_regs`), and the loop of `+leap` adds them up
(`leapLoop_regs`).  The labels are kept in order by the turns and filtered by
`+lazy-prune`, so no key appears twice at a level (`LKeys`) and every label
is one of the goal's.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- **What `+leap` keeps of the invariant**: the rest and every `by` meet
`LInv`, no register is in two of them or twice in one, and each is a
register of the goal's need. -/
def LeapInv (kr kb : Nat) (laz : Lazy CSet) (q r : Nomm) : Prop :=
  ∀ rest bys, leap laz q r = some (some (rest, bys)) →
    LInv kr kb rest ∧ (∀ b ∈ bys, LInv kr kb b) ∧ (lregs rest ++ bys.flatMap lregs).Nodup ∧
      ∀ y ∈ lregs rest ++ bys.flatMap lregs, y ∈ lregs laz

/-- The counts of `a` are at most those of `b`. -/
def RC (a b : List Nat) : Prop := ∀ y, a.count y ≤ b.count y

theorem rc_nodup {a b : List Nat} (h : RC a b) (hb : b.Nodup) : a.Nodup :=
  List.nodup_iff_count.2 fun y => Nat.le_trans (h y) (List.nodup_iff_count.1 hb y)

theorem rc_mem {a b : List Nat} (h : RC a b) {y : Nat} (hy : y ∈ a) : y ∈ b :=
  List.count_pos_iff.1 (Nat.lt_of_lt_of_le (List.count_pos_iff.2 hy) (h y))

/-! ## `WalkP` of a conjunction -/

section
variable {P Q : Nat → Sure CSet → Prop}

mutual
theorem walkP_and : ∀ (o : Nat) (laz : Lazy CSet), WalkP P o laz → WalkP Q o laz →
    WalkP (fun o s => P o s ∧ Q o s) o laz
  | o, Lazy.mk s fk bd, ⟨hs, hf, hb⟩, ⟨hs', hf', hb'⟩ => ⟨⟨hs, hs'⟩, walkPF_and fk hf hf', walkPB_and bd hb hb'⟩

theorem walkPF_and : ∀ (fk : List (Lazy.ForkE CSet)), WalkPF P fk → WalkPF Q fk →
    WalkPF (fun o s => P o s ∧ Q o s) fk
  | [], _, _ => trivial
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩, ⟨hy', hn', hr'⟩ =>
    ⟨walkP_and oy y hy hy', walkP_and on n hn hn', walkPF_and rest hr hr'⟩

theorem walkPB_and : ∀ (bd : List (Nat × Lazy CSet)), WalkPB P bd → WalkPB Q bd →
    WalkPB (fun o s => P o s ∧ Q o s) bd
  | [], _, _ => trivial
  | (ob, l) :: rest, ⟨hl, hr⟩, ⟨hl', hr'⟩ => ⟨walkP_and ob l hl hl', walkPB_and rest hr hr'⟩
end
end

/-- `LNB` from the looks and the registers. -/
theorem lnb_of {k : Nat} {laz : Lazy CSet} (hl : LAll CrLok laz) (hr : ∀ y ∈ lregs laz, y < k) :
    LAll (LNB k) laz :=
  walkP_and (P := fun _ s => CrLok s) (Q := fun _ s => ∀ r, NMem s.ned r → r < k) 0 laz hl
    (lall_regs (· < k) laz hr)

/-! ## The registers of the needs -/

theorem flatten_consNeed (a b : Need) : flattenNeed (consNeed a b) = flattenNeed a ++ flattenNeed b := by
  unfold consNeed
  split
  · rename_i h; obtain ⟨rfl, rfl⟩ := h; rfl
  · rfl

theorem needCut_regs : ∀ (ned : Need) (axe : Nat) (d c : Need), needCut axe ned = some (some (d, c)) →
    RC (flattenNeed d ++ flattenNeed c) (flattenNeed ned)
  | Need.none, axe, d, c, h, y => by
    simp only [needCut] at h
    split at h <;>
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [flattenNeed]
  | Need.this r, axe, d, c, h, y => by
    simp only [needCut] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [flattenNeed]
    · cases h
  | Need.both r hh t, axe, d, c, h, y => by
    simp only [needCut] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [flattenNeed]
    · cases h
  | Need.pair p q, axe, d, c, h, y => by
    simp only [needCut] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [flattenNeed]
    · split at h
      · cases h
      · split at h
        · cases e : needCut (mas axe) p with
          | none => simp [e] at h
          | some k =>
            cases k with
            | none => simp [e] at h
            | some k =>
              obtain ⟨d', c'⟩ := k
              simp only [e, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have := needCut_regs p _ d' c' e y
              simp only [List.count_append] at this
              simp only [flattenNeed, flatten_consNeed, List.count_append]
              omega
        · cases e : needCut (mas axe) q with
          | none => simp [e] at h
          | some k =>
            cases k with
            | none => simp [e] at h
            | some k =>
              obtain ⟨d', c'⟩ := k
              simp only [e, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have := needCut_regs q _ d' c' e y
              simp only [List.count_append] at this
              simp only [flattenNeed, flatten_consNeed, List.count_append]
              omega

theorem flatten_fromPath (ned : Need) : ∀ axe, flattenNeed (fromPath ned axe) = flattenNeed ned := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    rw [fromPath]
    split
    · rfl
    · have hm := mas_lt axe (by omega)
      split <;> simp [flattenNeed, ih _ hm]

theorem needFrom_regs {s : Nat} {don nf : Need} (h : needFrom s don = some nf) :
    flattenNeed nf = flattenNeed don := by
  unfold needFrom at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · cases h; exact flatten_fromPath don s

/-- The root needs of `by` and `rec` split the registers of the root need. -/
theorem lzSur_regs {p s : Nat} {sur sb sr : Sure CSet} {cut : Option (Need × Need)}
    (hc : needCut p sur.ned = some cut) (h : lzSur p s sur cut = some (sb, sr)) :
    RC (flattenNeed sb.ned ++ flattenNeed sr.ned) (flattenNeed sur.ned) := by
  intro y
  cases cut with
  | none =>
    simp only [lzSur, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Sure.bunt, flattenNeed]
  | some dr =>
    obtain ⟨don, rec⟩ := dr
    have hcut := needCut_regs _ _ don rec hc y
    simp only [lzSur] at h
    cases e1 : leapLok p s sur.lok with
    | none => simp [e1] at h
    | some lb =>
      obtain ⟨lb, lr⟩ := lb
      cases e2 : needFrom s don with
      | none => simp [e1, e2] at h
      | some nf =>
        simp only [e1, e2, Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [needFrom_regs e2]
        exact hcut

/-! ## `+lazy-leap` -/

section
variable {p s : Nat}

mutual
/-- **What `+lazy-leap` keeps**: the registers of `by` and `rec` together
are at most those of the need, the keys stay apart at each level, the labels
are the need's. -/
theorem lzl_inv : ∀ (laz b r : Lazy CSet), lazyLeap p s laz = some (b, r) →
    RC (lregs b ++ lregs r) (lregs laz) ∧ (LKeys laz → LKeys b ∧ LKeys r) ∧
      ∀ o ∈ llabs b ++ llabs r, o ∈ llabs laz
  | Lazy.mk sur fk bd, b, r, h => by
    rw [lazyLeap_eq] at h
    cases e1 : needCut p sur.ned with
    | none => simp [e1] at h
    | some cut =>
      cases e2 : lzSur p s sur cut with
      | none => simp [e1, e2] at h
      | some ss =>
        obtain ⟨sb, sr⟩ := ss
        cases e3 : fk.mapM (lfF p s) with
        | none => simp [e1, e2, e3] at h
        | some fs =>
          cases e4 : bd.mapM (lbF p s) with
          | none => simp [e1, e2, e3, e4] at h
          | some bs =>
            simp only [e1, e2, e3, e4, Option.bind_some, Option.map_some, Option.some.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hss := lzSur_regs e1 e2
            obtain ⟨fr, ef1, ef2, fk1, fl⟩ := lzl_inv_forks fk fs e3
            obtain ⟨br, eb1, eb2, bk1, bl⟩ := lzl_inv_bonds bd bs e4
            refine ⟨fun y => ?_, fun hk => ?_, fun o ho => ?_⟩
            · have h1 := prune_regs (Lazy.mk sb (fs.map Prod.fst) (bs.map Prod.fst)) y
              have h2 := prune_regs (Lazy.mk sr (fs.map Prod.snd) (bs.map Prod.snd)) y
              have h3 := hss y
              have h4 := fr y
              have h5 := br y
              simp only [lregs, List.count_append] at h1 h2 h3 h4 h5 ⊢
              omega
            · obtain ⟨k1, k2, k3, k4⟩ := hk
              obtain ⟨ff1, ff2⟩ := fk1 k3
              obtain ⟨bb1, bb2⟩ := bk1 k4
              refine ⟨prune_keys ⟨?_, ?_, ff1, bb1⟩, prune_keys ⟨?_, ?_, ff2, bb2⟩⟩
              · rw [ef1]; exact k1
              · rw [eb1]; exact k2
              · rw [ef2]; exact k1
              · rw [eb2]; exact k2
            · rw [List.mem_append] at ho
              have hf := fun o h => fl o (List.mem_append_left _ h)
              have hf' := fun o h => fl o (List.mem_append_right _ h)
              have hb := fun o h => bl o (List.mem_append_left _ h)
              have hb' := fun o h => bl o (List.mem_append_right _ h)
              rcases ho with ho | ho
              · have := prune_labs _ o ho
                simp only [llabs, List.mem_append] at this ⊢
                rcases this with e | e
                · exact Or.inl (hf o e)
                · exact Or.inr (hb o e)
              · have := prune_labs _ o ho
                simp only [llabs, List.mem_append] at this ⊢
                rcases this with e | e
                · exact Or.inl (hf' o e)
                · exact Or.inr (hb' o e)

theorem lzl_inv_forks : ∀ (fk : List (Lazy.ForkE CSet)) (fs : List (Lazy.ForkE CSet × Lazy.ForkE CSet)),
    fk.mapM (lfF p s) = some fs →
    RC (fregs (fs.map Prod.fst) ++ fregs (fs.map Prod.snd)) (fregs fk) ∧
      (fs.map Prod.fst).map (fun e => e.1.1) = fk.map (fun e => e.1.1) ∧
      (fs.map Prod.snd).map (fun e => e.1.1) = fk.map (fun e => e.1.1) ∧
      (FKeys fk → FKeys (fs.map Prod.fst) ∧ FKeys (fs.map Prod.snd)) ∧
      ∀ o ∈ flabs (fs.map Prod.fst) ++ flabs (fs.map Prod.snd), o ∈ flabs fk
  | [], fs, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨fun _ => Nat.le_refl _, rfl, rfl, fun _ => ⟨trivial, trivial⟩, fun o ho => by simp [flabs] at ho⟩
  | ((oy, y), (on, n)) :: rest, fs, h => by
    simp only [List.mapM_cons] at h
    cases e1 : lazyLeap p s y with
    | none => simp [lfF, e1] at h
    | some yy =>
      obtain ⟨yb, yr⟩ := yy
      cases e2 : lazyLeap p s n with
      | none => simp [lfF, e1, e2] at h
      | some nn =>
        obtain ⟨nb, nr⟩ := nn
        cases e3 : rest.mapM (lfF p s) with
        | none => simp [lfF, e1, e2, e3] at h
        | some rs =>
          simp [lfF, e1, e2, e3] at h
          subst h
          obtain ⟨ry, ky, ly⟩ := lzl_inv y yb yr e1
          obtain ⟨rn, kn, ln⟩ := lzl_inv n nb nr e2
          obtain ⟨rr, er1, er2, kr, lr⟩ := lzl_inv_forks rest rs e3
          refine ⟨fun x => ?_, ?_, ?_, fun ⟨hy, hn, hr⟩ => ?_, fun o ho => ?_⟩
          · have := ry x; have := rn x; have := rr x
            simp only [List.map_cons, fregs, List.count_append] at *
            omega
          · simp only [List.map_cons, er1]
          · simp only [List.map_cons, er2]
          · obtain ⟨ky1, ky2⟩ := ky hy
            obtain ⟨kn1, kn2⟩ := kn hn
            obtain ⟨kr1, kr2⟩ := kr hr
            exact ⟨⟨ky1, kn1, kr1⟩, ⟨ky2, kn2, kr2⟩⟩
          · simp only [List.map_cons, flabs, List.mem_cons, List.mem_append] at ho ⊢
            have ly1 := fun o h => ly o (List.mem_append_left _ h)
            have ly2 := fun o h => ly o (List.mem_append_right _ h)
            have ln1 := fun o h => ln o (List.mem_append_left _ h)
            have ln2 := fun o h => ln o (List.mem_append_right _ h)
            have lr1 := fun o h => lr o (List.mem_append_left _ h)
            have lr2 := fun o h => lr o (List.mem_append_right _ h)
            rcases ho with (e | e | e | e | e) | (e | e | e | e | e)
            · exact Or.inl e
            · exact Or.inr (Or.inl e)
            · exact Or.inr (Or.inr (Or.inl (ly1 o e)))
            · exact Or.inr (Or.inr (Or.inr (Or.inl (ln1 o e))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (lr1 o e))))
            · exact Or.inl e
            · exact Or.inr (Or.inl e)
            · exact Or.inr (Or.inr (Or.inl (ly2 o e)))
            · exact Or.inr (Or.inr (Or.inr (Or.inl (ln2 o e))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (lr2 o e))))

theorem lzl_inv_bonds : ∀ (bd : List (Nat × Lazy CSet)) (bs : List ((Nat × Lazy CSet) × (Nat × Lazy CSet))),
    bd.mapM (lbF p s) = some bs →
    RC (bregs (bs.map Prod.fst) ++ bregs (bs.map Prod.snd)) (bregs bd) ∧
      (bs.map Prod.fst).map (fun e => e.1) = bd.map (fun e => e.1) ∧
      (bs.map Prod.snd).map (fun e => e.1) = bd.map (fun e => e.1) ∧
      (BKeys bd → BKeys (bs.map Prod.fst) ∧ BKeys (bs.map Prod.snd)) ∧
      ∀ o ∈ blabs (bs.map Prod.fst) ++ blabs (bs.map Prod.snd), o ∈ blabs bd
  | [], bs, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨fun _ => Nat.le_refl _, rfl, rfl, fun _ => ⟨trivial, trivial⟩, fun o ho => by simp [blabs] at ho⟩
  | (ob, l) :: rest, bs, h => by
    simp only [List.mapM_cons] at h
    cases e1 : lazyLeap p s l with
    | none => simp [lbF, e1] at h
    | some bb =>
      obtain ⟨lb, lr⟩ := bb
      cases e3 : rest.mapM (lbF p s) with
      | none => simp [lbF, e1, e3] at h
      | some rs =>
        simp [lbF, e1, e3] at h
        subst h
        obtain ⟨rl, kl, ll⟩ := lzl_inv l lb lr e1
        obtain ⟨rr, er1, er2, kr, lrr⟩ := lzl_inv_bonds rest rs e3
        refine ⟨fun x => ?_, ?_, ?_, fun ⟨hl, hr⟩ => ?_, fun o ho => ?_⟩
        · have := rl x; have := rr x
          simp only [List.map_cons, bregs, List.count_append] at *
          omega
        · simp only [List.map_cons, er1]
        · simp only [List.map_cons, er2]
        · obtain ⟨kl1, kl2⟩ := kl hl
          obtain ⟨kr1, kr2⟩ := kr hr
          exact ⟨⟨kl1, kr1⟩, ⟨kl2, kr2⟩⟩
        · simp only [List.map_cons, blabs, List.mem_cons, List.mem_append] at ho ⊢
          have ll1 := fun o h => ll o (List.mem_append_left _ h)
          have ll2 := fun o h => ll o (List.mem_append_right _ h)
          have lr1 := fun o h => lrr o (List.mem_append_left _ h)
          have lr2 := fun o h => lrr o (List.mem_append_right _ h)
          rcases ho with (e | e | e) | (e | e | e)
          · exact Or.inl e
          · exact Or.inr (Or.inl (ll1 o e))
          · exact Or.inr (Or.inr (lr1 o e))
          · exact Or.inl e
          · exact Or.inr (Or.inl (ll2 o e))
          · exact Or.inr (Or.inr (lr2 o e))
end

end

/-! ## The loop of `+leap`, and `+leap` -/

theorem lkeys_sure (s s' : Sure CSet) (f : List (Lazy.ForkE CSet)) (b : List (Nat × Lazy CSet))
    (h : LKeys (Lazy.mk s f b)) : LKeys (Lazy.mk s' f b) := h

/-- **What the loop of `+leap` keeps**: the registers of the forks and bonds
of the final `lab` and of the `bys` together are at most those of the first
`lab` and `bys`; the keys and the labels likewise. -/
theorem leapLoop_inv (sur : Sure CSet) : ∀ (pas : List (Nat × Nat)) (lab : Lazy CSet) (bys : List (Lazy CSet))
    (rest : Lazy CSet) (out : List (Lazy CSet)), leapLoop sur pas lab bys = some (some (rest, out)) →
    RC (lregs rest ++ out.flatMap lregs) (flattenNeed sur.ned ++ lregs lab ++ bys.flatMap lregs) ∧
      (LKeys lab → (∀ b ∈ bys, LKeys b) → LKeys rest ∧ ∀ b ∈ out, LKeys b) ∧
      ∀ o ∈ llabs rest ++ out.flatMap llabs, o ∈ llabs lab ++ bys.flatMap llabs
  | [], lab, bys, rest, out, h => by
    simp only [leapLoop] at h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ls, lf, lb⟩ := lab
      refine ⟨fun y => ?_, fun hk hb => ⟨lkeys_sure ls sur lf lb hk, hb⟩, fun o ho => ?_⟩
      · simp only [Lazy.fork, Lazy.bond, lregs, List.count_append]
        omega
      · simpa [Lazy.fork, Lazy.bond, llabs] using ho
  | (p, s) :: pas, lab, bys, rest, out, h => by
    simp only [leapLoop] at h
    cases e : lazyLeap p s lab with
    | none => simp [e] at h
    | some br =>
      obtain ⟨b, r⟩ := br
      obtain ⟨rc, kk, ll⟩ := lzl_inv lab b r e
      simp only [e, Option.bind_some] at h
      split at h
      · exact leapLoop_inv sur pas lab bys rest out h
      · obtain ⟨rc', kk', ll'⟩ := leapLoop_inv sur pas r (b :: bys) rest out h
        refine ⟨fun y => ?_, fun hk hb => ?_, fun o ho => ?_⟩
        · have h1 := rc' y
          have h2 := rc y
          simp only [List.flatMap_cons, List.count_append] at h1 h2 ⊢
          omega
        · obtain ⟨k1, k2⟩ := kk hk
          refine kk' k2 fun b' hb' => ?_
          rcases List.mem_cons.1 hb' with rfl | hb'
          · exact k1
          · exact hb b' hb'
        · have := ll' o ho
          simp only [List.flatMap_cons, List.mem_append] at this ⊢
          rcases this with e | e | e
          · exact Or.inl (ll o (List.mem_append_right _ e))
          · exact Or.inl (ll o (List.mem_append_left _ e))
          · exact Or.inr e

/-- **What `+leap` keeps**, on the rest and the `bys`. -/
theorem leap_keeps {laz : Lazy CSet} {q r : Nomm} {rest : Lazy CSet} {out : List (Lazy CSet)}
    (h : leap laz q r = some (some (rest, out))) :
    RC (lregs rest ++ out.flatMap lregs) (lregs laz) ∧ (LKeys laz → LKeys rest ∧ ∀ b ∈ out, LKeys b) ∧
      ∀ o ∈ llabs rest ++ out.flatMap llabs, o ∈ llabs laz := by
  obtain ⟨sur, fk, bd⟩ := laz
  simp only [leap] at h
  split at h
  · cases h
  · cases ep : passBoth q r with
    | none => simp [ep] at h
    | some pas =>
      simp only [ep, Option.bind_some] at h
      obtain ⟨rc, kk, ll⟩ := leapLoop_inv _ pas _ [] rest out h
      refine ⟨fun y => ?_, fun hk => kk (lkeys_sure sur _ fk bd hk) fun _ hb => absurd hb List.not_mem_nil,
        fun o ho => ?_⟩
      · have := rc y
        simp only [Lazy.sure, Lazy.fork, Lazy.bond, lregs, Sure.bunt, flattenNeed, List.flatMap_nil,
          List.append_nil, List.nil_append, List.count_append] at this ⊢
        omega
      · simpa [Lazy.fork, Lazy.bond, llabs] using ll o ho

theorem nodup_of_flatMap : ∀ {l : List (Lazy CSet)}, (l.flatMap lregs).Nodup → ∀ b ∈ l, (lregs b).Nodup
  | [], _, b, hb => absurd hb List.not_mem_nil
  | a :: t, h, b, hb => by
    rw [List.flatMap_cons] at h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact (List.nodup_append.1 h).1
    · exact nodup_of_flatMap (List.nodup_append.1 h).2.1 b hb

/-- **`LeapInv` holds**: on a lazy need with `LInv` and branches with
`Bake.NoAx0`, what `+leap` returns meets `LInv`, its registers apart and the
goal's. -/
theorem leapInv {kr kb : Nat} {laz : Lazy CSet} {q r : Nomm} (hi : LInv kr kb laz) (hq : Bake.NoAx0 q)
    (hr : Bake.NoAx0 r) : LeapInv kr kb laz q r := by
  intro rest bys h
  obtain ⟨rc, hk, hl⟩ := leap_keeps h
  obtain ⟨cl1, cl2⟩ := leap_lall (lall_mono (fun _ h => h.1) hi.1) hq hr h
  have hnd := rc_nodup rc hi.2.1
  have hmem : ∀ y ∈ lregs rest ++ bys.flatMap lregs, y ∈ lregs laz := fun y hy => rc_mem rc hy
  have hlt : ∀ y ∈ lregs laz, y < kr := lnb_regs hi.1
  obtain ⟨kr1, kb1⟩ := hk hi.2.2.1
  have hnd' := List.nodup_append.1 hnd
  refine ⟨⟨lnb_of cl1 (fun y hy => hlt y (hmem y (List.mem_append_left _ hy))), hnd'.1, kr1,
      fun o ho => hi.2.2.2 o (hl o (List.mem_append_left _ ho))⟩,
    fun b hb => ⟨lnb_of (cl2 b hb) (fun y hy => hlt y (hmem y (List.mem_append_right _ (List.mem_flatMap.2 ⟨b, hb, hy⟩)))),
      nodup_of_flatMap hnd'.2.1 b hb, kb1 b hb,
      fun o ho => hi.2.2.2 o (hl o (List.mem_append_right _ (List.mem_flatMap.2 ⟨b, hb, ho⟩)))⟩, hnd, hmem⟩

end Compiler
end Formalization
