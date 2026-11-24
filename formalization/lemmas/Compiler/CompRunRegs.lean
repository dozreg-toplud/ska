import lemmas.Compiler.CompRunGoalL

/-!
# The registers, keys and labels of lazy needs through the helpers of `+run`

`LInv` of `CompRunGoalL.lean` asks, besides the looks and the registers below
the counter (`LAll (LNB ..)`, kept by `split_lnb`, `into_lnb`, `from_lnb`,
`past_lnb`, `copy_lnb` of `CompRunInvL.lean` and `CompCopyAll.lean`), that
no register occur twice (`(lregs laz).Nodup`), no key twice at a level
(`LKeys`), and every label be below the label counter.  Here these are
kept by `+lazy-prune`, `+from`, `+past`, `+split` and `+into`, on every lazy
need.

The registers are counted (`List.count`): `Sub I a b O` says that every
register occurs in `O` at most as often as in `I`, plus once if it is fresh
(in `[a, b)`).  `Sub` composes by adding counts (`sub_app`), so the order in
which a helper produces its parts does not matter, and with `I` below `a`
and with no register twice it gives `O` with no register twice
(`nodup_of_sub`) and made of registers of `I` and fresh ones
(`mem_of_sub`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Counting registers -/

/-- `1` on the fresh range `[a, b)`, `0` elsewhere. -/
def fr (a b x : Nat) : Nat := if a ≤ x ∧ x < b then 1 else 0

theorem fr_le_one (a b x : Nat) : fr a b x ≤ 1 := by unfold fr; split <;> omega

theorem fr_add {a b c x : Nat} (hab : a ≤ b) (hbc : b ≤ c) : fr a b x + fr b c x = fr a c x := by
  unfold fr; split <;> split <;> split <;> omega

theorem fr_mono {a b a' b' x : Nat} (ha : a' ≤ a) (hb : b ≤ b') : fr a b x ≤ fr a' b' x := by
  unfold fr; split <;> split <;> omega

theorem fr_lt {a b x : Nat} (h : x < a) : fr a b x = 0 := by unfold fr; split <;> omega

theorem fr_pos {a b x : Nat} (h : 0 < fr a b x) : a ≤ x ∧ x < b := by unfold fr at h; split at h <;> omega

/-- **`O` is made of the registers of `I` and of fresh registers** in
`[a, b)`: every register at most as often as in `I`, plus once if fresh. -/
def Sub (I : List Nat) (a b : Nat) (O : List Nat) : Prop := ∀ x, O.count x ≤ I.count x + fr a b x

theorem sub_of_nodup {I O : List Nat} {a b : Nat} (hO : O.Nodup) (hm : ∀ x ∈ O, x ∈ I ∨ (a ≤ x ∧ x < b)) :
    Sub I a b O := by
  intro x
  have h1 := List.nodup_iff_count.1 hO x
  by_cases hx : x ∈ O
  · rcases hm x hx with e | e
    · have := List.count_pos_iff.2 e; omega
    · have : fr a b x = 1 := by unfold fr; rw [if_pos e]
      omega
  · rw [List.count_eq_zero.2 hx]; omega

theorem nodup_of_sub {I O : List Nat} {a b : Nat} (h : Sub I a b O) (hI : I.Nodup) (hl : ∀ x ∈ I, x < a) :
    O.Nodup := by
  rw [List.nodup_iff_count]
  intro x
  have h1 := h x
  have h2 := List.nodup_iff_count.1 hI x
  by_cases hx : x ∈ I
  · rw [fr_lt (hl x hx)] at h1; omega
  · rw [List.count_eq_zero.2 hx] at h1; have := fr_le_one a b x; omega

theorem mem_of_sub {I O : List Nat} {a b : Nat} (h : Sub I a b O) {x : Nat} (hx : x ∈ O) :
    x ∈ I ∨ (a ≤ x ∧ x < b) := by
  have h1 := h x
  have h2 := List.count_pos_iff.2 hx
  by_cases hI : x ∈ I
  · exact Or.inl hI
  · rw [List.count_eq_zero.2 hI] at h1; exact Or.inr (fr_pos (by omega))

theorem sub_app {I1 I2 O1 O2 : List Nat} {a b c : Nat} (h1 : Sub I1 a b O1) (h2 : Sub I2 b c O2)
    (hab : a ≤ b) (hbc : b ≤ c) : Sub (I1 ++ I2) a c (O1 ++ O2) := by
  intro x
  have := h1 x; have := h2 x; have := fr_add (x := x) hab hbc
  simp only [List.count_append]; omega

theorem sub_widen {I O : List Nat} {a b a' b' : Nat} (h : Sub I a b O) (ha : a' ≤ a) (hb : b ≤ b') :
    Sub I a' b' O := fun x => by have := h x; have := fr_mono (x := x) ha hb; omega

theorem sub_refl (I : List Nat) (a b : Nat) : Sub I a b I := fun x => by omega

theorem sub_nil (I : List Nat) (a b : Nat) : Sub I a b [] := fun x => by simp

/-- `Sub` along smaller outputs and larger inputs (counts). -/
theorem sub_congr {I I' O O' : List Nat} {a b : Nat} (h : Sub I a b O) (hO : ∀ x, O'.count x ≤ O.count x)
    (hI : ∀ x, I.count x ≤ I'.count x) : Sub I' a b O' := fun x => by
  have := h x; have := hO x; have := hI x; omega

/-! ## The registers of the parts of a lazy need -/

section
variable {S : Type} [HoonSet S]

theorem lregs_mk (s : Sure S) (f : List (Lazy.ForkE S)) (b : List (Nat × Lazy S)) :
    lregs (Lazy.mk s f b) = flattenNeed s.ned ++ (fregs f ++ bregs b) := by
  simp only [lregs]

theorem lregs_ofSure (s : Sure S) : lregs (Lazy.ofSure s) = flattenNeed s.ned := by
  simp [Lazy.ofSure, lregs, fregs, bregs]

theorem fregs_append : ∀ (a b : List (Lazy.ForkE S)), fregs (a ++ b) = fregs a ++ fregs b
  | [], b => by simp [fregs]
  | ((oy, y), (on, n)) :: rest, b => by simp [fregs, fregs_append rest b]

theorem bregs_append : ∀ (a b : List (Nat × Lazy S)), bregs (a ++ b) = bregs a ++ bregs b
  | [], b => by simp [bregs]
  | (o, l) :: rest, b => by simp [bregs, bregs_append rest b]

theorem fregs_filter (p : Lazy.ForkE S → Bool) : ∀ f : List (Lazy.ForkE S), List.Sublist (fregs (f.filter p)) (fregs f)
  | [] => by simp [fregs]
  | ((oy, y), (on, n)) :: rest => by
    rw [List.filter_cons]
    split
    · simp only [fregs]
      exact ((fregs_filter p rest).append_left _).append_left _
    · simp only [fregs]
      exact ((fregs_filter p rest).trans (List.sublist_append_right _ _)).trans (List.sublist_append_right _ _)

theorem bregs_filter (p : Nat × Lazy S → Bool) : ∀ b : List (Nat × Lazy S), List.Sublist (bregs (b.filter p)) (bregs b)
  | [] => by simp [bregs]
  | (o, l) :: rest => by
    rw [List.filter_cons]
    split
    · simp only [bregs]; exact (bregs_filter p rest).append_left _
    · simp only [bregs]; exact (bregs_filter p rest).trans (List.sublist_append_right _ _)

/-- A list cut by a test and its negation: the counts add up. -/
theorem fregs_filter_split (p : Lazy.ForkE S → Bool) (x : Nat) : ∀ f : List (Lazy.ForkE S),
    (fregs (f.filter p)).count x + (fregs (f.filter (fun e => !p e))).count x = (fregs f).count x
  | [] => by simp [fregs]
  | ((oy, y), (on, n)) :: rest => by
    have ih := fregs_filter_split p x rest
    rw [List.filter_cons, List.filter_cons]
    cases hp : p ((oy, y), (on, n)) <;> simp [fregs, List.count_append] <;> omega

theorem bregs_filter_split (p : Nat × Lazy S → Bool) (x : Nat) : ∀ b : List (Nat × Lazy S),
    (bregs (b.filter p)).count x + (bregs (b.filter (fun e => !p e))).count x = (bregs b).count x
  | [] => by simp [bregs]
  | (o, l) :: rest => by
    have ih := bregs_filter_split p x rest
    rw [List.filter_cons, List.filter_cons]
    cases hp : p (o, l) <;> simp [bregs, List.count_append] <;> omega

/-! ## Keys and labels of the parts -/

theorem llabs_mk (s : Sure S) (f : List (Lazy.ForkE S)) (b : List (Nat × Lazy S)) :
    llabs (Lazy.mk s f b) = flabs f ++ blabs b := by
  simp only [llabs]

theorem llabs_ofSure (s : Sure S) : llabs (Lazy.ofSure s) = [] := by
  simp [Lazy.ofSure, llabs, flabs, blabs]

theorem lkeys_ofSure (s : Sure S) : LKeys (Lazy.ofSure s) := by
  simp [Lazy.ofSure, LKeys, FKeys, BKeys]

theorem fkeys_filter (p : Lazy.ForkE S → Bool) : ∀ f : List (Lazy.ForkE S), FKeys f → FKeys (f.filter p)
  | [], _ => trivial
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩ => by
    rw [List.filter_cons]
    split
    · exact ⟨hy, hn, fkeys_filter p rest hr⟩
    · exact fkeys_filter p rest hr

theorem bkeys_filter (p : Nat × Lazy S → Bool) : ∀ b : List (Nat × Lazy S), BKeys b → BKeys (b.filter p)
  | [], _ => trivial
  | (o, l) :: rest, ⟨hl, hr⟩ => by
    rw [List.filter_cons]
    split
    · exact ⟨hl, bkeys_filter p rest hr⟩
    · exact bkeys_filter p rest hr

theorem fkeys_append : ∀ (a b : List (Lazy.ForkE S)), FKeys a → FKeys b → FKeys (a ++ b)
  | [], b, _, hb => hb
  | ((oy, y), (on, n)) :: rest, b, ⟨hy, hn, hr⟩, hb => ⟨hy, hn, fkeys_append rest b hr hb⟩

theorem bkeys_append : ∀ (a b : List (Nat × Lazy S)), BKeys a → BKeys b → BKeys (a ++ b)
  | [], b, _, hb => hb
  | (o, l) :: rest, b, ⟨hl, hr⟩, hb => ⟨hl, bkeys_append rest b hr hb⟩

theorem flabs_filter (p : Lazy.ForkE S → Bool) : ∀ f : List (Lazy.ForkE S), ∀ o ∈ flabs (f.filter p), o ∈ flabs f
  | [], o, h => by simp [flabs] at h
  | ((oy, y), (on, n)) :: rest, o, h => by
    rw [List.filter_cons] at h
    simp only [flabs, List.mem_cons, List.mem_append] at h ⊢
    split at h
    · simp only [flabs, List.mem_cons, List.mem_append] at h
      rcases h with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (flabs_filter p rest o h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (flabs_filter p rest o h))))

theorem blabs_filter (p : Nat × Lazy S → Bool) : ∀ b : List (Nat × Lazy S), ∀ o ∈ blabs (b.filter p), o ∈ blabs b
  | [], o, h => by simp [blabs] at h
  | (ob, l) :: rest, o, h => by
    rw [List.filter_cons] at h
    simp only [blabs, List.mem_cons, List.mem_append] at h ⊢
    split at h
    · simp only [blabs, List.mem_cons, List.mem_append] at h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (blabs_filter p rest o h))
    · exact Or.inr (Or.inr (blabs_filter p rest o h))

theorem flabs_append : ∀ (a b : List (Lazy.ForkE S)), flabs (a ++ b) = flabs a ++ flabs b
  | [], b => by simp [flabs]
  | ((oy, y), (on, n)) :: rest, b => by simp [flabs, flabs_append rest b]

theorem blabs_append : ∀ (a b : List (Nat × Lazy S)), blabs (a ++ b) = blabs a ++ blabs b
  | [], b => by simp [blabs]
  | (o, l) :: rest, b => by simp [blabs, blabs_append rest b]

/-- The keys of a fork list are among its labels. -/
theorem fkey_flabs : ∀ (f : List (Lazy.ForkE S)), ∀ k ∈ f.map (fun e => e.1.1), k ∈ flabs f
  | [], k, h => by simp at h
  | ((oy, y), (on, n)) :: rest, k, h => by
    simp only [List.map_cons, List.mem_cons] at h
    simp only [flabs, List.mem_cons, List.mem_append]
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (fkey_flabs rest k h))))

theorem bkey_blabs : ∀ (b : List (Nat × Lazy S)), ∀ k ∈ b.map (fun e => e.1), k ∈ blabs b
  | [], k, h => by simp at h
  | (o, l) :: rest, k, h => by
    simp only [List.map_cons, List.mem_cons] at h
    simp only [blabs, List.mem_cons, List.mem_append]
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (bkey_blabs rest k h))

end

/-! ## `+lazy-prune` -/

theorem prune_sublist (l : Lazy CSet) : List.Sublist (lregs (Lazy.lazyPrune l)) (lregs l) := by
  obtain ⟨s, f, b⟩ := l
  simp only [Lazy.lazyPrune, Lazy.sure, Lazy.fork, Lazy.bond, lregs]
  exact ((fregs_filter _ f).append (bregs_filter _ b)).append_left _

theorem prune_regs (l : Lazy CSet) (x : Nat) : (lregs (Lazy.lazyPrune l)).count x ≤ (lregs l).count x :=
  (prune_sublist l).count_le x

theorem prune_keys {l : Lazy CSet} (h : LKeys l) : LKeys (Lazy.lazyPrune l) := by
  obtain ⟨s, f, b⟩ := l
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨((List.filter_sublist).map _).nodup h1, ((List.filter_sublist).map _).nodup h2,
    fkeys_filter _ f h3, bkeys_filter _ b h4⟩

theorem prune_labs (l : Lazy CSet) : ∀ o ∈ llabs (Lazy.lazyPrune l), o ∈ llabs l := by
  obtain ⟨s, f, b⟩ := l
  intro o h
  simp only [Lazy.lazyPrune, Lazy.sure, Lazy.fork, Lazy.bond, llabs, List.mem_append] at h ⊢
  rcases h with h | h
  · exact Or.inl (flabs_filter _ f o h)
  · exact Or.inr (blabs_filter _ b o h)

/-! ## `+from`: the registers, keys and labels are kept -/

theorem fromSure_regs {axe : Nat} {s s' : Sure CSet} (h : fromSure axe s = some s') :
    flattenNeed s'.ned = flattenNeed s.ned := by
  unfold fromSure at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · simp only [Option.some.injEq] at h
        subst h
        rename_i h2 _
        simp [h2, flattenNeed]
    · simp only [Option.some.injEq] at h
      subst h
      exact flatten_fromPath _ _
where
  flatten_fromPath (ned : Need) : ∀ axe, flattenNeed (fromPath ned axe) = flattenNeed ned := by
    intro axe
    induction axe using Nat.strongRecOn with
    | ind axe ih =>
      rw [fromPath]
      split
      · rfl
      · split
        · simp [flattenNeed, ih (mas axe) (mas_lt axe (by omega))]
        · simp [flattenNeed, ih (mas axe) (mas_lt axe (by omega))]

mutual
/-- **`+from` keeps the registers, the keys and the labels** of every lazy
need. -/
theorem from_regs (axe : Nat) : ∀ (laz laz' : Lazy CSet), Lazy.fromL axe laz = some laz' →
    lregs laz' = lregs laz ∧ (LKeys laz → LKeys laz') ∧ llabs laz' = llabs laz
  | Lazy.mk s f b, laz', e => by
    simp only [Lazy.fromL] at e
    split at e
    · rename_i hfb
      obtain ⟨s', e1, rfl⟩ := Option.map_eq_some_iff.mp e
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hfb
      obtain ⟨rfl, rfl⟩ := hfb
      refine ⟨by simp [lregs_ofSure, lregs, fregs, bregs, fromSure_regs e1], fun _ => lkeys_ofSure _, ?_⟩
      simp [llabs_ofSure, llabs, flabs, blabs]
    · obtain ⟨s', e1, e⟩ := Option.bind_eq_some_iff.mp e
      obtain ⟨f', e2, e⟩ := Option.bind_eq_some_iff.mp e
      obtain ⟨b', e3, rfl⟩ := Option.map_eq_some_iff.mp e
      obtain ⟨rf, kf, mf, lf⟩ := from_forks axe f f' e2
      obtain ⟨rb, kb, mb, lb⟩ := from_bonds axe b b' e3
      refine ⟨by simp [lregs, fromSure_regs e1, rf, rb], fun ⟨h1, h2, h3, h4⟩ => ⟨mf ▸ h1, mb ▸ h2, kf h3, kb h4⟩,
        by simp [llabs, lf, lb]⟩

theorem from_forks (axe : Nat) : ∀ (f f' : List (Lazy.ForkE CSet)), Lazy.fromForks axe f = some f' →
    fregs f' = fregs f ∧ (FKeys f → FKeys f') ∧ f'.map (fun e => e.1.1) = f.map (fun e => e.1.1) ∧
      flabs f' = flabs f
  | [], f', e => by simp only [Lazy.fromForks, Option.some.injEq] at e; subst e; exact ⟨rfl, id, rfl, rfl⟩
  | ((oy, y), (on, n)) :: rest, f', e => by
    simp only [Lazy.fromForks] at e
    obtain ⟨y', e1, e⟩ := Option.bind_eq_some_iff.mp e
    obtain ⟨n', e2, e⟩ := Option.bind_eq_some_iff.mp e
    obtain ⟨r', e3, rfl⟩ := Option.map_eq_some_iff.mp e
    obtain ⟨ry, ky, ly⟩ := from_regs axe y y' e1
    obtain ⟨rn, kn, ln⟩ := from_regs axe n n' e2
    obtain ⟨rr, kr, mr, lr⟩ := from_forks axe rest r' e3
    exact ⟨by simp [fregs, ry, rn, rr], fun ⟨a, b, c⟩ => ⟨ky a, kn b, kr c⟩, by simp [mr], by simp [flabs, ly, ln, lr]⟩

theorem from_bonds (axe : Nat) : ∀ (b b' : List (Nat × Lazy CSet)), Lazy.fromBonds axe b = some b' →
    bregs b' = bregs b ∧ (BKeys b → BKeys b') ∧ b'.map (fun e => e.1) = b.map (fun e => e.1) ∧
      blabs b' = blabs b
  | [], b', e => by simp only [Lazy.fromBonds, Option.some.injEq] at e; subst e; exact ⟨rfl, id, rfl, rfl⟩
  | (o, l) :: rest, b', e => by
    simp only [Lazy.fromBonds] at e
    obtain ⟨l', e1, e⟩ := Option.bind_eq_some_iff.mp e
    obtain ⟨r', e2, rfl⟩ := Option.map_eq_some_iff.mp e
    obtain ⟨rl, kl, ll⟩ := from_regs axe l l' e1
    obtain ⟨rr, kr, mr, lr⟩ := from_bonds axe rest r' e2
    exact ⟨by simp [bregs, rl, rr], fun ⟨a, b⟩ => ⟨kl a, kr b⟩, by simp [mr], by simp [blabs, ll, lr]⟩
end

/-! ## `+past` -/

/-- **`+past` keeps the registers**, keeps the keys and the labels below the
counter when they are, and does not lower the counters. -/
theorem past_regs {cod : Bell → Option Bool} {nex nex' : NextL CSet} {nom : Nomm} {region : List Nat}
    {g g' : Gen (TreapMap mugF)} (h : pastL cod nex nom region g = some (nex', g')) :
    lregs nex'.laz = lregs nex.laz ∧ g.re = g'.re ∧ g.bo ≤ g'.bo ∧ g'.drop = g.drop ∧
      (LKeys nex.laz → (∀ o ∈ llabs nex.laz, o < g.bo) → LKeys nex'.laz ∧ ∀ o ∈ llabs nex'.laz, o < g'.bo) ∧
      (nex'.th = nex.th ∨ nex'.th = jmp0 g.bo) := by
  obtain ⟨⟨s, fk, bd⟩, th⟩ := nex
  simp only [pastL] at h
  split at h
  · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, Nat.le_refl _, rfl, fun a b => ⟨a, b⟩, Or.inl rfl⟩
  · rcases hh : hinted cod nom with _ | _ | _
    · simp [hh] at h
    · simp only [hh, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, Nat.le_refl _, rfl, fun a b => ⟨a, b⟩, Or.inl rfl⟩
    · simp only [hh] at h
      obtain ⟨o1, g1, e1, h⟩ := bind_some h
      obtain ⟨u, g2, e2, h⟩ := bind_some h
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [emit_apply] at e1
      simp only [Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      simp only [setTag, Option.some.injEq, Prod.mk.injEq] at e2
      obtain ⟨-, rfl⟩ := e2
      have hb : (if (g.emitted ⟨[], [], Termin.hop th⟩).drop = true then g.emitted ⟨[], [], Termin.hop th⟩ else
          { g.emitted ⟨[], [], Termin.hop th⟩ with
            tags := HoonMap.put (g.emitted ⟨[], [], Termin.hop th⟩).tags g.bo region }).bo = g.bo + 1 := by
        split <;> simp [emitted_bo]
      have hr : (if (g.emitted ⟨[], [], Termin.hop th⟩).drop = true then g.emitted ⟨[], [], Termin.hop th⟩ else
          { g.emitted ⟨[], [], Termin.hop th⟩ with
            tags := HoonMap.put (g.emitted ⟨[], [], Termin.hop th⟩).tags g.bo region }).re = g.re := by
        split <;> simp [emitted_re]
      have hd : (if (g.emitted ⟨[], [], Termin.hop th⟩).drop = true then g.emitted ⟨[], [], Termin.hop th⟩ else
          { g.emitted ⟨[], [], Termin.hop th⟩ with
            tags := HoonMap.put (g.emitted ⟨[], [], Termin.hop th⟩).tags g.bo region }).drop = g.drop := by
        split <;> simp [emitted_drop]
      refine ⟨by simp [lregs, Sure.bunt, flattenNeed, fregs, bregs], hr.symm, by rw [hb]; omega, hd,
        fun ⟨k1, k2, k3, k4⟩ hl => ?_, Or.inr rfl⟩
      rw [hb]
      simp only [llabs, flabs, blabs] at hl
      refine ⟨⟨by simp, ?_, trivial, ⟨k1, by simp, k3, trivial⟩, k4⟩, ?_⟩
      · simp only [List.map_cons, List.nodup_cons]
        refine ⟨fun hm => ?_, k2⟩
        have := hl g.bo (List.mem_append_right _ (bkey_blabs bd g.bo hm))
        omega
      · intro o ho
        simp only [llabs, flabs, blabs, List.nil_append, List.mem_cons, List.mem_append, List.append_nil] at ho
        rcases ho with ho | ho | ho
        · omega
        · have := hl o (List.mem_append_left _ ho); omega
        · have := hl o (List.mem_append_right _ ho); omega

end Compiler
end Formalization

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Two and three parts -/

theorem sub_two {A B H1 T1 H2 T2 : List Nat} {a b c : Nat} (h1 : Sub A a b (H1 ++ T1)) (h2 : Sub B b c (H2 ++ T2))
    (hab : a ≤ b) (hbc : b ≤ c) : Sub (A ++ B) a c ((H1 ++ H2) ++ (T1 ++ T2)) := by
  intro x
  have e1 := h1 x; have e2 := h2 x; have := fr_add (x := x) hab hbc
  simp only [List.count_append] at e1 e2 ⊢; omega

theorem sub_three {A B C H1 T1 H2 T2 H3 T3 : List Nat} {a b c d : Nat} (h1 : Sub A a b (H1 ++ T1))
    (h2 : Sub B b c (H2 ++ T2)) (h3 : Sub C c d (H3 ++ T3)) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    Sub (A ++ (B ++ C)) a d ((H1 ++ (H2 ++ H3)) ++ (T1 ++ (T2 ++ T3))) := by
  intro x
  have e1 := h1 x; have e2 := h2 x; have e3 := h3 x
  have := fr_add (x := x) hab hbc; have := fr_add (x := x) (Nat.le_trans hab hbc) hcd
  simp only [List.count_append] at e1 e2 e3 ⊢; omega

/-- The parts of a list with no register twice and below a bound. -/
theorem nodup_below_left {A B : List Nat} {k : Nat} (hn : (A ++ B).Nodup) (hb : ∀ x ∈ A ++ B, x < k) :
    A.Nodup ∧ ∀ x ∈ A, x < k :=
  ⟨(List.nodup_append.1 hn).1, fun x hx => hb x (List.mem_append_left _ hx)⟩

theorem nodup_below_right {A B : List Nat} {k : Nat} (hn : (A ++ B).Nodup) (hb : ∀ x ∈ A ++ B, x < k) :
    B.Nodup ∧ ∀ x ∈ B, x < k :=
  ⟨(List.nodup_append.1 hn).2.1, fun x hx => hb x (List.mem_append_right _ hx)⟩

/-! ## `+split` -/

/-- The two halves of a sure need, from the facts of `splitNeed_spec`. -/
theorem sure_halves_sub {ned d r : Need} {a b : Nat}
    (md : ∀ y, NMem d y → NMem ned y ∨ (a ≤ y ∧ y < b)) (mr : ∀ y, NMem r y → NMem ned y ∨ (a ≤ y ∧ y < b))
    (dd : Distinct d) (dr : Distinct r) (ap : ∀ y, NMem d y → ¬ NMem r y) :
    Sub (flattenNeed ned) a b (flattenNeed d ++ flattenNeed r) := by
  apply sub_of_nodup
  · rw [List.nodup_append]
    exact ⟨(distinct_iff_nodup d).1 dd, (distinct_iff_nodup r).1 dr,
      fun x hx y hy e => ap x ((mem_flat d x).1 hx) (e ▸ (mem_flat r y).1 hy)⟩
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · rcases md x ((mem_flat d x).1 hx) with e | e
      · exact Or.inl ((mem_flat ned x).2 e)
      · exact Or.inr e
    · rcases mr x ((mem_flat r x).1 hx) with e | e
      · exact Or.inl ((mem_flat ned x).2 e)
      · exact Or.inr e

theorem splitSure_sub {s sh st : Sure CSet} {o : Nat} {g g' : Gen (TreapMap mugF)}
    (hn : (flattenNeed s.ned).Nodup) (hb : ∀ x ∈ flattenNeed s.ned, x < g.re)
    (h : splitSure s o g = some ((sh, st), g')) :
    g.re ≤ g'.re ∧ Sub (flattenNeed s.ned) g.re g'.re (flattenNeed sh.ned ++ flattenNeed st.ned) := by
  simp only [splitSure] at h
  obtain ⟨⟨lh, lt⟩, hl, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨nh, nt⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  obtain ⟨-, -, le, -, md, mr, sem, -⟩ := splitNeed_spec h3
  obtain ⟨dd, dr, ap, -⟩ := sem ((distinct_iff_nodup _).2 hn) (fun y hy => hb y ((mem_flat _ y).2 hy))
  exact ⟨le, sure_halves_sub md mr dd dr ap⟩

/-- What `+split` (and `+into`) make of a lazy need: the counter grows, the
halves are made of its registers and fresh ones, the keys and labels are
kept. -/
structure HalvesOK (laz h t : Lazy CSet) (a b : Nat) : Prop where
  le : a ≤ b
  sub : Sub (lregs laz) a b (lregs h ++ lregs t)
  keys : LKeys laz → LKeys h ∧ LKeys t
  labs : ∀ o, (o ∈ llabs h ∨ o ∈ llabs t) → o ∈ llabs laz

structure HalvesF (f fh ft : List (Lazy.ForkE CSet)) (a b : Nat) : Prop where
  le : a ≤ b
  sub : Sub (fregs f) a b (fregs fh ++ fregs ft)
  keys : FKeys f → FKeys fh ∧ FKeys ft
  mh : fh.map (fun e => e.1.1) = f.map (fun e => e.1.1)
  mt : ft.map (fun e => e.1.1) = f.map (fun e => e.1.1)
  labs : ∀ o, (o ∈ flabs fh ∨ o ∈ flabs ft) → o ∈ flabs f

structure HalvesB (b bh bt : List (Nat × Lazy CSet)) (a c : Nat) : Prop where
  le : a ≤ c
  sub : Sub (bregs b) a c (bregs bh ++ bregs bt)
  keys : BKeys b → BKeys bh ∧ BKeys bt
  mh : bh.map (fun e => e.1) = b.map (fun e => e.1)
  mt : bt.map (fun e => e.1) = b.map (fun e => e.1)
  labs : ∀ o, (o ∈ blabs bh ∨ o ∈ blabs bt) → o ∈ blabs b

/-- The root and the parts, pruned: the step common to `+split` and `+into`. -/
theorem halves_mk {s sh st : Sure CSet} {f fh ft : List (Lazy.ForkE CSet)} {b bh bt : List (Nat × Lazy CSet)}
    {a1 a2 a3 a4 : Nat} (S1 : a1 ≤ a2 ∧ Sub (flattenNeed s.ned) a1 a2 (flattenNeed sh.ned ++ flattenNeed st.ned))
    (F : HalvesF f fh ft a2 a3) (B : HalvesB b bh bt a3 a4) :
    HalvesOK (Lazy.mk s f b) (Lazy.lazyPrune (Lazy.mk sh fh bh)) (Lazy.lazyPrune (Lazy.mk st ft bt)) a1 a4 := by
  refine ⟨by have := F.le; have := B.le; omega, ?_, ?_, ?_⟩
  · have T := sub_three S1.2 F.sub B.sub S1.1 F.le B.le
    refine sub_congr T (fun x => ?_) (fun x => by simp only [lregs, Nat.le_refl])
    have p1 := prune_regs (Lazy.mk sh fh bh) x
    have p2 := prune_regs (Lazy.mk st ft bt) x
    simp only [lregs, List.count_append] at p1 p2 ⊢
    omega
  · rintro ⟨k1, k2, k3, k4⟩
    obtain ⟨fh', ft'⟩ := F.keys k3
    obtain ⟨bh', bt'⟩ := B.keys k4
    exact ⟨prune_keys ⟨by rw [F.mh]; exact k1, by rw [B.mh]; exact k2, fh', bh'⟩,
      prune_keys ⟨by rw [F.mt]; exact k1, by rw [B.mt]; exact k2, ft', bt'⟩⟩
  · intro o ho
    simp only [llabs, List.mem_append]
    rcases ho with ho | ho
    · have := prune_labs _ o ho
      simp only [llabs, List.mem_append] at this
      rcases this with e | e
      · exact Or.inl (F.labs o (Or.inl e))
      · exact Or.inr (B.labs o (Or.inl e))
    · have := prune_labs _ o ho
      simp only [llabs, List.mem_append] at this
      rcases this with e | e
      · exact Or.inl (F.labs o (Or.inr e))
      · exact Or.inr (B.labs o (Or.inr e))

/-- A fork-free need's halves. -/
theorem halves_ofSure {s sh st : Sure CSet} {a b : Nat}
    (S1 : a ≤ b ∧ Sub (flattenNeed s.ned) a b (flattenNeed sh.ned ++ flattenNeed st.ned)) :
    HalvesOK (Lazy.mk s [] []) (Lazy.ofSure sh) (Lazy.ofSure st) a b := by
  refine ⟨S1.1, ?_, fun _ => ⟨lkeys_ofSure _, lkeys_ofSure _⟩, fun o ho => ?_⟩
  · simpa [lregs_ofSure, lregs, fregs, bregs] using S1.2
  · simp [llabs_ofSure] at ho

theorem halvesF_cons {oy on : Nat} {y yh yt n nh nt : Lazy CSet} {rest rh rt : List (Lazy.ForkE CSet)}
    {a1 a2 a3 a4 : Nat} (Y : HalvesOK y yh yt a1 a2) (N : HalvesOK n nh nt a2 a3) (R : HalvesF rest rh rt a3 a4) :
    HalvesF (((oy, y), (on, n)) :: rest) (((oy, yh), (on, nh)) :: rh) (((oy, yt), (on, nt)) :: rt) a1 a4 := by
  refine ⟨by have := Y.le; have := N.le; have := R.le; omega, ?_, ?_, by simp [R.mh], by simp [R.mt], ?_⟩
  · simpa only [fregs] using sub_three Y.sub N.sub R.sub Y.le N.le R.le
  · rintro ⟨ky, kn, kr⟩
    exact ⟨⟨(Y.keys ky).1, (N.keys kn).1, (R.keys kr).1⟩, ⟨(Y.keys ky).2, (N.keys kn).2, (R.keys kr).2⟩⟩
  · intro o ho
    simp only [flabs, List.mem_cons, List.mem_append] at ho ⊢
    rcases ho with (e | e | e | e | e) | (e | e | e | e | e)
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl (Y.labs o (Or.inl e))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (N.labs o (Or.inl e)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (R.labs o (Or.inl e)))))
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl (Y.labs o (Or.inr e))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (N.labs o (Or.inr e)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (R.labs o (Or.inr e)))))

theorem halvesB_cons {ob : Nat} {l lh lt : Lazy CSet} {rest rh rt : List (Nat × Lazy CSet)}
    {a1 a2 a3 : Nat} (L : HalvesOK l lh lt a1 a2) (R : HalvesB rest rh rt a2 a3) :
    HalvesB ((ob, l) :: rest) ((ob, lh) :: rh) ((ob, lt) :: rt) a1 a3 := by
  refine ⟨by have := L.le; have := R.le; omega, ?_, ?_, by simp [R.mh], by simp [R.mt], ?_⟩
  · simpa only [bregs] using sub_two L.sub R.sub L.le R.le
  · rintro ⟨kl, kr⟩
    exact ⟨⟨(L.keys kl).1, (R.keys kr).1⟩, ⟨(L.keys kl).2, (R.keys kr).2⟩⟩
  · intro o ho
    simp only [blabs, List.mem_cons, List.mem_append] at ho ⊢
    rcases ho with (e | e | e) | (e | e | e)
    · exact Or.inl e
    · exact Or.inr (Or.inl (L.labs o (Or.inl e)))
    · exact Or.inr (Or.inr (R.labs o (Or.inl e)))
    · exact Or.inl e
    · exact Or.inr (Or.inl (L.labs o (Or.inr e)))
    · exact Or.inr (Or.inr (R.labs o (Or.inr e)))

mutual
/-- **`+split` on every lazy need** with no register twice and below the
counter: `HalvesOK`. -/
theorem split_halves : ∀ (laz : Lazy CSet) (o : Nat) (g g' : Gen (TreapMap mugF)) (h t : Lazy CSet),
    (lregs laz).Nodup → (∀ x ∈ lregs laz, x < g.re) → Lazy.splitLoop laz o g = some ((h, t), g') →
    HalvesOK laz h t g.re g'.re
  | Lazy.mk s f b, o, g, g', h, t, hn, hb, e => by
    simp only [Lazy.splitLoop] at e
    obtain ⟨⟨sh, st⟩, g1, e1, e⟩ := bind_some e
    have hn' := hn; have hb' := hb
    simp only [lregs] at hn' hb'
    obtain ⟨n1, b1⟩ := nodup_below_left hn' hb'
    obtain ⟨n23, b23⟩ := nodup_below_right hn' hb'
    obtain ⟨n2, b2⟩ := nodup_below_left n23 b23
    obtain ⟨n3, b3⟩ := nodup_below_right n23 b23
    have S1 := splitSure_sub n1 b1 e1
    split at e
    · rename_i hfb
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hfb
      obtain ⟨rfl, rfl⟩ := hfb
      exact halves_ofSure S1
    · obtain ⟨⟨fh, ft⟩, g2, e2, e⟩ := bind_some e
      have F := split_forks f g1 g2 fh ft n2 (fun x hx => Nat.lt_of_lt_of_le (b2 x hx) S1.1) e2
      obtain ⟨⟨bh, bt⟩, g3, e3, e⟩ := bind_some e
      have B := split_bonds b g2 g3 bh bt n3 (fun x hx => Nat.lt_of_lt_of_le (b3 x hx) (Nat.le_trans S1.1 F.le)) e3
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
      exact halves_mk S1 F B

theorem split_forks : ∀ (f : List (Lazy.ForkE CSet)) (g g' : Gen (TreapMap mugF)) (fh ft : List (Lazy.ForkE CSet)),
    (fregs f).Nodup → (∀ x ∈ fregs f, x < g.re) → Lazy.splitForks f g = some ((fh, ft), g') →
    HalvesF f fh ft g.re g'.re
  | [], g, g', fh, ft, _, _, e => by
    simp only [Lazy.splitForks, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨Nat.le_refl _, sub_nil _ _ _, fun _ => ⟨trivial, trivial⟩, rfl, rfl, fun o ho => by simp [flabs] at ho⟩
  | ((oy, y), (on, n)) :: rest, g, g', fh, ft, hn, hb, e => by
    simp only [Lazy.splitForks] at e
    have hn' := hn; have hb' := hb
    simp only [fregs] at hn' hb'
    obtain ⟨n1, b1⟩ := nodup_below_left hn' hb'
    obtain ⟨n23, b23⟩ := nodup_below_right hn' hb'
    obtain ⟨n2, b2⟩ := nodup_below_left n23 b23
    obtain ⟨n3, b3⟩ := nodup_below_right n23 b23
    obtain ⟨⟨yh, yt⟩, g1, e1, e⟩ := bind_some e
    have Y := split_halves y oy g g1 yh yt n1 b1 e1
    obtain ⟨⟨nh, nt⟩, g2, e2, e⟩ := bind_some e
    have N := split_halves n on g1 g2 nh nt n2 (fun x hx => Nat.lt_of_lt_of_le (b2 x hx) Y.le) e2
    obtain ⟨⟨rh, rt⟩, g3, e3, e⟩ := bind_some e
    have R := split_forks rest g2 g3 rh rt n3 (fun x hx => Nat.lt_of_lt_of_le (b3 x hx) (Nat.le_trans Y.le N.le)) e3
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact halvesF_cons Y N R

theorem split_bonds : ∀ (b : List (Nat × Lazy CSet)) (g g' : Gen (TreapMap mugF)) (bh bt : List (Nat × Lazy CSet)),
    (bregs b).Nodup → (∀ x ∈ bregs b, x < g.re) → Lazy.splitBonds b g = some ((bh, bt), g') →
    HalvesB b bh bt g.re g'.re
  | [], g, g', bh, bt, _, _, e => by
    simp only [Lazy.splitBonds, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨Nat.le_refl _, sub_nil _ _ _, fun _ => ⟨trivial, trivial⟩, rfl, rfl, fun o ho => by simp [blabs] at ho⟩
  | (ob, l) :: rest, g, g', bh, bt, hn, hb, e => by
    simp only [Lazy.splitBonds] at e
    have hn' := hn; have hb' := hb
    simp only [bregs] at hn' hb'
    obtain ⟨n1, b1⟩ := nodup_below_left hn' hb'
    obtain ⟨n2, b2⟩ := nodup_below_right hn' hb'
    obtain ⟨⟨lh, lt⟩, g1, e1, e⟩ := bind_some e
    have L := split_halves l ob g g1 lh lt n1 b1 e1
    obtain ⟨⟨rh, rt⟩, g2, e2, e⟩ := bind_some e
    have R := split_bonds rest g1 g2 rh rt n2 (fun x hx => Nat.lt_of_lt_of_le (b2 x hx) L.le) e2
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact halvesB_cons L R
end

/-! ## `+into` -/

theorem intoSure_sub {axe : Nat} {s sd sr : Sure CSet} {o : Nat} {g g' : Gen (TreapMap mugF)}
    (hn : (flattenNeed s.ned).Nodup) (hb : ∀ x ∈ flattenNeed s.ned, x < g.re)
    (h : intoSure axe s o g = some ((sd, sr), g')) :
    g.re ≤ g'.re ∧ Sub (flattenNeed s.ned) g.re g'.re (flattenNeed sd.ned ++ flattenNeed sr.ned) := by
  simp only [intoSure] at h
  obtain ⟨⟨ld, lr⟩, hl, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨nd, nr⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  obtain ⟨-, ops, g1, I, q1, -⟩ := intoNeed_rec h3
  obtain ⟨dd, dr, ap, -⟩ := I.sem ((distinct_iff_nodup _).2 hn) (fun y hy => hb y ((mem_flat _ y).2 hy))
  have md : ∀ y, NMem nd y → NMem s.ned y ∨ (g.re ≤ y ∧ y < g2.re) := fun y hy => by
    rcases I.md y hy with e | e
    · exact Or.inl e
    · exact Or.inr ⟨e.1, by omega⟩
  have mr : ∀ y, NMem nr y → NMem s.ned y ∨ (g.re ≤ y ∧ y < g2.re) := fun y hy => by
    rcases I.mr y hy with e | e
    · exact Or.inl e
    · exact Or.inr ⟨e.1, by omega⟩
  exact ⟨by have := I.le; omega, sure_halves_sub md mr dd dr ap⟩

mutual
/-- **`+into` on every lazy need** with no register twice and below the
counter: `HalvesOK`. -/
theorem into_halves (axe : Nat) : ∀ (laz : Lazy CSet) (o : Nat) (g g' : Gen (TreapMap mugF)) (h t : Lazy CSet),
    (lregs laz).Nodup → (∀ x ∈ lregs laz, x < g.re) → Lazy.intoLoopL axe laz o g = some ((h, t), g') →
    HalvesOK laz h t g.re g'.re
  | Lazy.mk s f b, o, g, g', h, t, hn, hb, e => by
    simp only [Lazy.intoLoopL] at e
    obtain ⟨⟨sh, st⟩, g1, e1, e⟩ := bind_some e
    have hn' := hn; have hb' := hb
    simp only [lregs] at hn' hb'
    obtain ⟨n1, b1⟩ := nodup_below_left hn' hb'
    obtain ⟨n23, b23⟩ := nodup_below_right hn' hb'
    obtain ⟨n2, b2⟩ := nodup_below_left n23 b23
    obtain ⟨n3, b3⟩ := nodup_below_right n23 b23
    have S1 := intoSure_sub n1 b1 e1
    split at e
    · rename_i hfb
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hfb
      obtain ⟨rfl, rfl⟩ := hfb
      exact halves_ofSure S1
    · obtain ⟨⟨fh, ft⟩, g2, e2, e⟩ := bind_some e
      have F := into_forks axe f g1 g2 fh ft n2 (fun x hx => Nat.lt_of_lt_of_le (b2 x hx) S1.1) e2
      obtain ⟨⟨bh, bt⟩, g3, e3, e⟩ := bind_some e
      have B := into_bonds axe b g2 g3 bh bt n3 (fun x hx => Nat.lt_of_lt_of_le (b3 x hx) (Nat.le_trans S1.1 F.le)) e3
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
      exact halves_mk S1 F B

theorem into_forks (axe : Nat) : ∀ (f : List (Lazy.ForkE CSet)) (g g' : Gen (TreapMap mugF)) (fh ft : List (Lazy.ForkE CSet)),
    (fregs f).Nodup → (∀ x ∈ fregs f, x < g.re) → Lazy.intoForks axe f g = some ((fh, ft), g') →
    HalvesF f fh ft g.re g'.re
  | [], g, g', fh, ft, _, _, e => by
    simp only [Lazy.intoForks, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨Nat.le_refl _, sub_nil _ _ _, fun _ => ⟨trivial, trivial⟩, rfl, rfl, fun o ho => by simp [flabs] at ho⟩
  | ((oy, y), (on, n)) :: rest, g, g', fh, ft, hn, hb, e => by
    simp only [Lazy.intoForks] at e
    have hn' := hn; have hb' := hb
    simp only [fregs] at hn' hb'
    obtain ⟨n1, b1⟩ := nodup_below_left hn' hb'
    obtain ⟨n23, b23⟩ := nodup_below_right hn' hb'
    obtain ⟨n2, b2⟩ := nodup_below_left n23 b23
    obtain ⟨n3, b3⟩ := nodup_below_right n23 b23
    obtain ⟨⟨yh, yt⟩, g1, e1, e⟩ := bind_some e
    have Y := into_halves axe y oy g g1 yh yt n1 b1 e1
    obtain ⟨⟨nh, nt⟩, g2, e2, e⟩ := bind_some e
    have N := into_halves axe n on g1 g2 nh nt n2 (fun x hx => Nat.lt_of_lt_of_le (b2 x hx) Y.le) e2
    obtain ⟨⟨rh, rt⟩, g3, e3, e⟩ := bind_some e
    have R := into_forks axe rest g2 g3 rh rt n3 (fun x hx => Nat.lt_of_lt_of_le (b3 x hx) (Nat.le_trans Y.le N.le)) e3
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact halvesF_cons Y N R

theorem into_bonds (axe : Nat) : ∀ (b : List (Nat × Lazy CSet)) (g g' : Gen (TreapMap mugF)) (bh bt : List (Nat × Lazy CSet)),
    (bregs b).Nodup → (∀ x ∈ bregs b, x < g.re) → Lazy.intoBonds axe b g = some ((bh, bt), g') →
    HalvesB b bh bt g.re g'.re
  | [], g, g', bh, bt, _, _, e => by
    simp only [Lazy.intoBonds, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨Nat.le_refl _, sub_nil _ _ _, fun _ => ⟨trivial, trivial⟩, rfl, rfl, fun o ho => by simp [blabs] at ho⟩
  | (ob, l) :: rest, g, g', bh, bt, hn, hb, e => by
    simp only [Lazy.intoBonds] at e
    have hn' := hn; have hb' := hb
    simp only [bregs] at hn' hb'
    obtain ⟨n1, b1⟩ := nodup_below_left hn' hb'
    obtain ⟨n2, b2⟩ := nodup_below_right hn' hb'
    obtain ⟨⟨lh, lt⟩, g1, e1, e⟩ := bind_some e
    have L := into_halves axe l ob g g1 lh lt n1 b1 e1
    obtain ⟨⟨rh, rt⟩, g2, e2, e⟩ := bind_some e
    have R := into_bonds axe rest g1 g2 rh rt n2 (fun x hx => Nat.lt_of_lt_of_le (b2 x hx) L.le) e2
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact halvesB_cons L R
end

end Compiler
end Formalization
