import lemmas.Ska.PokeFlagsOf
import lemmas.Compiler.PokeLinkGood2

/-!
# The flags of a closed table are unique (track P, README Gaps 23, P1)

`FlagSol T F` (`Ska/PokeFlagsOf.lean`) says that `F` solves the SCC loop on
the table `T`.  On a table that is closed (`CodeClosed`) and whose `%2`
info bells are among the callees (`InfoCalls`, which `+know` and the bake
give: `knowGo_infos`, `finalFold_calls`), the solution is unique, so
`flagsOf T` is the flags of every solution (`flagsOf_sol`).

* `efGo_congr`: `+eval-finalized`'s trap reads the flag table only at the
  info bells of the nomm;
* `Reach.trans`, `reach_of_inScc`, `sccSet_eq`, `mem_sccOrd`;
* `reachCnt` (how many of a key list a bell reaches), `len_filter_mono`,
  `len_filter_lt`: the measure of the induction (strict callees reach
  fewer, the members of one SCC are ordered by `rap`);
* **`flagSol_uniq`**, **`flagsOf_sol`**.
-/

namespace Formalization
namespace Compiler

open Nock SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF

/-- **The info bells of every entry are among its callees.** -/
def InfoCalls (T : FinMap Bell (VarEntry FinMap)) : Prop :=
  ∀ b e, FinMap.get T b = some e → ∀ c ∈ nommInfos e.nomm, FinMap.get e.calls c = some ()

/-- **`+eval-finalized`'s trap reads the flags of the info bells only.** -/
theorem efGo_congr (ft ft' : FlagTab) :
    ∀ (n : Nomm) (s : Sock), (∀ c ∈ nommInfos n, ft c = ft' c) → efGo ft s n = efGo ft' s n := by
  intro n
  induction n with
  | cons p q ihp ihq =>
    intro s h
    have hp := fun s => ihp s (fun c hc => h c (by simp [nommInfos, hc]))
    have hq := fun s => ihq s (fun c hc => h c (by simp [nommInfos, hc]))
    simp only [efGo, hp, hq]
  | n0 p => intro s _; rfl
  | n1 p => intro s _; rfl
  | n2 p q info ihp ihq =>
    intro s h
    have hp := fun s => ihp s (fun c hc => h c (by simp [nommInfos, hc]))
    have hq := fun s => ihq s (fun c hc => h c (by simp [nommInfos, hc]))
    have hi : ∀ i, info = some i → ft i.1 = ft' i.1 := by
      intro i hi; subst hi; exact h _ (by simp [nommInfos])
    simp only [efGo, hp, hq]
    cases info with
    | none => rfl
    | some i => simp only [hi i rfl]
  | n3 p ihp =>
    intro s h
    have hp := fun s => ihp s (fun c hc => h c (by simp [nommInfos, hc]))
    simp only [efGo, hp]
  | n4 p _ => intro s _; rfl
  | n5 p q ihp ihq =>
    intro s h
    have hp := fun s => ihp s (fun c hc => h c (by simp [nommInfos, hc]))
    have hq := fun s => ihq s (fun c hc => h c (by simp [nommInfos, hc]))
    simp only [efGo, hp, hq]
  | n6 p q r _ ihq ihr =>
    intro s h
    have hq := fun s => ihq s (fun c hc => h c (by simp [nommInfos, hc]))
    have hr := fun s => ihr s (fun c hc => h c (by simp [nommInfos, hc]))
    simp only [efGo, hq, hr]
  | n7 p q ihp ihq =>
    intro s h
    have hp := fun s => ihp s (fun c hc => h c (by simp [nommInfos, hc]))
    have hq := fun s => ihq s (fun c hc => h c (by simp [nommInfos, hc]))
    simp only [efGo, hp, hq]
  | n10 a v q ihv ihq =>
    intro s h
    have hv := fun s => ihv s (fun c hc => h c (by simp [nommInfos, hc]))
    have hq := fun s => ihq s (fun c hc => h c (by simp [nommInfos, hc]))
    simp only [efGo, hv, hq]
  | n11s tag q body ihq =>
    intro s h
    have hq := fun s => ihq s (fun c hc => h c (by simp [nommInfos, hc]))
    simp only [efGo, hq]
  | n11d tag hh q body ihh ihq =>
    intro s h
    have hh' := fun s => ihh s (fun c hc => h c (by simp [nommInfos, hc]))
    have hq := fun s => ihq s (fun c hc => h c (by simp [nommInfos, hc]))
    simp only [efGo, hh', hq]
  | n12 p q _ _ => intro s _; rfl
  | mean p b q body k ihp ihq =>
    intro s h
    have hp := fun s => ihp s (fun c hc => h c (by simp [nommInfos, hc]))
    have hq := fun s => ihq s (fun c hc => h c (by simp [nommInfos, hc]))
    simp only [efGo, hp, hq]

theorem Reach.trans {T : FinMap Bell (VarEntry FinMap)} {a b c : Bell} (h1 : Reach T a b) (h2 : Reach T b c) :
    Reach T a c := by
  induction h1 with
  | refl _ => exact h2
  | step e _ ih => exact Reach.step e (ih h2)

open Classical in
/-- Two members of one SCC have the same SCC. -/
theorem sccSet_eq {T : FinMap Bell (VarEntry FinMap)} {b c : Bell} (h1 : Reach T b c) (h2 : Reach T c b) :
    sccSet T b = sccSet T c := by
  have hiff : ∀ x, InScc T b x ↔ InScc T c x := fun x =>
    ⟨fun ⟨k, r1, r2⟩ => ⟨k, h2.trans r1, r2.trans h1⟩, fun ⟨k, r1, r2⟩ => ⟨k, h1.trans r1, r2.trans h2⟩⟩
  apply Subtype.ext
  funext x
  show (if InScc T b x then some () else none) = (if InScc T c x then some () else none)
  by_cases hx : InScc T b x
  · rw [if_pos hx, if_pos ((hiff x).1 hx)]
  · rw [if_neg hx, if_neg (fun h => hx ((hiff x).2 h))]

open Classical in
theorem mem_sccOrd {T : FinMap Bell (VarEntry FinMap)} {b c : Bell} : c ∈ sccOrd T b ↔ InScc T b c := by
  unfold sccOrd
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨c', v⟩, hm, rfl⟩
    have := (FinMap.mem_rap _ _ _).1 hm
    simp only [sccSet] at this
    by_cases hn : InScc T b c'
    · exact hn
    · rw [if_neg hn] at this; cases this
  · intro h
    refine ⟨(c, ()), (FinMap.mem_rap _ _ _).2 ?_, rfl⟩
    simp only [sccSet]
    rw [if_pos h]

theorem len_filter_mono {α : Type} (p q : α → Bool) (h : ∀ x, p x = true → q x = true) :
    ∀ l : List α, (l.filter p).length ≤ (l.filter q).length
  | [] => Nat.le_refl _
  | a :: l => by
    have ih := len_filter_mono p q h l
    by_cases hp : p a = true
    · simp [List.filter_cons, hp, h a hp]; omega
    · by_cases hq : q a = true <;> simp [List.filter_cons, hp, hq] <;> omega

theorem len_filter_lt {α : Type} (p q : α → Bool) (h : ∀ x, p x = true → q x = true) :
    ∀ l : List α, (∃ x ∈ l, q x = true ∧ p x = false) → (l.filter p).length < (l.filter q).length
  | [], ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | a :: l, ⟨x, hx, hqx, hpx⟩ => by
    rcases List.mem_cons.1 hx with rfl | hx'
    · have := len_filter_mono p q h l
      simp [List.filter_cons, hqx, hpx]; omega
    · have ih := len_filter_lt p q h l ⟨x, hx', hqx, hpx⟩
      by_cases hp : p a = true
      · simp [List.filter_cons, hp, h a hp]; omega
      · by_cases hq : q a = true <;> simp [List.filter_cons, hp, hq] <;> omega

open Classical in
/-- How many bells of `l` the bell `b` reaches. -/
noncomputable def reachCnt (T : FinMap Bell (VarEntry FinMap)) (l : List Bell) (b : Bell) : Nat :=
  (l.filter fun x => decide (Reach T b x)).length

theorem reachCnt_le {T : FinMap Bell (VarEntry FinMap)} (l : List Bell) {b c : Bell} (h : Reach T b c) :
    reachCnt T l c ≤ reachCnt T l b :=
  len_filter_mono _ _ (fun x hx => by simp only [decide_eq_true_eq] at hx ⊢; exact h.trans hx) l

theorem reachCnt_lt {T : FinMap Bell (VarEntry FinMap)} (l : List Bell) {b c : Bell} (h : Reach T b c)
    (hn : ¬ Reach T c b) (hb : b ∈ l) : reachCnt T l c < reachCnt T l b :=
  len_filter_lt _ _ (fun x hx => by simp only [decide_eq_true_eq] at hx ⊢; exact h.trans hx) l
    ⟨b, hb, by simp [Reach.refl], by simp [hn]⟩

open Classical in
/-- **The solution of the SCC loop on a closed table is unique.** -/
theorem flagSol_uniq {T : FinMap Bell (VarEntry FinMap)} (hC : CodeClosed T) (hI : InfoCalls T)
    {F G : FlagTab} (hF : FlagSol T F) (hG : FlagSol T G) : F = G := by
  obtain ⟨l, hl⟩ := T.2
  have hkey : ∀ b e, FinMap.get T b = some e → b ∈ l := fun b e h =>
    hl b (by intro h0; have : FinMap.get T b = none := h0; rw [this] at h; cases h)
  -- the step: equal below `b` gives equal at `b`
  have step : ∀ b, (∀ c, Reach T b c → ¬ Reach T c b → F c = G c) →
      (∀ c, InScc T b c → (sccOrd T b).idxOf c < (sccOrd T b).idxOf b → F c = G c) → F b = G b := by
    intro b hlt hin
    cases hb : FinMap.get T b with
    | none => rw [hF.1 b hb, hG.1 b hb]
    | some e =>
      rw [hF.2 b e hb, hG.2 b e hb]
      unfold evalFin
      have hn : nmOf T b = some e.nomm := by simp [nmOf, hb]
      rw [hn]
      simp only [Option.bind_some]
      rw [efGo_congr _ _ e.nomm b.less]
      intro c hc
      obtain ⟨e', he'⟩ := (hC b e hb).2 c hc
      have hE : Edge T b c := ⟨e, hb, hI b e hb c hc, e', he'⟩
      have hR : Reach T b c := Reach.step hE (Reach.refl c)
      unfold ftAt
      simp only
      by_cases hm : c ∈ sccOrd T b
      · rw [if_pos hm, if_pos hm]
        by_cases hi : (sccOrd T b).idxOf c < (sccOrd T b).idxOf b
        · rw [if_pos hi, if_pos hi]; exact hin c (mem_sccOrd.1 hm) hi
        · rw [if_neg hi, if_neg hi]
      · rw [if_neg hm, if_neg hm]
        exact hlt c hR (fun h => hm (mem_sccOrd.2 ⟨⟨e', he'⟩, hR, h⟩))
  have outer : ∀ n b, reachCnt T l b < n → F b = G b := by
    intro n
    induction n with
    | zero => intro b h; omega
    | succ n ih =>
      have inner : ∀ k b, reachCnt T l b ≤ n → (sccOrd T b).idxOf b < k → F b = G b := by
        intro k
        induction k with
        | zero => intro b _ h; omega
        | succ k ihk =>
          intro b hb hk
          apply step b
          · intro c hR hn
            cases hbk : FinMap.get T b with
            | none =>
              cases hR with
              | refl => exact absurd (Reach.refl b) hn
              | step hE _ => obtain ⟨e, he, -⟩ := hE; rw [hbk] at he; cases he
            | some e =>
              exact ih c (Nat.lt_of_lt_of_le (reachCnt_lt l hR hn (hkey b e hbk)) hb)
          · intro c hc hi
            obtain ⟨_, r1, r2⟩ := hc
            have hs : sccOrd T c = sccOrd T b := by unfold sccOrd; rw [sccSet_eq r1 r2]
            exact ihk c (Nat.le_trans (reachCnt_le l r1) hb) (by rw [hs]; omega)
      intro b hb
      exact inner _ b (by omega) (Nat.lt_succ_self _)
  funext b
  exact outer _ b (Nat.lt_succ_self _)

/-- **`flagsOf` is the flags of any solution** on a closed table. -/
theorem flagsOf_sol {T : FinMap Bell (VarEntry FinMap)} (hC : CodeClosed T) (hI : InfoCalls T)
    {F : FlagTab} (hF : FlagSol T F) (b : Bell) :
    flagsOf T b = match F b with
      | some p => flagNoun p
      | none => A 0 :=
  flagsOf_eq hF (fun _ hG => flagSol_uniq hC hI hG hF) b

/-! ## The SCC loop gives the new table's solution -/

/-- **`T'` is `T` with the new entries `nc`** (as `addCode code (newCode code baked)`):
old entries kept, new keys not old, nothing else. -/
structure AddsTo (T nc T' : FinMap Bell (VarEntry FinMap)) : Prop where
  old : ∀ b e, FinMap.get T b = some e → FinMap.get T' b = some e
  new : ∀ b e, FinMap.get nc b = some e → FinMap.get T b = none ∧ FinMap.get T' b = some e
  cov : ∀ b e, FinMap.get T' b = some e → FinMap.get T b = some e ∨ FinMap.get nc b = some e

/-- `TarjanSpec` with callees first as `Pairwise`. -/
def TarjanSpecP (nc : FinMap Bell (VarEntry FinMap)) (L : List (List Bell)) : Prop :=
  (∀ S ∈ L, ∃ b, (∃ e, FinMap.get nc b = some e) ∧ S = sccOrd nc b) ∧
    L.flatten.Nodup ∧ (∀ b, b ∈ L.flatten ↔ ∃ e, FinMap.get nc b = some e) ∧
    L.Pairwise (fun S S' => ∀ b ∈ S, ∀ c ∈ S', ¬ Edge nc b c)

theorem tarjanSpecP_of {nc : FinMap Bell (VarEntry FinMap)} {L : List (List Bell)} (h : TarjanSpec nc L) :
    TarjanSpecP nc L :=
  ⟨h.1, h.2.1, h.2.2.1, List.pairwise_iff_getElem.2 fun i j hi hj hij => h.2.2.2 i j hij hi hj⟩

section Adds

variable {T nc T' : FinMap Bell (VarEntry FinMap)}

theorem reach_old (hA : AddsTo T nc T') (hC : CodeClosed T) {a x : Bell} (h : Reach T' a x) :
    FinMap.get T a ≠ none → FinMap.get T x ≠ none ∧ Reach T a x := by
  induction h with
  | refl b => exact fun ha => ⟨ha, Reach.refl b⟩
  | @step a y _ hE _ ih =>
    intro ha
    obtain ⟨e, he, hc, -, -⟩ := hE
    cases h0 : FinMap.get T a with
    | none => exact absurd h0 ha
    | some e0 =>
      have hee : e = e0 := by rw [hA.old _ _ h0] at he; exact (Option.some.inj he).symm
      subst hee
      obtain ⟨e1, he1⟩ := (hC _ _ h0).1 _ hc
      obtain ⟨h2, h3⟩ := ih (by rw [he1]; simp)
      exact ⟨h2, Reach.step ⟨e, h0, hc, e1, he1⟩ h3⟩

theorem reach_mono_old (hA : AddsTo T nc T') {a x : Bell} (h : Reach T a x) : Reach T' a x := by
  induction h with
  | refl b => exact Reach.refl b
  | step hE _ ih =>
    obtain ⟨e, he, hc, e', he'⟩ := hE
    exact Reach.step ⟨e, hA.old _ _ he, hc, e', hA.old _ _ he'⟩ ih

theorem reach_mono_new (hA : AddsTo T nc T') {a x : Bell} (h : Reach nc a x) : Reach T' a x := by
  induction h with
  | refl b => exact Reach.refl b
  | step hE _ ih =>
    obtain ⟨e, he, hc, e', he'⟩ := hE
    exact Reach.step ⟨e, (hA.new _ _ he).2, hc, e', (hA.new _ _ he').2⟩ ih

theorem new_of_reach (hA : AddsTo T nc T') (hC : CodeClosed T) {a b : Bell} (h : Reach T' a b)
    (hb : FinMap.get T b = none) : FinMap.get T a = none := by
  cases h0 : FinMap.get T a with
  | none => rfl
  | some _ => exact absurd hb (reach_old hA hC h (by rw [h0]; simp)).1

theorem reach_new (hA : AddsTo T nc T') (hC : CodeClosed T) {a x : Bell} (h : Reach T' a x) :
    ∀ {b : Bell}, Reach T' x b → FinMap.get T b = none → Reach nc a x := by
  induction h with
  | refl _ => exact fun _ _ => Reach.refl _
  | step hE hR ih =>
    intro b hxb hb
    have hab := Reach.step hE (hR.trans hxb)
    have hyb := hR.trans hxb
    obtain ⟨e, he, hc, e', he'⟩ := hE
    have ha := new_of_reach hA hC hab hb
    have hy := new_of_reach hA hC hyb hb
    have hea := (hA.cov _ _ he).resolve_left (by rw [ha]; simp)
    have hey := (hA.cov _ _ he').resolve_left (by rw [hy]; simp)
    exact Reach.step ⟨e, hea, hc, e', hey⟩ (ih hxb hb)

theorem inScc_new (hA : AddsTo T nc T') (hC : CodeClosed T) {b : Bell} (hb : FinMap.get T b = none) (x : Bell) :
    InScc T' b x ↔ InScc nc b x := by
  constructor
  · rintro ⟨⟨e, hx⟩, r1, r2⟩
    have hxn := new_of_reach hA hC r2 hb
    exact ⟨⟨e, (hA.cov _ _ hx).resolve_left (by rw [hxn]; simp)⟩, reach_new hA hC r1 r2 hb,
      reach_new hA hC r2 (Reach.refl b) hb⟩
  · rintro ⟨⟨e, hx⟩, r1, r2⟩
    exact ⟨⟨e, (hA.new _ _ hx).2⟩, reach_mono_new hA r1, reach_mono_new hA r2⟩

theorem inScc_old (hA : AddsTo T nc T') (hC : CodeClosed T) {b : Bell} (hb : FinMap.get T b ≠ none) (x : Bell) :
    InScc T' b x ↔ InScc T b x := by
  constructor
  · rintro ⟨_, r1, r2⟩
    obtain ⟨h1, r1'⟩ := reach_old hA hC r1 hb
    cases hx : FinMap.get T x with
    | none => exact absurd hx h1
    | some e => exact ⟨⟨e, hx⟩, r1', (reach_old hA hC r2 h1).2⟩
  · rintro ⟨⟨e, hx⟩, r1, r2⟩
    exact ⟨⟨e, hA.old _ _ hx⟩, reach_mono_old hA r1, reach_mono_old hA r2⟩

end Adds

open Classical in
theorem sccSet_congr {T1 T2 : FinMap Bell (VarEntry FinMap)} {b c : Bell}
    (h : ∀ x, InScc T1 b x ↔ InScc T2 c x) : sccSet T1 b = sccSet T2 c := by
  apply Subtype.ext
  funext x
  show (if InScc T1 b x then some () else none) = (if InScc T2 c x then some () else none)
  by_cases hx : InScc T1 b x
  · rw [if_pos hx, if_pos ((h x).1 hx)]
  · rw [if_neg hx, if_neg (fun h' => hx ((h x).2 h'))]

/-! ### One SCC: the fold of `sccStep` -/

/-- The gate of `sccStep`'s fold. -/
def efStep (nm : Bell → Option Nomm) (acc : Option FlagTab) (b : Bell) : Option FlagTab :=
  acc.bind fun f => (evalFin nm f b).map fun pt => fun c => if c = b then some pt else f c

theorem sccStep_eq (nm : Bell → Option Nomm) (ft : FlagTab) (S : List Bell) :
    sccStep nm ft S = S.foldl (efStep nm) (some fun c => if c ∈ S then some (false, false) else ft c) := rfl

theorem efFold_none (nm : Bell → Option Nomm) : ∀ l : List Bell, l.foldl (efStep nm) none = none
  | [] => rfl
  | _ :: l => efFold_none nm l

/-- The table a member `b` of `S` is evaluated on: the members before it
with `f`, it and the later ones `[| |]`, the rest `ft`. -/
def frm (S : List Bell) (ft f : FlagTab) (b : Bell) : FlagTab := fun c =>
  if c ∈ S then (if S.idxOf c < S.idxOf b then f c else some (false, false)) else ft c

theorem idxOf_lt_iff {pre post : List Bell} {c : Bell} : (pre ++ post).idxOf c < pre.length ↔ c ∈ pre := by
  rw [List.idxOf_append]
  by_cases h : c ∈ pre
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => List.idxOf_lt_length_iff.2 h⟩
  · rw [if_neg h]; exact ⟨fun h' => by omega, fun h' => absurd h' h⟩

theorem efFold_spec (nm : Bell → Option Nomm) (ft : FlagTab) (S : List Bell) (hS : S.Nodup) :
    ∀ (rest pre : List Bell) (f H : FlagTab), S = pre ++ rest →
      (∀ c, c ∉ S → f c = ft c) → (∀ c ∈ rest, f c = some (false, false)) →
      (∀ b ∈ pre, f b = evalFin nm (frm S ft f b) b) →
      rest.foldl (efStep nm) (some f) = some H →
      (∀ c, c ∉ S → H c = ft c) ∧ ∀ b ∈ S, H b = evalFin nm (frm S ft H b) b := by
  intro rest
  induction rest with
  | nil =>
    intro pre f H hSe ha _ hc hr
    simp only [List.foldl_nil, Option.some.injEq] at hr
    subst hr
    rw [List.append_nil] at hSe
    subst hSe
    exact ⟨ha, hc⟩
  | cons r rest' ih =>
    intro pre f H hSe ha hb hc hr
    rw [List.foldl_cons] at hr
    have hnd := hS
    rw [hSe, List.nodup_append, List.nodup_cons] at hnd
    have hrpre : r ∉ pre := fun h => hnd.2.2 r h r List.mem_cons_self rfl
    have hrrest : r ∉ rest' := hnd.2.1.1
    have hrS : r ∈ S := by rw [hSe]; simp
    have hidr : S.idxOf r = pre.length := by
      rw [hSe, List.idxOf_append, if_neg hrpre, List.idxOf_cons_self]; omega
    have hlt : ∀ c, S.idxOf c < pre.length ↔ c ∈ pre := fun c => by rw [hSe]; exact idxOf_lt_iff
    cases hev : evalFin nm f r with
    | none =>
      simp only [efStep, Option.bind_some, hev, Option.map_none] at hr
      rw [efFold_none] at hr; cases hr
    | some pt =>
      simp only [efStep, Option.bind_some, hev, Option.map_some] at hr
      refine ih (pre ++ [r]) _ H (by rw [hSe]; simp) ?_ ?_ ?_ hr
      · intro c hc'
        have : c ≠ r := fun h => hc' (h ▸ hrS)
        simp only [this, if_false]; exact ha c hc'
      · intro c hc'
        have : c ≠ r := fun h => hrrest (h ▸ hc')
        simp only [this, if_false]; exact hb c (List.mem_cons_of_mem _ hc')
      · intro b hb'
        rcases List.mem_append.1 hb' with hbp | hbr
        · have hbr : b ≠ r := fun h => hrpre (h ▸ hbp)
          simp only [hbr, if_false]
          rw [hc b hbp]
          congr 1
          funext c
          unfold frm
          by_cases hcS : c ∈ S
          · rw [if_pos hcS, if_pos hcS]
            by_cases hi : S.idxOf c < S.idxOf b
            · rw [if_pos hi, if_pos hi]
              have hbl := (hlt b).2 hbp
              have : c ≠ r := fun h => by subst h; omega
              simp only [this, if_false]
            · rw [if_neg hi, if_neg hi]
          · rw [if_neg hcS, if_neg hcS]
        · have hbr' : b = r := by simpa using hbr
          subst hbr'
          simp only [if_true]
          rw [← hev]
          congr 1
          funext c
          unfold frm
          by_cases hcS : c ∈ S
          · rw [if_pos hcS]
            by_cases hi : S.idxOf c < S.idxOf b
            · rw [if_pos hi]
              have hcp := (hlt c).1 (by omega)
              have : c ≠ b := fun h => hrpre (h ▸ hcp)
              simp only [this, if_false]
            · rw [if_neg hi]
              have hcp : c ∉ pre := fun h => hi (by have := (hlt c).2 h; omega)
              have hcr : c ∈ b :: rest' := by
                have := hcS; rw [hSe] at this
                rcases List.mem_append.1 this with h | h
                · exact absurd h hcp
                · exact h
              exact hb c hcr
          · rw [if_neg hcS]; exact ha c hcS

theorem sccStep_spec (nm : Bell → Option Nomm) (ft : FlagTab) (S : List Bell) (hS : S.Nodup) {H : FlagTab}
    (h : sccStep nm ft S = some H) :
    (∀ c, c ∉ S → H c = ft c) ∧ ∀ b ∈ S, H b = evalFin nm (frm S ft H b) b := by
  rw [sccStep_eq] at h
  refine efFold_spec nm ft S hS S [] _ H rfl (fun c hc => by simp [hc]) (fun c hc => by simp [hc])
    (fun b hb => absurd hb List.not_mem_nil) h

/-! ### The loop over the SCCs of the new code -/

section Loop

variable {T nc T' : FinMap Bell (VarEntry FinMap)}

/-- The SCC of a member of a listed SCC, in `T'`, is that SCC. -/
theorem sccOrd_listed (hA : AddsTo T nc T') (hC : CodeClosed T) {L : List (List Bell)} (hL : TarjanSpecP nc L)
    {S : List Bell} (hS : S ∈ L) {b : Bell} (hb : b ∈ S) : sccOrd T' b = S := by
  obtain ⟨b0, _, rfl⟩ := hL.1 S hS
  obtain ⟨⟨e, hbe⟩, r1, r2⟩ := mem_sccOrd.1 hb
  have hbn := (hA.new _ _ hbe).1
  unfold sccOrd
  rw [sccSet_congr (inScc_new hA hC hbn), sccSet_eq r2 r1]

theorem listed_new (hA : AddsTo T nc T') {L : List (List Bell)} (hL : TarjanSpecP nc L) {b : Bell}
    (hb : b ∈ L.flatten) : FinMap.get T b = none ∧ ∃ e, FinMap.get nc b = some e := by
  obtain ⟨e, he⟩ := (hL.2.2.1 b).1 hb
  exact ⟨(hA.new _ _ he).1, e, he⟩

/-- **The invariant of the loop**: after the SCCs `D`, old bells have their
old flags, unlisted new bells none, and every old or done bell solves its
equation on `T'`. -/
theorem sccLoop_inv (hA : AddsTo T nc T') (hC : CodeClosed T) (hC' : CodeClosed T') (hI' : InfoCalls T')
    {L : List (List Bell)} (hL : TarjanSpecP nc L) (F : FlagTab) :
    ∀ (rest D : List (List Bell)) (ft G : FlagTab), L = D ++ rest →
      (∀ c, FinMap.get T c ≠ none → ft c = F c) →
      (∀ c, FinMap.get T c = none → c ∉ D.flatten → ft c = none) →
      (∀ b e, FinMap.get T' b = some e → (FinMap.get T b ≠ none ∨ b ∈ D.flatten) →
        ft b = evalFin (nmOf T') (ftAt T' ft b) b) →
      sccLoop (nmOf T') ft rest = some G → (∀ c, FinMap.get T c ≠ none → G c = F c) ∧ FlagSol T' G := by
  intro rest
  induction rest with
  | nil =>
    intro D ft G hLe h1 h2 h3 hr
    simp only [sccLoop, Option.some.injEq] at hr
    subst hr
    rw [List.append_nil] at hLe
    subst hLe
    refine ⟨h1, fun b hb => ?_, fun b e hb => ?_⟩
    · have hbo : FinMap.get T b = none := by
        cases h0 : FinMap.get T b with
        | none => rfl
        | some e => rw [hA.old _ _ h0] at hb; cases hb
      refine h2 b hbo (fun hm => ?_)
      obtain ⟨-, e, he⟩ := listed_new hA hL hm
      rw [(hA.new _ _ he).2] at hb; cases hb
    · refine h3 b e hb ?_
      rcases hA.cov _ _ hb with h | h
      · exact Or.inl (by rw [h]; simp)
      · exact Or.inr ((hL.2.2.1 b).2 ⟨e, h⟩)
  | cons S rest' ih =>
    intro D ft G hLe h1 h2 h3 hr
    simp only [sccLoop] at hr
    cases hst : sccStep (nmOf T') ft S with
    | none => rw [hst] at hr; cases hr
    | some H =>
    rw [hst, Option.bind_some] at hr
    have hSL : S ∈ L := by rw [hLe]; simp
    have hND := List.pairwise_flatten.1 hL.2.1
    have hSnd : S.Nodup := hND.1 S hSL
    have hdis : ∀ x ∈ D.flatten, x ∉ S := by
      intro x hx hxS
      have := (List.pairwise_append.1 (hLe ▸ hND.2)).2.2
      obtain ⟨l1, hl1, hx1⟩ := List.mem_flatten.1 hx
      exact this l1 hl1 S List.mem_cons_self x hx1 x hxS rfl
    have hcf : ∀ x ∈ D.flatten, ∀ y ∈ S, ¬ Edge nc x y := by
      intro x hx y hy
      have := (List.pairwise_append.1 (hLe ▸ hL.2.2.2)).2.2
      obtain ⟨l1, hl1, hx1⟩ := List.mem_flatten.1 hx
      exact this l1 hl1 S List.mem_cons_self x hx1 y hy
    have hSnew : ∀ x ∈ S, FinMap.get T x = none ∧ ∃ e, FinMap.get nc x = some e := fun x hx =>
      listed_new hA hL (List.mem_flatten.2 ⟨S, hSL, hx⟩)
    obtain ⟨hs1, hs2⟩ := sccStep_spec (nmOf T') ft S hSnd hst
    refine ih (D ++ [S]) H G (by rw [hLe]; simp) ?_ ?_ ?_ hr
    · intro c hc
      have hcS : c ∉ S := fun h => hc (hSnew c h).1
      rw [hs1 c hcS]; exact h1 c hc
    · intro c hc hcD
      simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.mem_append, not_or] at hcD
      rw [hs1 c hcD.2]; exact h2 c hc hcD.1
    · intro b e hb hbo
      by_cases hbS : b ∈ S
      · rw [hs2 b hbS]
        have hord := sccOrd_listed hA hC hL hSL hbS
        congr 1
        funext c
        unfold frm ftAt
        simp only [hord]
        by_cases hcS : c ∈ S
        · rw [if_pos hcS, if_pos hcS]
        · rw [if_neg hcS, if_neg hcS]; exact (hs1 c hcS).symm
      · have hbo' : FinMap.get T b ≠ none ∨ b ∈ D.flatten := by
          rcases hbo with h | h
          · exact Or.inl h
          · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
              List.mem_append] at h
            rcases h with h | h
            · exact Or.inr h
            · exact absurd h hbS
        rw [hs1 b hbS, h3 b e hb hbo']
        unfold evalFin
        have hn : nmOf T' b = some e.nomm := by simp [nmOf, hb]
        rw [hn]
        simp only [Option.bind_some]
        rw [efGo_congr _ _ e.nomm b.less]
        intro c hc
        have hcS : c ∉ S := by
          intro hcS
          obtain ⟨hcn, ec, hec⟩ := hSnew c hcS
          rcases hbo' with h | h
          · cases h0 : FinMap.get T b with
            | none => exact h h0
            | some e0 =>
              have hee : e = e0 := by rw [hA.old _ _ h0] at hb; exact (Option.some.inj hb).symm
              subst hee
              obtain ⟨e1, he1⟩ := (hC b e h0).1 c (hI' b e hb c hc)
              rw [he1] at hcn; cases hcn
          · obtain ⟨hbn, eb, heb⟩ := listed_new hA hL (by
              obtain ⟨l1, hl1, hx1⟩ := List.mem_flatten.1 h
              exact List.mem_flatten.2 ⟨l1, by rw [hLe]; simp [hl1], hx1⟩)
            have hee : eb = e := by rw [(hA.new _ _ heb).2] at hb; exact Option.some.inj hb
            subst hee
            exact hcf b h c hcS ⟨eb, heb, hI' b eb hb c hc, ec, hec⟩
        unfold ftAt
        simp only
        rw [hs1 c hcS]

/-- **The SCC loop over `+tarjan`'s list, from the old table's solution,
gives the new table's**, and keeps the old bells' flags. -/
theorem sccLoop_sol (hA : AddsTo T nc T') (hC : CodeClosed T) (hC' : CodeClosed T') (hI' : InfoCalls T')
    {L : List (List Bell)} (hL : TarjanSpec nc L) {F G : FlagTab} (hF : FlagSol T F)
    (hr : sccLoop (nmOf T') F L = some G) : (∀ c, FinMap.get T c ≠ none → G c = F c) ∧ FlagSol T' G := by
  refine sccLoop_inv hA hC hC' hI' (tarjanSpecP_of hL) F L [] F G rfl (fun _ _ => rfl)
    (fun c hc _ => hF.1 c hc) ?_ hr
  intro b e hb hbo
  have hbo' : FinMap.get T b ≠ none := by
    rcases hbo with h | h
    · exact h
    · simp at h
  cases h0 : FinMap.get T b with
  | none => exact absurd h0 hbo'
  | some e0 =>
    rw [hF.2 b e0 h0]
    have hn : nmOf T' b = nmOf T b := by simp [nmOf, h0, hA.old _ _ h0]
    have hord : sccOrd T' b = sccOrd T b := by
      unfold sccOrd; rw [sccSet_congr (inScc_old hA hC hbo')]
    unfold evalFin
    rw [hn]
    unfold ftAt
    simp only [hord]

/-- **`flagsOf` after the loop**: on the new table it is the loop's flags,
and on an old bell they are the old ones. -/
theorem flagsOf_loop (hA : AddsTo T nc T') (hC : CodeClosed T) (hI : InfoCalls T) (hC' : CodeClosed T')
    (hI' : InfoCalls T') {L : List (List Bell)} (hL : TarjanSpec nc L) {F G : FlagTab} (hF : FlagSol T F)
    (hr : sccLoop (nmOf T') F L = some G) (b : Bell) :
    flagsOf T' b = (match G b with
      | some p => flagNoun p
      | none => A 0) ∧
    (FinMap.get T b ≠ none → flagsOf T' b = flagsOf T b) := by
  obtain ⟨hold, hsol⟩ := sccLoop_sol hA hC hC' hI' hL hF hr
  refine ⟨flagsOf_sol hC' hI' hsol b, fun hb => ?_⟩
  rw [flagsOf_sol hC' hI' hsol b, flagsOf_sol hC hI hF b, hold b hb]

end Loop

end Compiler
end Formalization
