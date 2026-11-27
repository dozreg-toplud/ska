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

end Compiler
end Formalization
