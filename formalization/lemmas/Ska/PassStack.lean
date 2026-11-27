import lemmas.Ska.PassIdents
import lemmas.Ska.HeBound

/-!
# No infinite sequence of pushes that stay on the stack (track F, Gaps 16)

The author's termination argument (the comment of `+recursive-call`): "an
infinite chain has infinitely many functions with one formula (the callable
formulas are finitely many), so past the threshold HE applies to it".  Here
it is proved for every sequence of pushed identities whose earlier members
are all on the stack when a later one is pushed, with no push tree and no
finite branching:

* `recLoop_none`, `recursiveCall_none`: when `+recursive-call` answers `~`
  with the embedding test on (`he-threshold` frames of the kid's formula on
  the stack), no frame of that formula is embedded (`he kid.1 j.1 = false`);
* `resolveStep_new`: `resolve` analyses `idT` afresh exactly after a miss in
  the graph, a miss of `+git:mi` and that answer `~`, so `push_guard`: the
  pushed identity is not `he`-above any frame of its formula on the stack once
  the threshold is reached;
* **`noStackSeq_of_kruskal`**: from `KruskalBT`, finitely many formulas, and
  a tree view `sub` of identities for which an embedding of trees gives `he`
  of the later subject over the earlier one, there is no infinite sequence of
  distinct identities, each pushed with the guard of `push_guard` against a
  stack that holds every earlier one.

Two instances: an infinite descent of nested `+analyze` calls that never
return (every root stays on the stack), and the members of one component's
pass loop (with fix (b), dab8478, `+cull` runs only before the first pass and
at the stable end, and a nested `+pop` removes only its own members, so a
member stays on the stack until the loop ends).  What it does not cover is
the width of the analysis: the identities that a loop pushes and that finish
(popped into `done`) before later ones are pushed are never on the stack
together, so the embedding test never compares them (README Gaps 16).
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- **`+recursive-call`'s loop answering `~`**: no frame of the kid's formula
is embedded by the kid's subject when the embedding test is on. -/
theorem recLoop_none {he : Sock → Sock → Bool} {heOn : Bool} {g : Sock × Noun → Option Datum}
    {kid : Sock × Noun} : ∀ {stk : List (Sock × Noun)}, recLoop he heOn g kid stk = some none →
    ∀ j ∈ stk, j.2 = kid.2 → heOn = true → he kid.1 j.1 = false
  | [], _, j, hj, _, _ => absurd hj List.not_mem_nil
  | i :: stk, h, j, hj, hf, ho => by
    unfold recLoop at h
    split at h
    · rename_i hne
      rcases List.mem_cons.mp hj with rfl | hj
      · exact absurd hf.symm hne
      · exact recLoop_none h j hj hf ho
    · split at h
      · cases h
      · cases h
      · split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨_, _, h⟩ := h
          cases h
        · rename_i hc
          rcases List.mem_cons.mp hj with rfl | hj
          · cases e : he kid.1 j.1
            · rfl
            · exact absurd ⟨ho, e⟩ hc
          · exact recLoop_none h j hj hf ho

/-- **`+recursive-call` answering `~` past the threshold**: with at least
`he-threshold` frames of the kid's formula on the stack, the kid's subject
embeds none of their subjects. -/
theorem recursiveCall_none {he : Sock → Sock → Bool} {th : Nat} {kid : Sock × Noun}
    {stk : List (Sock × Noun)} {g : Sock × Noun → Option Datum}
    (h : recursiveCall he th kid stk g = some none)
    (hth : th ≤ (stk.filter (fun i => i.2 = kid.2)).length) :
    ∀ j ∈ stk, j.2 = kid.2 → he kid.1 j.1 = false :=
  fun j hj hf => recLoop_none h j hj hf (decide_eq_true hth)

/-- **When `resolve` analyses afresh**: a miss in the graph, a miss of
`+git:mi` in `done`, and `+recursive-call` answering `~`. -/
theorem resolveStep_new {env : Env R} {res : ResGo M R} {an : AnaGo M R} {orig idT : Ident}
    {gen : GenS M R} (hg : Treap.get gen.st.g idT = none) (hm : gitMi gen.st.done orig.2 idT.1 = some none)
    (hr : recursiveCall env.he env.threshold idT gen.st.stk (gCore gen.st.g) = some none) :
    resolveStep env res an orig idT gen =
      (an idT gen.st).map fun r => ((idT, gitG r.2.g idT), { gen with st := r.2, low := min gen.low r.1 }) := by
  simp only [resolveStep, hg, hm, hr]

/-- **The guard of a push**: an identity that `resolve` analyses afresh, with
`he-threshold` frames of its formula on the stack, embeds none of them. -/
theorem push_guard {env : Env R} {idT : Ident} {gen : GenS M R}
    (hr : recursiveCall env.he env.threshold idT gen.st.stk (gCore gen.st.g) = some none)
    (hth : env.threshold ≤ (gen.st.stk.filter (fun i => i.2 = idT.2)).length) :
    ∀ j ∈ gen.st.stk, j.2 = idT.2 → env.he idT.1 j.1 = false :=
  recursiveCall_none hr hth

/-- `n` distinct elements of a list with one formula make its filter at least `n` long. -/
theorem count_ge_of_seq {w : Nat → Ident} {s : Nat → Nat} (hs : ∀ n, s n < s (n + 1))
    (hinj : ∀ i j, i < j → w i ≠ w j) {F : Noun} (hF : ∀ n, (w (s n)).2 = F) (S : List Ident) :
    ∀ n, (∀ k, k < n → w (s k) ∈ S) → n ≤ (S.filter (fun i => i.2 = F)).length := by
  have build : ∀ n, ∃ l : List Ident, l.Nodup ∧ l.length = n ∧ ∀ x ∈ l, ∃ k, k < n ∧ x = w (s k) := by
    intro n
    induction n with
    | zero => exact ⟨[], List.nodup_nil, rfl, fun _ h => absurd h List.not_mem_nil⟩
    | succ n ih =>
      obtain ⟨l, hl, hlen, hx⟩ := ih
      refine ⟨w (s n) :: l, List.nodup_cons.mpr ⟨fun hm => ?_, hl⟩, by simp [hlen], fun x hx' => ?_⟩
      · obtain ⟨k, hk, e⟩ := hx _ hm
        exact hinj (s k) (s n) (strictMono_le hs hk) e.symm
      · rcases List.mem_cons.mp hx' with rfl | hx'
        · exact ⟨n, Nat.lt_succ_self n, rfl⟩
        · obtain ⟨k, hk, e⟩ := hx x hx'
          exact ⟨k, by omega, e⟩
  intro n hS
  obtain ⟨l, hl, hlen, hx⟩ := build n
  rw [← hlen]
  refine hl.length_le_of_subset fun x hx' => ?_
  obtain ⟨k, hk, rfl⟩ := hx x hx'
  exact List.mem_filter.mpr ⟨hS k hk, by simp [hF k]⟩

/-- **No infinite sequence of pushes that stay on the stack**, from Kruskal's
theorem.  `w n` is the `n`-th pushed identity and `S n` the stack at its push;
the identities are distinct, their formulas are among `Fs`, every earlier one
is on the stack at a later push, and each push has the guard of `push_guard`
(past `th` frames of its formula, `he` of its subject over theirs is false).
`hemb` is the tree view: an embedding of the trees of an earlier and a later
identity gives `he` of the later subject over the earlier one. -/
theorem noStackSeq_of_kruskal {L : Type} (hK : KruskalBT) (ls : List L) (hls : ∀ a : L, a ∈ ls)
    (he : Sock → Sock → Bool) (th : Nat) (sub : Ident → BT L)
    (hemb : ∀ a b : Ident, BTEmb (sub a) (sub b) → he b.1 a.1 = true) (Fs : List Noun) :
    ¬ ∃ (w : Nat → Ident) (S : Nat → List Ident),
      (∀ n, (w n).2 ∈ Fs) ∧ (∀ i j, i < j → w i ≠ w j) ∧ (∀ i j, i < j → w i ∈ S j) ∧
      (∀ j, th ≤ ((S j).filter (fun i => i.2 = (w j).2)).length →
        ∀ x ∈ S j, x.2 = (w j).2 → he (w j).1 x.1 = false) := by
  rintro ⟨w, S, hFs, hinj, hstk, hguard⟩
  obtain ⟨F, hF⟩ := pigeon_inf Fs (fun n => (w n).2) hFs
  obtain ⟨s, hs, hsF⟩ := subseq_of_inf hF
  obtain ⟨i, j, hij, hb⟩ := hK L ls hls (fun n => sub (w (s (th + n))))
  have hlt : s (th + i) < s (th + j) := strictMono_le hs (by omega)
  have hcount : th ≤ ((S (s (th + j))).filter (fun x => x.2 = (w (s (th + j))).2)).length := by
    rw [hsF (th + j)]
    exact Nat.le_trans (Nat.le_add_right th j)
      (count_ge_of_seq hs hinj hsF _ (th + j) fun k hk => hstk _ _ (strictMono_le hs hk))
  have hfalse := hguard (s (th + j)) hcount (w (s (th + i))) (hstk _ _ hlt)
    (by rw [hsF (th + i), hsF (th + j)])
  rw [hemb _ _ hb] at hfalse
  cases hfalse

end Ana
end SkaModel
end Formalization
