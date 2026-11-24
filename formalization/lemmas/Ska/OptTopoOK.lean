import lemmas.Ska.OptTopo

/-!
# `+bb-topo` gives `TopoOK` on an acyclic CFG

`Acyclic bl`: some rank `ρ` decreases along every jump of every block.  Raw
`+comp` output has it from the Gen blocks, which go down in a rank
(`DownRk` of `CompStraight.lean`, from `run_down` and the rank of the `%6`
under `%next`), through the renaming and chasing of `+to-straight`
(`Sim.down`, `chase_spec`: a chased jump does not go up in the rank); that
the rank carries over to the Straight blocks is for the `+comp` track.

`bbTopo_ok`: if `+bb-topo` returns `topo` on blocks with `Acyclic`, then
`TopoOK bl topo`.  The proof is the usual one for a depth-first walk
(`dfs_spec`).  A visit of `o` from `(out, saw)` returns `L ++ out`, where `L`
starts with `o`, has no duplicates, is new to `saw`, holds only blocks, adds
exactly itself to `saw`, and sends every jump of a member to a later member
of `L ++ out` (`Fwd`).  The registers seen but not yet output are the visits
in progress, the ancestors of `o`, whose ranks are above that of `o`: a jump
of `o` to one of them would go up.  So a jump target already seen is already
output, and lies after `o` once `o` is put in front.
-/

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-- **The CFG is acyclic**: some rank decreases along every jump. -/
def Acyclic (bl : Map Blob) : Prop :=
  ∃ ρ : Nat → Nat, ∀ o b j, HoonMap.get bl o = some b → j ∈ getJmps b.fin → ρ j.there < ρ o

/-- Every jump of a member of `L` goes to a later position of `l`. -/
def Fwd (bl : Map Blob) (L l : List Nat) : Prop :=
  ∀ (i x : Nat) (b : Blob) (j : Jmp), L[i]? = some x → HoonMap.get bl x = some b → j ∈ getJmps b.fin →
    ∃ k : Nat, i < k ∧ l[k]? = some j.there

theorem fwd_append {bl : Map Blob} {A B l : List Nat} (ha : Fwd bl A (A ++ l)) (hb : Fwd bl B l) :
    Fwd bl (A ++ B) (A ++ l) := by
  intro i x b j hx hb' hj
  by_cases hi : i < A.length
  · rw [List.getElem?_append_left hi] at hx
    exact ha i x b j hx hb' hj
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hx
    obtain ⟨k, hk, hk'⟩ := hb _ x b j hx hb' hj
    refine ⟨k + A.length, by omega, ?_⟩
    rw [List.getElem?_append_right (by omega)]
    simpa using hk'

theorem fwd_one {bl : Map Blob} {o : Nat} {l : List Nat}
    (h : ∀ b j, HoonMap.get bl o = some b → j ∈ getJmps b.fin → j.there ∈ l) : Fwd bl [o] ([o] ++ l) := by
  intro i x b j hx hb hj
  cases i with
  | succ i => simp at hx
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
    subst hx
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (h b j hb hj)
    exact ⟨k + 1, by omega, by simpa using hk⟩

theorem fwd_nil {bl : Map Blob} {l : List Nat} : Fwd bl [] l := by
  intro i x b j hx; simp at hx

/-- What a visit of `o` from `(out, saw)` returns. -/
def DfsSpec (bl : Map Blob) (o : Nat) (out saw out' saw' : List Nat) : Prop :=
  ∃ L, out' = L ++ out ∧ L.head? = some o ∧ L.Nodup ∧ (∀ x ∈ L, x ∉ saw) ∧
    (∀ x, x ∈ saw' ↔ x ∈ saw ∨ x ∈ L) ∧ (∀ x ∈ L, (HoonMap.get bl x).isSome) ∧ Fwd bl L (L ++ out)

/-- The state of the fold over the jumps of `o`, from `(out, o :: saw)`. -/
def FoldInv (bl : Map Blob) (o : Nat) (out saw : List Nat) (acc : List Nat × List Nat) : Prop :=
  ∃ M, acc.1 = M ++ out ∧ M.Nodup ∧ (∀ x ∈ M, x ≠ o ∧ x ∉ saw) ∧
    (∀ x, x ∈ acc.2 ↔ x = o ∨ x ∈ saw ∨ x ∈ M) ∧ (∀ x ∈ M, (HoonMap.get bl x).isSome) ∧ Fwd bl M (M ++ out)

/-- **The walk of `+bb-topo`**, on blocks with a rank that decreases along
every jump: a visit of a block not yet seen, whose visits in progress (seen,
not yet output) all have a higher rank, meets `DfsSpec`. -/
theorem dfs_spec {bl : Map Blob} {ρ : Nat → Nat}
    (hρ : ∀ o b j, HoonMap.get bl o = some b → j ∈ getJmps b.fin → ρ j.there < ρ o) :
    ∀ n o out saw out' saw', dfs bl n o (out, saw) = some (out', saw') → o ∉ saw →
      (∀ g ∈ saw, g ∉ out → ρ o < ρ g) → (∀ x ∈ out, x ∈ saw) → DfsSpec bl o out saw out' saw'
  | 0, _, _, _, _, _, h, _, _, _ => by simp [dfs] at h
  | n + 1, o, out, saw, out', saw', h, ho, hg, hos => by
    simp only [dfs, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, ⟨mo, ms⟩, hf, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have fold : ∀ (js : List Jmp) (acc accF : List Nat × List Nat), (∀ j ∈ js, j ∈ getJmps b.fin) →
        js.foldlM (fun (acc : List Nat × List Nat) j =>
          if j.there ∈ acc.2 then some acc else dfs bl n j.there acc) acc = some accF →
        FoldInv bl o out saw acc →
        FoldInv bl o out saw accF ∧ (∀ x ∈ acc.1, x ∈ accF.1) ∧ ∀ j ∈ js, j.there ∈ accF.1 := by
      intro js
      induction js with
      | nil =>
        intro acc accF _ h hi
        simp only [List.foldlM_nil] at h
        cases h
        exact ⟨hi, fun _ h => h, fun _ h => absurd h List.not_mem_nil⟩
      | cons j js ih =>
        intro acc accF hjs h hi
        simp only [List.foldlM_cons] at h
        obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
        have hjb : j ∈ getJmps b.fin := hjs j List.mem_cons_self
        have hlt : ρ j.there < ρ o := hρ o b j hb hjb
        obtain ⟨M, h1, hMn, hMo, hMs, hMb, hMf⟩ := hi
        have step : FoldInv bl o out saw a ∧ (∀ x ∈ acc.1, x ∈ a.1) ∧ j.there ∈ a.1 := by
          by_cases hj : j.there ∈ acc.2
          · simp only [hj, if_true, Option.some.injEq] at ha
            subst ha
            refine ⟨⟨M, h1, hMn, hMo, hMs, hMb, hMf⟩, fun _ h => h, ?_⟩
            rw [h1]
            rcases (hMs _).mp hj with e | e | e
            · rw [e] at hlt; exact absurd hlt (Nat.lt_irrefl _)
            · by_cases e' : j.there ∈ out
              · exact List.mem_append_right _ e'
              · exact absurd (Nat.lt_trans hlt (hg _ e e')) (Nat.lt_irrefl _)
            · exact List.mem_append_left _ e
          · simp only [hj, if_false] at ha
            obtain ⟨outA, sawA⟩ := acc
            obtain ⟨outA', sawA'⟩ := a
            simp only at h1 hMs hj ⊢
            have hg' : ∀ g ∈ sawA, g ∉ outA → ρ j.there < ρ g := by
              intro g hgs hgo
              rcases (hMs g).mp hgs with e | e | e
              · rw [e]; exact hlt
              · exact Nat.lt_trans hlt (hg g e (fun h' => hgo (by rw [h1]; exact List.mem_append_right _ h')))
              · exact absurd (by rw [h1]; exact List.mem_append_left _ e) hgo
            have hos' : ∀ x ∈ outA, x ∈ sawA := by
              intro x hx
              rw [h1] at hx
              rcases List.mem_append.mp hx with e | e
              · exact (hMs x).mpr (Or.inr (Or.inr e))
              · exact (hMs x).mpr (Or.inr (Or.inl (hos x e)))
            obtain ⟨L', e', hL'0, hL'n, hL's, hL'S, hL'b, hL'f⟩ :=
              dfs_spec hρ n j.there outA sawA outA' sawA' ha hj hg' hos'
            refine ⟨⟨L' ++ M, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
            · rw [e', h1, List.append_assoc]
            · refine List.nodup_append.mpr ⟨hL'n, hMn, fun x hx y hy hxy => ?_⟩
              subst hxy
              exact hL's x hx ((hMs x).mpr (Or.inr (Or.inr hy)))
            · intro x hx
              rcases List.mem_append.mp hx with e | e
              · refine ⟨fun h' => hL's x e ((hMs x).mpr (Or.inl h')), fun h' => hL's x e ((hMs x).mpr (Or.inr (Or.inl h')))⟩
              · exact hMo x e
            · intro x
              rw [hL'S x, hMs x, List.mem_append]
              constructor
              · rintro ((h | h | h) | h)
                · exact Or.inl h
                · exact Or.inr (Or.inl h)
                · exact Or.inr (Or.inr (Or.inr h))
                · exact Or.inr (Or.inr (Or.inl h))
              · rintro (h | h | h | h)
                · exact Or.inl (Or.inl h)
                · exact Or.inl (Or.inr (Or.inl h))
                · exact Or.inr h
                · exact Or.inl (Or.inr (Or.inr h))
            · intro x hx
              rcases List.mem_append.mp hx with e | e
              · exact hL'b x e
              · exact hMb x e
            · have := fwd_append (l := M ++ out) (by rw [← h1]; exact hL'f) hMf
              rw [List.append_assoc]; exact this
            · intro x hx; rw [e']; exact List.mem_append_right _ hx
            · rw [e']
              cases L' with
              | nil => simp at hL'0
              | cons y L' =>
                simp only [List.head?_cons, Option.some.injEq] at hL'0
                subst hL'0; exact List.mem_cons_self
        obtain ⟨hia, hma, hja⟩ := step
        obtain ⟨hiF, hmF, hjF⟩ := ih a accF (fun j' hj' => hjs j' (List.mem_cons_of_mem _ hj')) h hia
        refine ⟨hiF, fun x hx => hmF x (hma x hx), fun j' hj' => ?_⟩
        rcases List.mem_cons.mp hj' with rfl | hj'
        · exact hmF _ hja
        · exact hjF j' hj'
    have hi0 : FoldInv bl o out saw (out, o :: saw) := by
      refine ⟨[], rfl, List.nodup_nil, fun _ h => absurd h List.not_mem_nil, fun x => ?_,
        fun _ h => absurd h List.not_mem_nil, fwd_nil⟩
      simp
    obtain ⟨⟨M, h1, hMn, hMo, hMs, hMb, hMf⟩, -, hjs⟩ := fold _ _ _ (fun _ h => h) hf hi0
    simp only at h1 hMs hjs
    refine ⟨o :: M, by rw [h1]; rfl, rfl, List.nodup_cons.mpr ⟨fun h => (hMo o h).1 rfl, hMn⟩, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | e
      · exact ho
      · exact (hMo x e).2
    · intro x
      rw [hMs x, List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | e
      · rw [hb]; rfl
      · exact hMb x e
    · have h1' : Fwd bl [o] ([o] ++ (M ++ out)) := fwd_one fun b' j hb' hj => by
        rw [hb] at hb'; cases hb'; rw [← h1]; exact hjs j hj
      exact fwd_append (A := [o]) h1' hMf

/-- **`+bb-topo` gives `TopoOK` on an acyclic CFG.** -/
theorem bbTopo_ok {fuel : Nat} {bl : Map Blob} {topo : List Nat} (ha : Acyclic bl)
    (h : bbTopo fuel bl = some topo) : TopoOK bl topo := by
  obtain ⟨ρ, hρ⟩ := ha
  simp only [bbTopo, Option.map_eq_some_iff] at h
  obtain ⟨⟨out', saw'⟩, hd, rfl⟩ := h
  obtain ⟨L, e, h0, hn, -, -, hb, hf⟩ :=
    dfs_spec hρ fuel 0 [] [] out' saw' hd (fun h => absurd h List.not_mem_nil)
      (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
  simp only [List.append_nil] at e hf
  subst out'
  simp only
  have hmem : ∀ o, Reach bl o → o ∈ L := by
    intro o hr
    induction hr with
    | zero =>
      cases L with
      | nil => simp at h0
      | cons y L => simp only [List.head?_cons, Option.some.injEq] at h0; subst h0; exact List.mem_cons_self
    | @jump o b j _ hb' hj ih =>
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ih
      obtain ⟨k, -, hk⟩ := hf i o b j hi hb' hj
      exact List.mem_iff_getElem?.mpr ⟨k, hk⟩
  exact ⟨hn, h0, hb, hmem, hf⟩

end Opt
end SkaModel
end Formalization
