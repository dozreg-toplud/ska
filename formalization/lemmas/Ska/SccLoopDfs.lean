import lemmas.Ska.SccLoop

/-! # The DFS postorder of `+compile-scc-in` (README Gaps 21.11, item 1)

The trap `=/  order` of `+compile-scc-in` (`desk/lib/nock-compilation.hoon`, lines 3653 to 3672),
with fuel: `vis` the visited bells, `out` the postorder reversed, `stk` the frames `[b kids]` (the
kids not yet looked at), `roots` the roots left.

* `dfsF kl n vis out stk roots`: the trap; `none` when the fuel runs out.
* `dfsOrder kl roots`: the trap from `[~ ~]`, `~`, `roots` on the fuel `dfsFuel kl roots`.
* `dfsF_total`: when every kid of a root is a root, the trap returns on that fuel
  (the measure: the roots not visited times `W`, plus one per frame and per kid on the stack,
  plus the roots left, with `W` above the kids of any root).
* `dfsOrder_sub`, `dfsOrder_cover`: the order holds exactly the roots (as a set). -/

namespace Formalization.SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {B : Type} [DecidableEq B]

/-- The trap of the DFS, with fuel. -/
def dfsF (kl : B → List B) : Nat → List B → List B → List (B × List B) → List B → Option (List B)
  | 0, _, _, _, _ => none
  | _ + 1, _, out, [], [] => some out.reverse
  | n + 1, vis, out, [], r :: rs =>
    if r ∈ vis then dfsF kl n vis out [] rs else dfsF kl n (r :: vis) out [(r, kl r)] rs
  | n + 1, vis, out, (b, []) :: stk, roots => dfsF kl n vis (b :: out) stk roots
  | n + 1, vis, out, (b, k :: ks) :: stk, roots =>
    if k ∈ vis then dfsF kl n vis out ((b, ks) :: stk) roots
    else dfsF kl n (k :: vis) out ((k, kl k) :: (b, ks) :: stk) roots

/-- `W`: above the number of kids of any root. -/
def dfsW (kl : B → List B) (roots : List B) : Nat := 2 + (roots.map fun x => (kl x).length).sum

/-- The fuel of the DFS. -/
def dfsFuel (kl : B → List B) (roots : List B) : Nat :=
  roots.length * dfsW kl roots + roots.length + 1

/-- **The DFS postorder** of `roots` over `kl`. -/
def dfsOrder (kl : B → List B) (roots : List B) : List B :=
  (dfsF kl (dfsFuel kl roots) [] [] [] roots).getD []

/-! ## The measure -/

/-- The roots of `U` not visited. -/
def dfsLeft (U vis : List B) : Nat := (U.filter fun x => decide (x ∉ vis)).length

/-- One per frame and per kid on the stack. -/
def dfsStk : List (B × List B) → Nat
  | [] => 0
  | (_, ks) :: stk => 1 + ks.length + dfsStk stk

theorem filt_le (p q : B → Bool) (h : ∀ x, q x = true → p x = true) :
    ∀ U : List B, (U.filter q).length ≤ (U.filter p).length
  | [] => by simp
  | x :: U => by
    have := filt_le p q h U
    cases hq : q x
    · cases hp : p x <;> simp [List.filter_cons, hq, hp] <;> omega
    · simp [List.filter_cons, hq, h x hq]; omega

theorem filt_lt (p q : B → Bool) (h : ∀ x, q x = true → p x = true) :
    ∀ (U : List B) (k : B), k ∈ U → p k = true → q k = false →
      (U.filter q).length < (U.filter p).length
  | [], _, hk, _, _ => by simp at hk
  | x :: U, k, hk, hp, hq => by
    have hle := filt_le p q h U
    rcases List.mem_cons.1 hk with rfl | hk
    · simp [List.filter_cons, hq, hp]; omega
    · have := filt_lt p q h U k hk hp hq
      cases hqx : q x
      · cases hpx : p x <;> simp [List.filter_cons, hqx, hpx] <;> omega
      · simp [List.filter_cons, hqx, h x hqx]; omega

theorem dfsLeft_le (U vis : List B) (k : B) : dfsLeft U (k :: vis) ≤ dfsLeft U vis :=
  filt_le _ _ (fun x hx => by simp at hx ⊢; exact hx.2) U

theorem dfsLeft_lt (U vis : List B) (k : B) (hk : k ∈ U) (hv : k ∉ vis) :
    dfsLeft U (k :: vis) < dfsLeft U vis :=
  filt_lt _ _ (fun x hx => by simp at hx ⊢; exact hx.2) U k hk (by simp [hv]) (by simp)

theorem len_le_sum (kl : B → List B) : ∀ (U : List B) (k : B), k ∈ U →
    (kl k).length ≤ (U.map fun x => (kl x).length).sum
  | [], _, h => by simp at h
  | x :: U, k, h => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := len_le_sum kl U k h; omega

/-- The invariant of the DFS: the roots left and the kids on the stack are in `U`. -/
def DfsInv (U : List B) (stk : List (B × List B)) (roots : List B) : Prop :=
  (∀ r ∈ roots, r ∈ U) ∧ ∀ f ∈ stk, ∀ k ∈ f.2, k ∈ U

/-- **The DFS returns** once the fuel is above the measure. -/
theorem dfsF_ret (kl : B → List B) (U : List B) (hcl : ∀ b ∈ U, ∀ k ∈ kl b, k ∈ U) :
    ∀ (n : Nat) (vis out : List B) (stk : List (B × List B)) (roots : List B),
      DfsInv U stk roots →
      dfsLeft U vis * dfsW kl U + dfsStk stk + roots.length < n →
      ∃ l, dfsF kl n vis out stk roots = some l := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; omega
  | succ n ih =>
    intro vis out stk roots hi hm
    have hW : ∀ k ∈ U, (kl k).length + 1 < dfsW kl U := by
      intro k hk; have := len_le_sum kl U k hk; unfold dfsW; omega
    match stk, roots with
    | [], [] => exact ⟨_, rfl⟩
    | [], r :: rs =>
      simp only [dfsF]
      have hr : r ∈ U := hi.1 r (List.mem_cons_self ..)
      have hrs : ∀ x ∈ rs, x ∈ U := fun x hx => hi.1 x (List.mem_cons_of_mem _ hx)
      split
      · refine ih _ _ _ _ ⟨hrs, by simp⟩ ?_
        simp [dfsStk] at hm ⊢; omega
      · next hv =>
        refine ih _ _ _ _ ⟨hrs, ?_⟩ ?_
        · intro f hf k hk
          simp at hf; subst hf; exact hcl r hr k hk
        · have hlt := dfsLeft_lt U vis r hr hv
          have hwr := hW r hr
          simp only [dfsStk, List.length_cons] at hm ⊢
          have : dfsLeft U (r :: vis) * dfsW kl U + dfsW kl U ≤ dfsLeft U vis * dfsW kl U := by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt
          omega
    | (b, []) :: stk, roots =>
      simp only [dfsF]
      refine ih _ _ _ _ ⟨hi.1, fun f hf => hi.2 f (List.mem_cons_of_mem _ hf)⟩ ?_
      simp [dfsStk] at hm ⊢; omega
    | (b, k :: ks) :: stk, roots =>
      simp only [dfsF]
      have hk : k ∈ U := hi.2 (b, k :: ks) (List.mem_cons_self ..) k (List.mem_cons_self ..)
      have hks : ∀ x ∈ ks, x ∈ U :=
        fun x hx => hi.2 (b, k :: ks) (List.mem_cons_self ..) x (List.mem_cons_of_mem _ hx)
      have hst : ∀ f ∈ stk, ∀ x ∈ f.2, x ∈ U := fun f hf => hi.2 f (List.mem_cons_of_mem _ hf)
      split
      · refine ih _ _ _ _ ⟨hi.1, ?_⟩ ?_
        · intro f hf
          rcases List.mem_cons.1 hf with rfl | hf
          · exact hks
          · exact hst f hf
        · simp [dfsStk] at hm ⊢; omega
      · next hv =>
        refine ih _ _ _ _ ⟨hi.1, ?_⟩ ?_
        · intro f hf
          rcases List.mem_cons.1 hf with rfl | hf
          · exact hcl k hk
          · rcases List.mem_cons.1 hf with rfl | hf
            · exact hks
            · exact hst f hf
        · have hlt := dfsLeft_lt U vis k hk hv
          have hwk := hW k hk
          simp only [dfsStk, List.length_cons] at hm ⊢
          have : dfsLeft U (k :: vis) * dfsW kl U + dfsW kl U ≤ dfsLeft U vis * dfsW kl U := by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt
          omega

theorem dfsLeft_nil_le (U : List B) : dfsLeft U [] ≤ U.length := by
  unfold dfsLeft; exact List.length_filter_le _ _

/-- **The DFS from the roots returns `dfsOrder`** when every kid of a root is a root. -/
theorem dfsF_total (kl : B → List B) (roots : List B) (hcl : ∀ b ∈ roots, ∀ k ∈ kl b, k ∈ roots) :
    dfsF kl (dfsFuel kl roots) [] [] [] roots = some (dfsOrder kl roots) := by
  obtain ⟨l, hl⟩ := dfsF_ret kl roots hcl (dfsFuel kl roots) [] [] [] roots
    ⟨fun r hr => hr, by simp⟩ (by
      have h1 := dfsLeft_nil_le roots
      have : dfsLeft roots [] * dfsW kl roots ≤ roots.length * dfsW kl roots :=
        Nat.mul_le_mul_right _ h1
      simp only [dfsFuel, dfsStk]; omega)
  unfold dfsOrder; rw [hl]; rfl

/-! ## What the order holds -/

/-- The bells of the frames of a stack. -/
def stkBells (stk : List (B × List B)) : List B := stk.map Prod.fst

/-- Every bell the DFS puts in `out` is a root. -/
theorem dfsF_sub (kl : B → List B) (U : List B) (hcl : ∀ b ∈ U, ∀ k ∈ kl b, k ∈ U) :
    ∀ (n : Nat) (vis out : List B) (stk : List (B × List B)) (roots l : List B),
      (∀ r ∈ roots, r ∈ U) → (∀ f ∈ stk, f.1 ∈ U ∧ ∀ k ∈ f.2, k ∈ U) → (∀ x ∈ out, x ∈ U) →
      dfsF kl n vis out stk roots = some l → ∀ x ∈ l, x ∈ U := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ h; simp [dfsF] at h
  | succ n ih =>
    intro vis out stk roots l hr hs ho h
    match stk, roots with
    | [], [] =>
      simp only [dfsF, Option.some.injEq] at h; subst h
      intro x hx; exact ho x (List.mem_reverse.1 hx)
    | [], r :: rs =>
      have hr0 : r ∈ U := hr r (List.mem_cons_self ..)
      have hrs : ∀ x ∈ rs, x ∈ U := fun x hx => hr x (List.mem_cons_of_mem _ hx)
      simp only [dfsF] at h
      split at h
      · exact ih _ _ _ _ _ hrs (by simp) ho h
      · refine ih _ _ _ _ _ hrs ?_ ho h
        intro f hf; simp at hf; subst hf; exact ⟨hr0, hcl r hr0⟩
    | (b, []) :: stk, roots =>
      simp only [dfsF] at h
      have hb := (hs (b, []) (List.mem_cons_self ..)).1
      refine ih _ _ _ _ _ hr (fun f hf => hs f (List.mem_cons_of_mem _ hf)) ?_ h
      intro x hx; rcases List.mem_cons.1 hx with rfl | hx
      · exact hb
      · exact ho x hx
    | (b, k :: ks) :: stk, roots =>
      simp only [dfsF] at h
      have hf0 := hs (b, k :: ks) (List.mem_cons_self ..)
      have hk : k ∈ U := hf0.2 k (List.mem_cons_self ..)
      have hf1 : (b, ks).1 ∈ U ∧ ∀ x ∈ (b, ks).2, x ∈ U :=
        ⟨hf0.1, fun x hx => hf0.2 x (List.mem_cons_of_mem _ hx)⟩
      split at h
      · refine ih _ _ _ _ _ hr ?_ ho h
        intro f hf; rcases List.mem_cons.1 hf with rfl | hf
        · exact hf1
        · exact hs f (List.mem_cons_of_mem _ hf)
      · refine ih _ _ _ _ _ hr ?_ ho h
        intro f hf; rcases List.mem_cons.1 hf with rfl | hf
        · exact ⟨hk, hcl k hk⟩
        · rcases List.mem_cons.1 hf with rfl | hf
          · exact hf1
          · exact hs f (List.mem_cons_of_mem _ hf)

/-- Every root ends in `out`: each bell is a root left or visited, and a visited bell is in
`out` or the bell of a frame. -/
theorem dfsF_cover (kl : B → List B) :
    ∀ (n : Nat) (vis out : List B) (stk : List (B × List B)) (roots l : List B) (x : B),
      (x ∈ roots ∨ x ∈ vis) → (∀ y ∈ vis, y ∈ out ∨ y ∈ stkBells stk) →
      dfsF kl n vis out stk roots = some l → x ∈ l := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ h; simp [dfsF] at h
  | succ n ih =>
    intro vis out stk roots l x hx hv h
    match stk, roots with
    | [], [] =>
      simp only [dfsF, Option.some.injEq] at h; subst h
      rcases hx with hx | hx
      · simp at hx
      · rcases hv x hx with h | h
        · exact List.mem_reverse.2 h
        · simp [stkBells] at h
    | [], r :: rs =>
      simp only [dfsF] at h
      split at h
      · next hr =>
        refine ih _ _ _ _ _ x ?_ hv h
        rcases hx with hx | hx
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact Or.inr hr
          · exact Or.inl hx
        · exact Or.inr hx
      · refine ih _ _ _ _ _ x ?_ ?_ h
        · rcases hx with hx | hx
          · rcases List.mem_cons.1 hx with rfl | hx
            · exact Or.inr (List.mem_cons_self ..)
            · exact Or.inl hx
          · exact Or.inr (List.mem_cons_of_mem _ hx)
        · intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · right; simp [stkBells]
          · rcases hv y hy with h | h
            · exact Or.inl h
            · simp [stkBells] at h
    | (b, []) :: stk, roots =>
      simp only [dfsF] at h
      refine ih _ _ _ _ _ x hx ?_ h
      intro y hy
      rcases hv y hy with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · simp only [stkBells, List.map_cons, List.mem_cons] at h
        rcases h with rfl | h
        · exact Or.inl (List.mem_cons_self ..)
        · exact Or.inr h
    | (b, k :: ks) :: stk, roots =>
      simp only [dfsF] at h
      split at h
      · refine ih _ _ _ _ _ x hx ?_ h
        intro y hy
        rcases hv y hy with h | h
        · exact Or.inl h
        · right; simpa [stkBells] using h
      · refine ih _ _ _ _ _ x ?_ ?_ h
        · rcases hx with hx | hx
          · exact Or.inl hx
          · exact Or.inr (List.mem_cons_of_mem _ hx)
        · intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · right; simp [stkBells]
          · rcases hv y hy with h | h
            · exact Or.inl h
            · right; simp only [stkBells, List.map_cons, List.mem_cons] at h ⊢
              rcases h with h | h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr h)

/-- **The order holds only roots.** -/
theorem dfsOrder_sub (kl : B → List B) (roots : List B) (h : ∀ b ∈ roots, ∀ k ∈ kl b, k ∈ roots) :
    ∀ b ∈ dfsOrder kl roots, b ∈ roots :=
  dfsF_sub kl roots h _ [] [] [] roots _ (fun r hr => hr) (by simp) (by simp) (dfsF_total kl roots h)

/-- **The order holds every root.** -/
theorem dfsOrder_cover (kl : B → List B) (roots : List B) (h : ∀ b ∈ roots, ∀ k ∈ kl b, k ∈ roots) :
    ∀ b ∈ roots, b ∈ dfsOrder kl roots :=
  fun b hb => dfsF_cover kl _ [] [] [] roots _ b (Or.inl hb) (by simp) (dfsF_total kl roots h)

end Formalization.SkaModel.SccLoop
