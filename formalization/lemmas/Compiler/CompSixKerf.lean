import lemmas.Compiler.CompRunSixNext
import lemmas.Compiler.CompKernGen

/-!
# The test of `+kerf` in the case `%6`, and phase K

The test that sends a `%next` goal with forks or bonds to `+kerf` (phase K)
rather than to `+fork` (phase F) is

    ?|  &((whole q.nomm) (whole r.nomm))
        (this-only laz.goal)
        (lazy-big (soft-less laz.goal))
        (soft-fork laz.goal q.nomm r.nomm)
    ==

(`cr6TK` of `CompRunSixN.lean`).  Here:

* `+this-only` (`compK` arm `178934`, `thoBat`) on every lazy need is the
  model's `thisOnly` (`tho_all`).  Its battery is that of
  `+none-equivalent` (`neBat`) but for the first test,
  `?=(?(%this %none) -.ned.sure.laz)`, which reads only the head of the need;
  the two `+levy` gates are the nouns `neGF` and `neGB` of
  `CompClaGen.lean` (they call the gate's own core).  No departure.
* `+soft-fork` (door arm `221182`, `sfkBat`): with an empty `soft` it is `|`
  on every lazy need (`sfk_all`): each bond's test `(~(has by soft.gen) o.e)`
  fails (`crn_has`), so `?&` never reaches `+need-to-ordered` or `+sound`
  (`sfkSnd`), and the recursion into the bonds and forks gives `|`.  The
  model's `softFork noSoft` is `false` (`softFork_noSoft`).  No departure.
* `cr6tk_eq`: the test is the model's, `kerfTest`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-! ## `+this-only` -/

/-- The battery of `+this-only` (`compK` arm `178934`): the battery of
`+none-equivalent` with the first test `?=(?(%this %none) -.ned.sure.laz)`. -/
def thoBat : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 48)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 48))))))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 25)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 3) (C (A 0) (A 25))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 50)))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 51))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 102)))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 103)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1)))))))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x2fbc) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 58)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) neGF) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x2fbc) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 59)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) neGB) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1)))))))

def thoBunt : Noun :=
  (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))

def thoArm : Noun := C (A 8) (C (C (A 1) thoBunt) (C (C (A 1) thoBat) (C (A 0) (A 1))))

theorem tho_at : slot? 178934 compK = some thoArm := by kernel_rfl

theorem tho_arm (d : Noun) : nock d thoArm = some (C thoBat (C thoBunt d)) := by
  unfold thoArm; simp only [nock_exec]

theorem thisOnlyForks_all : ∀ f : List (Lazy.ForkE CSet),
    thisOnlyForks f = f.all fun e => thisOnly e.1.2 && thisOnly e.2.2
  | [] => rfl
  | ((oy, y), (on, n)) :: rest => by simp [thisOnlyForks, thisOnlyForks_all rest]

theorem thisOnlyBonds_all : ∀ b : List (Nat × Lazy CSet),
    thisOnlyBonds b = b.all fun e => thisOnly e.2
  | [] => rfl
  | (o, l) :: rest => by simp [thisOnlyBonds, thisOnlyBonds_all rest]

mutual
/-- **`+this-only` on every lazy need** (forks and bonds to any depth). -/
theorem tho_all : ∀ laz : Lazy CSet,
    nock (C thoBat (C laz.toNoun compK)) thoBat = some (loob (thisOnly laz))
  | Lazy.mk ⟨ned, lok⟩ fk bd => by
    have hL := compK_layer2
    have hLF := levy_gate_map forkE layer2 neGF (C (C (A 0) lzBunt) (C (A 0) lzBunt))
      (C thoBat (C (C (Sure.toNoun ⟨ned, lok⟩) (C (listN (fk.map forkE)) (listN (bd.map bondE)))) compK))
      (fun e => thisOnly e.1.2 && thisOnly e.2.2) fk
      (fun e he => tho_forks fk e he _)
    have hLB := levy_gate_map bondE layer2 neGB (C (A 0) lzBunt)
      (C thoBat (C (C (Sure.toNoun ⟨ned, lok⟩) (C (listN (fk.map forkE)) (listN (bd.map bondE)))) compK))
      (fun e => thisOnly e.2) bd
      (fun e he => tho_bonds bd e he _)
    unfold lzBunt at hLF hLB
    rw [lazy_toNoun_mk]
    simp only [thisOnly, ← thisOnlyForks_all, ← thisOnlyBonds_all] at hLF hLB ⊢
    cases ned with
    | pair p q =>
      obtain ⟨a, b, hp⟩ := cd_need_cell p
      conv => { lhs; arg 2; unfold thoBat }
      simp [nock_exec, Need.toNoun, Sure.toNoun, hp, eqCode, loob]
    | both r h t =>
      conv => { lhs; arg 2; unfold thoBat }
      simp [nock_exec, Need.toNoun, Sure.toNoun, eqCode_atom, Tag.both, loob]
    | none =>
      simp only [Sure.toNoun, Need.toNoun, Tag.none] at hLF hLB ⊢
      conv => { lhs; arg 2; unfold thoBat }
      rcases cs_small_cases lok with ⟨hsm, hl | hl⟩ | ⟨hsm, n, l, r, hl, hne⟩
      · rw [hl] at hLF hLB ⊢
        cases hb1 : thisOnlyForks fk <;> cases hb2 : thisOnlyBonds bd <;>
          simp [nock_exec, hL, levy_arm, levy.arm_at, hLF, hLB, hsm, loob, hb1, hb2]
      · rw [hl] at hLF hLB ⊢
        cases hb1 : thisOnlyForks fk <;> cases hb2 : thisOnlyBonds bd <;>
          simp [nock_exec, hL, levy_arm, levy.arm_at, hLF, hLB, hsm, loob, hb1, hb2]
      · rw [hl]
        rcases n with k | ⟨n1, n2⟩
        · by_cases hk : k = 1
          · subst hk
            rcases l with l | ⟨l1, l2⟩
            · by_cases hl0 : l = 0
              · subst hl0
                rcases r with r | ⟨r1, r2⟩
                · have hr0 : r ≠ 0 := fun e => hne ⟨rfl, rfl, by rw [e]⟩
                  simp [nock_exec, hsm, loob, eqCode_atom, Ne.symm hr0]
                · simp [nock_exec, hsm, loob, eqCode_atom, eqCode]
              · simp [nock_exec, hsm, loob, eqCode_atom, Ne.symm hl0]
            · simp [nock_exec, hsm, loob, eqCode_atom, eqCode]
          · simp [nock_exec, hsm, loob, eqCode_atom, Ne.symm hk]
        · simp [nock_exec, hsm, loob, eqCode_atom, eqCode]
    | this r0 =>
      simp only [Sure.toNoun, Need.toNoun, Tag.this] at hLF hLB ⊢
      conv => { lhs; arg 2; unfold thoBat }
      rcases cs_small_cases lok with ⟨hsm, hl | hl⟩ | ⟨hsm, n, l, r, hl, hne⟩
      · rw [hl] at hLF hLB ⊢
        cases hb1 : thisOnlyForks fk <;> cases hb2 : thisOnlyBonds bd <;>
          simp [nock_exec, hL, levy_arm, levy.arm_at, hLF, hLB, hsm, loob, hb1, hb2]
      · rw [hl] at hLF hLB ⊢
        cases hb1 : thisOnlyForks fk <;> cases hb2 : thisOnlyBonds bd <;>
          simp [nock_exec, hL, levy_arm, levy.arm_at, hLF, hLB, hsm, loob, hb1, hb2]
      · rw [hl]
        rcases n with k | ⟨n1, n2⟩
        · by_cases hk : k = 1
          · subst hk
            rcases l with l | ⟨l1, l2⟩
            · by_cases hl0 : l = 0
              · subst hl0
                rcases r with r | ⟨r1, r2⟩
                · have hr0 : r ≠ 0 := fun e => hne ⟨rfl, rfl, by rw [e]⟩
                  simp [nock_exec, hsm, loob, eqCode_atom, Ne.symm hr0]
                · simp [nock_exec, hsm, loob, eqCode_atom, eqCode]
              · simp [nock_exec, hsm, loob, eqCode_atom, Ne.symm hl0]
            · simp [nock_exec, hsm, loob, eqCode_atom, eqCode]
          · simp [nock_exec, hsm, loob, eqCode_atom, Ne.symm hk]
        · simp [nock_exec, hsm, loob, eqCode_atom, eqCode]

theorem tho_forks : ∀ (fk : List (Lazy.ForkE CSet)), ∀ e ∈ fk, ∀ L : Noun,
    nock (C neGF (C (forkE e) (C thoBat (C L compK)))) neGF
      = some (loob (thisOnly e.1.2 && thisOnly e.2.2))
  | [], e, he => absurd he List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro L
      have hy := tho_all y
      have hn := tho_all n
      unfold neGF
      cases ey : thisOnly y <;> cases en : thisOnly n <;>
        simp [nock_exec, forkE, hy, hn, ey, en, loob]
    · exact tho_forks rest e he'

theorem tho_bonds : ∀ (bd : List (Nat × Lazy CSet)), ∀ e ∈ bd, ∀ L : Noun,
    nock (C neGB (C (bondE e) (C thoBat (C L compK)))) neGB = some (loob (thisOnly e.2))
  | [], e, he => absurd he List.not_mem_nil
  | (ob, l) :: rest, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro L
      have hl := tho_all l
      unfold neGB
      simp [nock_exec, bondE, hl]
    · exact tho_bonds rest e he'
end

/-! ## `+soft-fork` -/

/-- The `+need-to-ordered` and `+sound` part of the bond gate of `+soft-fork`:
`=/  ned  (need-to-ordered ned.sure.laz.e)  !&((sound q ned) (sound r ned))`.
It runs only when the block is a key of `soft`. -/
def sfkSnd : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0xaebc) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 116))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x5556) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 506)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x5556) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 507)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))

/-- The gate of the `+lien` over the bonds: `(~(has by soft.gen) o.e)` and
`sfkSnd`, or `^$(laz laz.e)`. -/
def sfkGB : Noun :=
  (C (A 6) (C (C (A 6) (C slHas (C sfkSnd (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 13))) (C (A 0) (A 7)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))))))

/-- The gate of the `+lien` over the forks: `|(^$(laz laz.y.e) ^$(laz laz.n.e))`. -/
def sfkGF : Noun :=
  (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 25))) (C (A 0) (A 7)))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 27))) (C (A 0) (A 7)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))))))

/-- The battery of `+soft-fork` (door arm `221182`). -/
def sfkBat : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x2fbde) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 115)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) lzBunt)) (C (C (A 1) sfkGB) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x2fbde) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 114)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) lzBunt) (C (A 0) lzBunt))) (C (C (A 1) sfkGF) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))))))

def sfkBunt : Noun :=
  (C lzBunt (C (C (A 0) (A 0)) (C (A 0) (A 0))))

def sfkArm : Noun := C (A 8) (C (C (A 1) sfkBunt) (C (C (A 1) sfkBat) (C (A 0) (A 1))))

theorem sfk_at : slot? 221182 comp.door = some sfkArm := by kernel_rfl

theorem sfk_arm (d : Noun) : nock d sfkArm = some (C sfkBat (C sfkBunt d)) := by
  unfold sfkArm; simp only [nock_exec]

/-- With an empty `soft`, the model's `+soft-fork` is `false`. -/
theorem softFork_noSoft (u : Need → Bool) : ∀ l : Lazy CSet, softFork Lazy.noSoft u l = false
  | Lazy.mk s f b => by
    simp only [softFork, softForkBonds_noSoft u b, softForkForks_noSoft u f, Bool.or_self]
where
  softForkBonds_noSoft (u : Need → Bool) : ∀ b : List (Nat × Lazy CSet), softForkBonds Lazy.noSoft u b = false
    | [] => rfl
    | (o, l) :: rest => by
      simp only [softForkBonds, Lazy.noSoft, Bool.false_and, Bool.false_or, softFork_noSoft u l,
        softForkBonds_noSoft u rest, Bool.or_self]
  softForkForks_noSoft (u : Need → Bool) : ∀ f : List (Lazy.ForkE CSet), softForkForks Lazy.noSoft u f = false
    | [] => rfl
    | ((oy, y), (on, n)) :: rest => by
      simp only [softForkForks, softFork_noSoft u y, softFork_noSoft u n, softForkForks_noSoft u rest,
        Bool.or_self]

section
variable (hc : CompIn ctx) (x : GenRest) (hx : x.NoSoft) (G0 : Gen (TreapMap mugF))
include hc hx

mutual
/-- **`+soft-fork` with an empty `soft`** is `|` on every lazy need (forks
and bonds to any depth), whatever `q` and `r`. -/
theorem sfk_all : ∀ (laz : Lazy CSet) (qn rn : Noun),
    nock (C sfkBat (C (C laz.toNoun (C qn rn)) (C comp.door (C (genNoun G0 x) ctx)))) sfkBat = some (A 1)
  | Lazy.mk s fk bd, qn, rn => by
    rw [lazy_toNoun_mk]
    have hB := lien_gate layer2 sfkGB (C (A 0) lzBunt)
      (C sfkBat (C (C (C s.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE)))) (C qn rn))
        (C comp.door (C (genNoun G0 x) ctx))))
      (fun _ => false) (bd.map bondE) (fun y hy => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
        exact sfk_bonds bd e he _ qn rn)
    have hF := lien_gate layer2 sfkGF (C (C (A 0) lzBunt) (C (A 0) lzBunt))
      (C sfkBat (C (C (C s.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE)))) (C qn rn))
        (C comp.door (C (genNoun G0 x) ctx))))
      (fun _ => false) (fk.map forkE) (fun y hy => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
        exact sfk_forks fk e he _ qn rn)
    have e1 : (bd.map bondE).any (fun _ => false) = false := by simp
    have e2 : (fk.map forkE).any (fun _ => false) = false := by simp
    rw [e1] at hB
    rw [e2] at hF
    conv => { lhs; arg 2; unfold sfkBat }
    simp [nock_exec, hc, lien.arm_at, lien_arm, hB, hF, loob]

theorem sfk_bonds : ∀ (bd : List (Nat × Lazy CSet)), ∀ e ∈ bd, ∀ (Lz qn rn : Noun),
    nock (C sfkGB (C (bondE e) (C sfkBat (C (C Lz (C qn rn)) (C comp.door (C (genNoun G0 x) ctx)))))) sfkGB
      = some (loob false)
  | [], e, he => absurd he List.not_mem_nil
  | (ob, l) :: rest, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro Lz qn rn
      have ihl := sfk_all l qn rn
      simp only [genNoun] at ihl
      have hhas := crn_has x ob (hx ob)
      unfold sfkGB slHas
      simp [nock_exec, bondE, ihl, hc, by_arm, by.arm_at, by.has.arm_at, has_arm, hhas, genNoun, loob]
    · exact sfk_bonds rest e he'

theorem sfk_forks : ∀ (fk : List (Lazy.ForkE CSet)), ∀ e ∈ fk, ∀ (Lz qn rn : Noun),
    nock (C sfkGF (C (forkE e) (C sfkBat (C (C Lz (C qn rn)) (C comp.door (C (genNoun G0 x) ctx)))))) sfkGF
      = some (loob false)
  | [], e, he => absurd he List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro Lz qn rn
      have ihy := sfk_all y qn rn
      have ihn := sfk_all n qn rn
      unfold sfkGF
      simp [nock_exec, forkE, ihy, ihn, loob]
    · exact sfk_forks rest e he'
end

end

end Compiler
end Formalization
