import lemmas.Compiler.Mi

/-!
`+git:mi` of the memoization core `+mi` against `Ana.gitMi` of
`lemmas/Ska/Analysis.lean`, on memos of `FinMap`.

```hoon
++  git
  ~%  %git-mi  ..ride  ~
  |=  [m=memo f=^ s=sock]
  ^-  (unit [identity datum])
  =/  entries=(list [* id=identity d=datum])  ~(tap by (gut m f))
  |-  ^-  (unit [identity datum])
  ?~  entries  ~
  ?:  ?&  (huge:so less-code.d.i.entries s)
          %+  huge:so  (app:ca indi.d.i.entries s)
          (app:ca indi.d.i.entries more.id.i.entries)
      ==
    =/  p  (patch-prod [prod map]:d.i.entries s)
    `[id.i.entries d.i.entries(prod sock.p, map src.p)]
  $(entries t.entries)
```

The gate lists the inner map of `gut` with `+tap:by` of the library's second
layer, and its loop (`mi.git.loop`) is `Ana.gitLoop` with `hitTest`: a crash
of `+huge:so` is the model's `none`.  The loop reads, through the context `x`
of the core `+mi`, the library core at axis `7` of `x` (for `+so` and `+ca`)
and `+patch-prod` at axis `22` of `x` (`MiGitIn`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

/-- `~(tap by a)` on a tree, as a Nock equation. -/
theorem tap_by_nock (ctx : Noun) {a : Noun} (h : Tree a) :
    nock (C by.battery (C a ctx)) by.tap.arm = some (listN (tapList a)) := by
  rw [tap_arm, tap_loop, show A 0 = listN [] from rfl, tapF_list h, List.append_nil]

/-- The noun of an element of `~(tap by (gut m f))`: `[code-requirement
[identity datum]]`. -/
noncomputable def gitElem (e : Sock × (Ident × FDatum FinMap)) : Noun :=
  C e.1.toNoun (entryNoun e.2)

/-- `~(tap by (gut m f))`, as the list of `Treap.tap`. -/
theorem tap_inner (l2 : Noun) (n : FinMap Sock (Ident × FDatum FinMap)) :
    nock (C by.battery (C (innerNoun n) l2)) by.tap.arm
      = some (listN ((Treap.tap n).map gitElem)) := by
  show nock (C by.battery (C (FinMap.toNoun entryNoun n) l2)) by.tap.arm = _
  rw [tap_by_nock l2 (Tree.of_isMap (FinMap.isMap_toNoun entryNoun n)), FinMap.tapList_toNoun]
  rfl

/-- What `+git:mi` reads from the context `x` of the core `+mi`: what
`+gut:mi` reads, the pill's library core at axis `7`, and `+patch-prod` with
`+knit-anno` at their axes. -/
abbrev MiGitIn (x : Noun) : Prop :=
  GitGIn x ∧ slot? knit_anno.lib.axis x = some lib ∧
    slot? patch_prod.axis x = some patch_prod.arm ∧ slot? knit_anno.axis x = some knit_anno.arm

@[nock_exec] theorem mi_git_arm (c : Noun) :
    nock c mi.git.arm
      = some (C mi.git.battery (C (C (A 0) (C (C (A 0) (A 0)) (C (A 1) (A 0)))) c)) := by
  nock_open mi.git.arm; simp only [nock_exec]

/-- The loop of `+git:mi` over a list of entries: `Ana.gitLoop`.  The loop
reads the sample only at `s`. -/
theorem mi_git_loop (x : Noun) (hc : MiGitIn x) (m f : Noun) (s : Sock) :
    ∀ es : List (Sock × (Ident × FDatum FinMap)),
    nock (C mi.git.loop (C (listN (es.map gitElem))
        (C mi.git.battery (C (C m (C f s.toNoun)) (C mi.battery x))))) mi.git.loop
      = (gitLoop s es).map (unitNoun entryNoun)
  | [] => by nock_open mi.git.loop; simp [nock_exec, gitLoop, unitNoun]
  | (k, (i, d)) :: es => by
    have ih := mi_git_loop x hc m f s es
    obtain ⟨-, hlib, hpp, hka⟩ := hc
    have hpi : PatchProdIn x := ⟨hka, lib, hlib, soOf_lib, piOf_lib, soPullOf_lib⟩
    have hpg := patch_prod_gate x hpi s d.map d.prod
    have hlib' : slot? 7 x = some lib := hlib
    have hpp' : slot? 22 x = some patch_prod.arm := hpp
    have hu1 := so_huge_gate (C so.battery lib) d.less s
    have hu2 := so_huge_gate (C so.battery lib) (Ca.app d.indi s) (Ca.app d.indi i.1)
    nock_open mi.git.loop
    cases h1 : So.huge d.less s with
    | none =>
      rw [h1] at hu1
      simp [nock_exec, gitElem, entryNoun, identNoun, FDatum.toNoun, hlib', so.lib.arm_at,
        so_lib_arm, so.huge.arm_at, so_huge_arm, hu1, gitLoop, hitTest, FDatum.core, h1]
    | some b1 =>
      rw [h1] at hu1
      cases b1 with
      | false =>
        simp [nock_exec, gitElem, entryNoun, identNoun, FDatum.toNoun, hlib', so.lib.arm_at,
          so_lib_arm, so.huge.arm_at, so_huge_arm, hu1, gitLoop, hitTest, FDatum.core, h1, ih]
      | true =>
        cases h2 : So.huge (Ca.app d.indi s) (Ca.app d.indi i.1) with
        | none =>
          rw [h2] at hu2
          simp [nock_exec, gitElem, entryNoun, identNoun, FDatum.toNoun, hlib', so.lib.arm_at,
            so_lib_arm, so.huge.arm_at, so_huge_arm, hu1, gitLoop, hitTest, FDatum.core, h1, h2,
            ca.lib.arm_at, ca_lib_arm, ca.app.arm_at, ca_app_arm, ca_app_pill, hu2]
        | some b2 =>
          rw [h2] at hu2
          cases b2 with
          | false =>
            simp [nock_exec, gitElem, entryNoun, identNoun, FDatum.toNoun, hlib', so.lib.arm_at,
              so_lib_arm, so.huge.arm_at, so_huge_arm, hu1, gitLoop, hitTest, FDatum.core, h1, h2,
              ca.lib.arm_at, ca_lib_arm, ca.app.arm_at, ca_app_arm, ca_app_pill, hu2, ih]
          | true =>
            simp [nock_exec, gitElem, entryNoun, identNoun, FDatum.toNoun, hlib', so.lib.arm_at,
              so_lib_arm, so.huge.arm_at, so_huge_arm, hu1, gitLoop, hitTest, FDatum.core, h1, h2,
              ca.lib.arm_at, ca_lib_arm, ca.app.arm_at, ca_app_arm, ca_app_pill, hu2, hpp',
              patch_prod_arm, hpg, Anno.toNoun, unitNoun]

/-- Slamming `+git:mi` on a memo of `FinMap`, a formula and a subject sock:
`Ana.gitMi`, crashes included. -/
theorem mi_git_gate (x : Noun) (hc : MiGitIn x) (m : Memo FinMap) (f : Noun) (s : Sock) :
    nock (C mi.git.battery (C (C (memoNoun m) (C f s.toNoun)) (C mi.battery x))) mi.git.battery
      = (gitMi m f s).map (unitNoun entryNoun) := by
  have hloop := mi_git_loop x hc (memoNoun m) f s (Treap.tap (gutMi m f))
  have hgut := mi_gut_gate x hc.1 m f
  obtain ⟨⟨l2, hl2, hby, -, -, -⟩, -, -, -⟩ := hc
  have htap := tap_inner l2 (gutMi m f)
  unfold gitMi
  nock_open mi.git.battery
  simp [nock_exec, hl2, hby, by_arm, by.tap.arm_at, mi.gut.arm_at, mi_gut_arm, hgut, htap, hloop]

/-! ## On the pill's analysis core -/

theorem miGitIn_ana : MiGitIn ana :=
  ⟨gitGIn_ana, knit_anno.lib.arm_at, patch_prod.arm_at, knit_anno.arm_at⟩

theorem mi_git_pill (m : Memo FinMap) (f : Noun) (s : Sock) :
    nock (C mi.git.battery (C (C (memoNoun m) (C f s.toNoun)) (C mi.battery ana))) mi.git.battery
      = (gitMi m f s).map (unitNoun entryNoun) :=
  mi_git_gate ana miGitIn_ana m f s

end Compiler
end Formalization
