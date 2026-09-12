import Equiv.SibLive

/-!
# 森の塔

行ごとの frame と値を 1 つの列にまとめる。層 `k` の frame の上に層 `k` の値を
載せると層 `k+1` の frame になる。

```
frameAt 0     = linearForest
frameAt (k+1) = (rows (ofSequence s) k).forest
valAt k       = (rows (ofSequence s) k).value
```

この形にすると行 0 も特別扱いせずに済む。`frameAt 0` が線形森なので、
そこでは 2 つの相異なる列が兄弟になれない（親は必ず 1 つ前の列だから）。
したがって兄弟についての帰納は層 0 で自動的に尽きる。

さらに層 0 では祖先関係が `<` と同じなので、`q1 < q2` なら常に
「`q1` が `q2` の祖先」の場合になる。降下はここで必ず止まる。
-/

namespace Yukito

open OneY OneY.Numeric

/-- 層 `k` の frame。 -/
def frameAt (s : List Nat) : Nat → ParentForest
  | 0 => linearForest
  | k+1 => (rows (ofSequence s) k).forest

/-- 層 `k` の値。 -/
def towerVal (s : List Nat) (k : Nat) : Nat → Nat := (rows (ofSequence s) k).value

/-- 塔の段。frame の上に値を載せると次の frame になる。 -/
theorem frameAt_step (s : List Nat) (k : Nat) :
    (frameAt s (k+1)).parent = restrictedParent (frameAt s k) (towerVal s k) := by
  cases k with
  | zero => rfl
  | succ k => rfl

/-- 層 0 の frame は線形森。 -/
theorem frameAt_zero (s : List Nat) : frameAt s 0 = linearForest := rfl

/-- 層 0 では相異なる 2 列は兄弟になれない。線形森の親は 1 つ前の列だから。 -/
theorem no_siblings_zero (s : List Nat) {t q1 q2 : Nat}
    (h1 : (frameAt s 0).parent q1 = some t)
    (h2 : (frameAt s 0).parent q2 = some t) : q1 = q2 := by
  have e1 : q1 = t + 1 := by
    cases q1 with
    | zero => cases h1
    | succ n => exact congrArg Nat.succ (Option.some.inj h1)
  have e2 : q2 = t + 1 := by
    cases q2 with
    | zero => cases h2
    | succ n => exact congrArg Nat.succ (Option.some.inj h2)
  omega

/-- 層 0 では `q1 < q2` なら `q1` は `q2` の祖先。したがって降下はここで止まる。 -/
theorem ancestor_at_zero (s : List Nat) {q1 q2 : Nat} (h : q1 < q2) :
    ZeroY.Forest.Ancestor (frameAt s 0).parent q2 q1 :=
  (linear_anc_zeroY q2 q1).mpr h

/-- 層 0 での場合 1。`q1 < q2` なら最大性がそのまま効く。 -/
theorem one_at_zero (s : List Nat) {t q1 q2 : Nat}
    (h2 : restrictedParent (frameAt s 0) (towerVal s 0) q2 = some t)
    (hlt : q1 < q2) (ht : t < q1) (hpos : 0 < towerVal s 0 q1) :
    towerVal s 0 q2 ≤ towerVal s 0 q1 :=
  one_of_ancestor t q2 q1 h2 (ancestor_at_zero s hlt) ht hpos

/-! ## 3 択を塔の形で書く

目標は層 `k` での `towerVal s k q2 ≤ towerVal s k q1` である。

1. `q1` が層 `k` の frame で `q2` の祖先 → 最大性で完了
2. `q1` と `q2` が層 `k` の frame で兄弟 → 目標が層 `k-1` に移る
3. どちらでもない → 合流点を取り `q2` を小さい列に置き換える

層 0 では 2 が起きえず（`no_siblings_zero`）、1 が必ず成り立つ（`one_at_zero`）
ので、降下はそこで止まる。 -/

/-- 場合 1。層 `k` の frame で `q1` が `q2` の祖先なら最大性で閉じる。 -/
theorem tower_case_ancestor (s : List Nat) {k t q1 q2 : Nat}
    (h2 : (frameAt s (k+1)).parent q2 = some t)
    (hanc : ZeroY.Forest.Ancestor (frameAt s k).parent q2 q1)
    (ht : t < q1) (hpos : 0 < towerVal s k q1) :
    towerVal s k q2 ≤ towerVal s k q1 := by
  rw [frameAt_step] at h2
  exact one_of_ancestor t q2 q1 h2 hanc ht hpos

/-- 場合 2。層 `k+1` の frame で兄弟なら、層 `k` の目標から層 `k+1` の目標が出る。 -/
theorem tower_case_descent (s : List Nat) {k t q1 q2 : Nat}
    (h1 : (frameAt s (k+1)).parent q1 = some t)
    (h2 : (frameAt s (k+1)).parent q2 = some t)
    (hgoal : towerVal s k q2 ≤ towerVal s k q1) :
    towerVal s (k+1) q2 ≤ towerVal s (k+1) q1 :=
  (sibling_descent (rows (ofSequence s) k) h1 h2).mpr hgoal

/-- 場合 3 の結合部。層 `k` の frame で `z` が `q2` の祖先なら、
`q2` 側を `z` で押さえて連鎖する。 -/
theorem tower_case_meet (s : List Nat) {k t z q1 q2 : Nat}
    (h2 : (frameAt s (k+1)).parent q2 = some t)
    (hz : ZeroY.Forest.Ancestor (frameAt s k).parent q2 z)
    (htz : t < z) (hzpos : 0 < towerVal s k z)
    (hrec : towerVal s k z ≤ towerVal s k q1) :
    towerVal s k q2 ≤ towerVal s k q1 := by
  rw [frameAt_step] at h2
  have := one_of_ancestor t q2 z h2 hz htz hzpos
  omega

/-! ## 帰納の組み立て

前の版では `Resolves` をすべての `q1 < q2` に課していたが、その仮定は一般に偽で
定理が空虚になっていた。降下で実際に保たれるのは次の不変量である。

```
CommonBelow k q1 q2 :  q1 と q2 は層 k の frame で共通の祖先を q1 より左に持つ
```

層 `k+1` で兄弟なら、その親 `t` は層 `k` の frame で両者の祖先であり `t < q1` を
満たすので、`CommonBelow k q1 q2` が従う。したがって降下で保たれる。 -/

/-- `q1` と `q2` が層 `k` の frame で共通の祖先を `q1` より左に持つ。 -/
def CommonBelow (s : List Nat) (k q1 q2 : Nat) : Prop :=
  ∃ t, t < q1 ∧ ZeroY.Forest.Ancestor (frameAt s k).parent q1 t ∧
       ZeroY.Forest.Ancestor (frameAt s k).parent q2 t

/-- 層 `k+1` で兄弟なら、層 `k` で共通の祖先を持つ。 -/
theorem commonBelow_of_siblings (s : List Nat) {k t q1 q2 : Nat}
    (h1 : (frameAt s (k+1)).parent q1 = some t)
    (h2 : (frameAt s (k+1)).parent q2 = some t) : CommonBelow s k q1 q2 := by
  rw [frameAt_step] at h1 h2
  obtain ⟨ha1, _, _, _⟩ := (restrictedParent_some_iff _ _ q1 t).mp h1
  obtain ⟨ha2, _, _, _⟩ := (restrictedParent_some_iff _ _ q2 t).mp h2
  exact ⟨t, ZeroY.Forest.ancestor_lt (frameAt s k).parent_left ha1, ha1, ha2⟩

/-- 層 `k` で 3 択が場合 1 か場合 2 に落ちること。 -/
def Resolves (s : List Nat) (k q1 q2 : Nat) : Prop :=
  (∃ t, (frameAt s (k+1)).parent q2 = some t ∧ t < q1 ∧
        ZeroY.Forest.Ancestor (frameAt s k).parent q2 q1)
  ∨ (∃ t, (frameAt s k).parent q1 = some t ∧ (frameAt s k).parent q2 = some t)

/-! ### 注意：`hres` の充足可能性は未確認

下の `sib_mono_of_resolves` は `hres` を仮定した条件付き定理である。
**その仮定が満たせるかはまだ示していない。** 不変量の候補を 2 つ試して、
どちらも実測で落ちた。

* `CommonBelow`（層 `k` の frame で共通祖先を `q1` より左に持つ）
  → 結論すら含意しない。列 `(1,1,1,2,3)` の層 0 で `q1 = 3`、`q2 = 4` が
    `U 3 = 2 < U 4 = 3` となる。
* 「層 `k+1` で兄弟」→ 結論を含意しない。列 `(1,1,2,5,7,5)` の層 1 で
  `q1 = 4`、`q2 = 5` が `U 4 = 2 < U 5 = 3` となる。

実測で確かめてある正しい対応は次である。

```
兄弟      frameAt s k
値        towerVal s k
liveness  (frameAt s (k+1)).parent q1 ≠ none
```

この形なら値 12 まで 123,641 件で反例が無い。上の 2 つの反例も、この対応では
該当層で `q1` が死んでいるため除外される。ただしこの形を `hres` の仮定に
落とし込む作業は済んでいない。層の対応を取り違えやすいので注意する。 -/

/-- 組み立て。`Resolves` があれば、生きている左の列について単調性が出る。
`hres` の充足可能性は未確認である（上の注意を参照）。 -/
theorem sib_mono_of_resolves (s : List Nat)
    (hres : ∀ k q1 q2, q1 < q2 → CommonBelow s k q1 q2 → Resolves s k q1 q2) :
    ∀ k q1 q2, q1 < q2 → CommonBelow s k q1 q2 →
      (∀ m, m ≤ k → 0 < towerVal s m q1) →
      towerVal s k q2 ≤ towerVal s k q1 := by
  intro k
  induction k with
  | zero =>
      intro q1 q2 hlt hcb hpos
      rcases hres 0 q1 q2 hlt hcb with ⟨t, h2, ht, hanc⟩ | ⟨t, h1, h2⟩
      · exact tower_case_ancestor s h2 hanc ht (hpos 0 (Nat.le_refl _))
      · exact absurd (no_siblings_zero s h1 h2) (by omega)
  | succ k ih =>
      intro q1 q2 hlt hcb hpos
      rcases hres (k+1) q1 q2 hlt hcb with ⟨t, h2, ht, hanc⟩ | ⟨t, h1, h2⟩
      · exact tower_case_ancestor s h2 hanc ht (hpos (k+1) (Nat.le_refl _))
      · exact tower_case_descent s h1 h2
          (ih q1 q2 hlt (commonBelow_of_siblings s h1 h2)
            (fun m hm => hpos m (by omega)))

/-! ## 正しい不変量

層の対応を取り違えていたので立て直す。目標が層 `m` のとき、担ぐべき条件は

```
Inv m q1 q2 :  (frameAt s (m+1)).parent q2 = some t かつ t < q1 < q2
               かつ (frameAt s (m+2)).parent q1 ≠ none
```

である。liveness を **一段上** に取るのが要点で、降下すると弱まるだけなので保たれる。

実測では値 12 まで 271,452 列・191,959 件でこの条件から結論が出ており、反例が無い。
内訳は祖先 189,600、兄弟 1,775、どちらでもない 584 である。 -/

/-- liveness は一段下へ伝わる。行が上がるほど値は増えないため。 -/
theorem frame_live_down (s : List Nat) (k q : Nat)
    (h : (frameAt s (k+2)).parent q ≠ none) : (frameAt s (k+1)).parent q ≠ none := by
  have h2 : 0 < (rows (ofSequence s) (k+2)).value q := by
    rcases hq : (frameAt s (k+2)).parent q with _ | z
    · exact absurd hq h
    · exact (rows_parent_iff_next_live (ofSequence s) (k+1) q).mp ⟨z, hq⟩
  have hle : (rows (ofSequence s) (k+2)).value q ≤ (rows (ofSequence s) (k+1)).value q :=
    rows_value_le (ofSequence s) (k+1) q
  obtain ⟨p, hp⟩ := (rows_parent_iff_next_live (ofSequence s) k q).mpr (by omega)
  intro hn
  rw [show (frameAt s (k+1)).parent = (rows (ofSequence s) k).forest.parent from rfl,
    hp] at hn
  cases hn

/-- liveness から、その層で値が正であることが出る。 -/
theorem frame_live_pos (s : List Nat) (k q : Nat)
    (h : (frameAt s (k+1)).parent q ≠ none) : 0 < towerVal s k q := by
  rcases hq : (frameAt s (k+1)).parent q with _ | z
  · exact absurd hq h
  · have := (rows_parent_iff_next_live (ofSequence s) k q).mp ⟨z, hq⟩
    have hle : (rows (ofSequence s) (k+1)).value q ≤ (rows (ofSequence s) k).value q :=
      rows_value_le (ofSequence s) k q
    show 0 < (rows (ofSequence s) k).value q
    omega

/-- 目標が層 `m` のときに担ぐ条件。 -/
def Inv (s : List Nat) (m q1 q2 : Nat) : Prop :=
  (∃ t, (frameAt s (m+1)).parent q2 = some t ∧ t < q1) ∧ q1 < q2 ∧
    (frameAt s (m+2)).parent q1 ≠ none

/-- 不変量から、その層で `q1` の値が正であることが出る。 -/
theorem inv_pos (s : List Nat) {m q1 q2 : Nat} (h : Inv s m q1 q2) :
    0 < towerVal s m q1 :=
  frame_live_pos s m q1 (frame_live_down s m q1 h.2.2)

/-- 兄弟なら不変量が一段下へ移る。 -/
theorem inv_descend (s : List Nat) {m t q1 q2 : Nat}
    (h : Inv s (m+1) q1 q2)
    (h1 : (frameAt s (m+1)).parent q1 = some t)
    (h2 : (frameAt s (m+1)).parent q2 = some t) : Inv s m q1 q2 :=
  ⟨⟨t, h2, (frameAt s (m+1)).parent_left h1⟩, h.2.1, frame_live_down s (m+1) q1 h.2.2⟩

end Yukito
