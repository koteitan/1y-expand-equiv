import Equiv.SibLive

/-!
# 森の塔

行ごとの frame と値を 1 つの列にまとめる。層 `k` の frame の上に層 `k` の値を
載せると層 `k+1` の frame になる。

```
frameAt 0     = linearForest
frameAt (k+1) = (rows T.base k).forest
valAt k       = (rows T.base k).value
```

この形にすると行 0 も特別扱いせずに済む。`frameAt 0` が線形森なので、
そこでは 2 つの相異なる列が兄弟になれない（親は必ず 1 つ前の列だから）。
したがって兄弟についての帰納は層 0 で自動的に尽きる。

さらに層 0 では祖先関係が `<` と同じなので、`q1 < q2` なら常に
「`q1` が `q2` の祖先」の場合になる。降下はここで必ず止まる。
-/

namespace Yukito

open OneY OneY.Numeric

/-- 塔。底の frame と、その上に載る行。底についての 2 つの義務を持つ。

`ofSequence s` の塔では底の frame が線形森で、2 つの義務は自明である。抽出後の行の
塔では底の frame が `topForest` で、義務は `TopFrame.lean` で証明する。 -/
structure Tower where
  /-- 底の frame。 -/
  frame0 : ParentForest
  /-- その上に載る行。 -/
  base : Row
  /-- 行の森は底の frame 上の `restrictedParent`。 -/
  hbase : ∀ c, base.forest.parent c = restrictedParent frame0 base.value c
  /-- 値はすべて正。 -/
  hpos : ∀ c, 0 < base.value c
  /-- 底の義務 1：最左の子は右隣。 -/
  A0 : ∀ root e, frame0.parent e = some root → frame0.parent (root + 1) = some root
  /-- 底の義務 2：右隣の兄弟の単調性。 -/
  B0 : ∀ root e, frame0.parent (root + 1) = some root → frame0.parent e = some root →
        root + 1 < e → base.value e ≤ base.value (root + 1)

/-- 橋渡しの設定。塔と、列の上限。上限より右の列は値 1 で、行 1 以降では死ぬ。 -/
structure Setting where
  /-- 塔。 -/
  tower : Tower
  /-- 列の上限。 -/
  n : Nat
  /-- 上限より右の列の値は 1。 -/
  htail : ∀ c, n ≤ c → tower.base.value c = 1

/-- 上限より右の列は行 1 以降で死んでいる。 -/
theorem setting_value_zero_of_ge (S : Setting) (r c : Nat) (hr : 0 < r) (h : S.n ≤ c) :
    (rows S.tower.base r).value c = 0 := by
  have h1 : (rows S.tower.base 1).value c = 0 := by
    show S.tower.base.difference c = 0
    have hn := Row.parent_none_of_one S.tower.base (S.htail c h)
    simp only [Row.difference, hn]
  have h2 : (rows S.tower.base r).value c ≤ (rows S.tower.base 1).value c :=
    rows_value_antitone S.tower.base hr c
  omega

/-- 層 `k` の frame。 -/
def frameAt (T : Tower) : Nat → ParentForest
  | 0 => T.frame0
  | k+1 => (rows T.base k).forest

/-- 層 `k` の値。 -/
def towerVal (T : Tower) (k : Nat) : Nat → Nat := (rows T.base k).value

/-- 塔の段。frame の上に値を載せると次の frame になる。 -/
theorem frameAt_step (T : Tower) (k : Nat) :
    (frameAt T (k+1)).parent = restrictedParent (frameAt T k) (towerVal T k) := by
  cases k with
  | zero => exact funext T.hbase
  | succ k => rfl

/-- 層 0 の frame は塔の底。 -/
theorem frameAt_zero (T : Tower) : frameAt T 0 = T.frame0 := rfl

/-! ## 3 択を塔の形で書く

目標は層 `k` での `towerVal T k q2 ≤ towerVal T k q1` である。

1. `q1` が層 `k` の frame で `q2` の祖先 → 最大性で完了
2. `q1` と `q2` が層 `k` の frame で兄弟 → 目標が層 `k-1` に移る
3. どちらでもない → 合流点を取り `q2` を小さい列に置き換える

層 0 では 2 が起きえず（`no_siblings_zero`）、1 が必ず成り立つ（`one_at_zero`）
ので、降下はそこで止まる。 -/

/-- 場合 1。層 `k` の frame で `q1` が `q2` の祖先なら最大性で閉じる。 -/
theorem tower_case_ancestor (T : Tower) {k t q1 q2 : Nat}
    (h2 : (frameAt T (k+1)).parent q2 = some t)
    (hanc : ZeroY.Forest.Ancestor (frameAt T k).parent q2 q1)
    (ht : t < q1) (hpos : 0 < towerVal T k q1) :
    towerVal T k q2 ≤ towerVal T k q1 := by
  rw [frameAt_step] at h2
  exact one_of_ancestor t q2 q1 h2 hanc ht hpos

/-- 場合 2。層 `k+1` の frame で兄弟なら、層 `k` の目標から層 `k+1` の目標が出る。 -/
theorem tower_case_descent (T : Tower) {k t q1 q2 : Nat}
    (h1 : (frameAt T (k+1)).parent q1 = some t)
    (h2 : (frameAt T (k+1)).parent q2 = some t)
    (hgoal : towerVal T k q2 ≤ towerVal T k q1) :
    towerVal T (k+1) q2 ≤ towerVal T (k+1) q1 :=
  (sibling_descent (rows T.base k) h1 h2).mpr hgoal

/-- 場合 3 の結合部。層 `k` の frame で `z` が `q2` の祖先なら、
`q2` 側を `z` で押さえて連鎖する。 -/
theorem tower_case_meet (T : Tower) {k t z q1 q2 : Nat}
    (h2 : (frameAt T (k+1)).parent q2 = some t)
    (hz : ZeroY.Forest.Ancestor (frameAt T k).parent q2 z)
    (htz : t < z) (hzpos : 0 < towerVal T k z)
    (hrec : towerVal T k z ≤ towerVal T k q1) :
    towerVal T k q2 ≤ towerVal T k q1 := by
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
def CommonBelow (T : Tower) (k q1 q2 : Nat) : Prop :=
  ∃ t, t < q1 ∧ ZeroY.Forest.Ancestor (frameAt T k).parent q1 t ∧
       ZeroY.Forest.Ancestor (frameAt T k).parent q2 t

/-- 層 `k+1` で兄弟なら、層 `k` で共通の祖先を持つ。 -/
theorem commonBelow_of_siblings (T : Tower) {k t q1 q2 : Nat}
    (h1 : (frameAt T (k+1)).parent q1 = some t)
    (h2 : (frameAt T (k+1)).parent q2 = some t) : CommonBelow T k q1 q2 := by
  rw [frameAt_step] at h1 h2
  obtain ⟨ha1, _, _, _⟩ := (restrictedParent_some_iff _ _ q1 t).mp h1
  obtain ⟨ha2, _, _, _⟩ := (restrictedParent_some_iff _ _ q2 t).mp h2
  exact ⟨t, ZeroY.Forest.ancestor_lt (frameAt T k).parent_left ha1, ha1, ha2⟩

/-- 層 `k` で 3 択が場合 1 か場合 2 に落ちること。 -/
def Resolves (T : Tower) (k q1 q2 : Nat) : Prop :=
  (∃ t, (frameAt T (k+1)).parent q2 = some t ∧ t < q1 ∧
        ZeroY.Forest.Ancestor (frameAt T k).parent q2 q1)
  ∨ (∃ t, (frameAt T k).parent q1 = some t ∧ (frameAt T k).parent q2 = some t)

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
兄弟      frameAt T k
値        towerVal T k
liveness  (frameAt T (k+1)).parent q1 ≠ none
```

この形なら値 12 まで 123,641 件で反例が無い。上の 2 つの反例も、この対応では
該当層で `q1` が死んでいるため除外される。ただしこの形を `hres` の仮定に
落とし込む作業は済んでいない。層の対応を取り違えやすいので注意する。 -/

/-! 以前ここに `Resolves` を仮定した組み立て `sib_mono_of_resolves` を置いていた。
仮定を満たす不変量が見つからず使わなかったので外した。潰した予想の記録として
下の注意を残す。 -/

/-! ## 正しい不変量

層の対応を取り違えていたので立て直す。目標が層 `m` のとき、担ぐべき条件は

```
Inv m q1 q2 :  (frameAt T (m+1)).parent q2 = some t かつ t < q1 < q2
               かつ (frameAt T (m+2)).parent q1 ≠ none
```

である。liveness を **一段上** に取るのが要点で、降下すると弱まるだけなので保たれる。

実測では値 12 まで 271,452 列・191,959 件でこの条件から結論が出ており、反例が無い。
内訳は祖先 189,600、兄弟 1,775、どちらでもない 584 である。 -/

/-- liveness は一段下へ伝わる。行が上がるほど値は増えないため。 -/
theorem frame_live_down (T : Tower) (k q : Nat)
    (h : (frameAt T (k+2)).parent q ≠ none) : (frameAt T (k+1)).parent q ≠ none := by
  have h2 : 0 < (rows T.base (k+2)).value q := by
    rcases hq : (frameAt T (k+2)).parent q with _ | z
    · exact absurd hq h
    · exact (rows_parent_iff_next_live T.base (k+1) q).mp ⟨z, hq⟩
  have hle : (rows T.base (k+2)).value q ≤ (rows T.base (k+1)).value q :=
    rows_value_le T.base (k+1) q
  obtain ⟨p, hp⟩ := (rows_parent_iff_next_live T.base k q).mpr (by omega)
  intro hn
  rw [show (frameAt T (k+1)).parent = (rows T.base k).forest.parent from rfl,
    hp] at hn
  cases hn

/-- liveness から、その層で値が正であることが出る。 -/
theorem frame_live_pos (T : Tower) (k q : Nat)
    (h : (frameAt T (k+1)).parent q ≠ none) : 0 < towerVal T k q := by
  rcases hq : (frameAt T (k+1)).parent q with _ | z
  · exact absurd hq h
  · have := (rows_parent_iff_next_live T.base k q).mp ⟨z, hq⟩
    have hle : (rows T.base (k+1)).value q ≤ (rows T.base k).value q :=
      rows_value_le T.base k q
    show 0 < (rows T.base k).value q
    omega

/-- 目標が層 `m` のときに担ぐ条件。 -/
def Inv (T : Tower) (m q1 q2 : Nat) : Prop :=
  (∃ t, (frameAt T (m+1)).parent q2 = some t ∧ t < q1) ∧ q1 < q2 ∧
    (frameAt T (m+2)).parent q1 ≠ none

/-- 不変量から、その層で `q1` の値が正であることが出る。 -/
theorem inv_pos (T : Tower) {m q1 q2 : Nat} (h : Inv T m q1 q2) :
    0 < towerVal T m q1 :=
  frame_live_pos T m q1 (frame_live_down T m q1 h.2.2)

/-- 兄弟なら不変量が一段下へ移る。 -/
theorem inv_descend (T : Tower) {m t q1 q2 : Nat}
    (h : Inv T (m+1) q1 q2)
    (h1 : (frameAt T (m+1)).parent q1 = some t)
    (h2 : (frameAt T (m+1)).parent q2 = some t) : Inv T m q1 q2 :=
  ⟨⟨t, h2, (frameAt T (m+1)).parent_left h1⟩, h.2.1, frame_live_down T (m+1) q1 h.2.2⟩

/-! ## `Inv` はまだ実際の配置より弱い

`Inv` は結論を含意し、降下でも保たれる（実測で確認済み）。しかし 3 択は尽きない。
値 12 まで 271,452 列・191,959 件の内訳は

```
祖先 189,600   兄弟 1,775   どちらでもない 584
```

である。「`q1` は `t` の次に生きている列」という条件を足しても 556 件残り、
そのうち 501 件は合流点で `u < q1` となって閉じない。反例の形は
列 `(1,1,2,4,8,4)` の層 1 で `t = 2`、`q1 = 4`、`q2 = 5`、合流点 `2`、`u = 3`。

一方、実際の配置（`q1 = j` が歩行で到達した根の次に生きている列、
`q2 = e` が根の `F` 子で `p` の鎖にある列）では、合流点は 69,364 件中 5 件だけで
いずれも `u = q1` であった。つまり `Inv` は実際の配置より弱く、余計な組を拾う。

したがって不変量をさらに絞る必要がある。降下で何が保たれるかを見極めるのが次の課題。

## この道は使わなかった

`SibSucc.lean` で別の道から閉じた。`e` を一段下がる**前に** `root` の子まで
引き上げると、主張の形が層をまたいで変わらず、3 択に分かれない。本ファイルの
`frameAt` / `towerVal` / `frameAt_step` / `tower_case_descent` はそちらでも使うが、
`Resolves` と `Inv` は使っていない。潰した予想の記録として残す。 -/

end Yukito
