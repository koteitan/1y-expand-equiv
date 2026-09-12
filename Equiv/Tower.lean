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

end Yukito
