import Equiv.Yukito

/-!
# 疎配列の走査

JS は行を「生きたセルだけを `position` 昇順に並べた配列」で持つ。列番号で引くには
`while (row[j].position < target) j++` で走査する。本ファイルはこの走査
（`scanFrom` / `firstAtLeast`）の性質を証明する。

要点は 3 つである。

```
firstAtLeast_before  それより手前のセルは position が target 未満
firstAtLeast_at      止まった所のセルは position が target 以上
firstAtLeast_eq_of_mem  position がちょうど target のセルがあれば、そこで止まる
```

3 つ目が「疎配列を列番号で引く」の正しさである。逆に、ちょうどのセルが無いと
`firstAtLeast` は**右隣のセルを指す**。これが山の段で唯一の食い違いになる箇所で、
`Mountain.lean` の `firstLiveNotSmaller_ofSequence` がそこを埋める。
-/

namespace Yukito

/-- 位置が狭義単調増加であること。JS の行はつねにこの形をしている。 -/
def PosMono (row : Rowj) : Prop :=
  ∀ i j, (hi : i < row.size) → (hj : j < row.size) → i < j →
    (row[i]'hi).pos < (row[j]'hj).pos

/-- 走査は始点以上の添字を返す。 -/
theorem scanFrom_ge (row : Rowj) (target j : Nat) : j ≤ scanFrom row target j := by
  induction j using scanFrom.induct row target with
  | case1 j h hlt ih =>
      rw [scanFrom.eq_def row target j, dif_pos h, if_pos hlt]
      omega
  | case2 j h hge =>
      rw [scanFrom.eq_def row target j, dif_pos h, if_neg hge]
      exact Nat.le_refl _
  | case3 j h =>
      rw [scanFrom.eq_def row target j, dif_neg h]
      exact Nat.le_refl _

/-- 走査は配列の外へは出ない。 -/
theorem scanFrom_le (row : Rowj) (target : Nat) :
    ∀ j, j ≤ row.size → scanFrom row target j ≤ row.size := by
  intro j
  induction j using scanFrom.induct row target with
  | case1 j h hlt ih =>
      intro _
      rw [scanFrom.eq_def row target j, dif_pos h, if_pos hlt]
      exact ih h
  | case2 j h hge =>
      intro hj
      rw [scanFrom.eq_def row target j, dif_pos h, if_neg hge]
      exact hj
  | case3 j h =>
      intro hj
      rw [scanFrom.eq_def row target j, dif_neg h]
      exact hj

/-- 止まる手前のセルは `position` が `target` 未満。 -/
theorem scanFrom_before (row : Rowj) (target : Nat) :
    ∀ j i, ∀ hi : i < row.size, j ≤ i → i < scanFrom row target j →
      (row[i]'hi).pos < target := by
  intro j
  induction j using scanFrom.induct row target with
  | case1 j h hlt ih =>
      intro i hi hji hlt2
      rw [scanFrom.eq_def row target j, dif_pos h, if_pos hlt] at hlt2
      rcases Nat.eq_or_lt_of_le hji with heq | hgt
      · subst heq; exact hlt
      · exact ih i hi hgt hlt2
  | case2 j h hge =>
      intro i hi hji hlt2
      rw [scanFrom.eq_def row target j, dif_pos h, if_neg hge] at hlt2
      omega
  | case3 j h =>
      intro i hi hji hlt2
      rw [scanFrom.eq_def row target j, dif_neg h] at hlt2
      omega

/-- 止まった所のセルは `position` が `target` 以上。 -/
theorem scanFrom_at (row : Rowj) (target : Nat) :
    ∀ j k, ∀ hk : k < row.size, scanFrom row target j = k →
      target ≤ (row[k]'hk).pos := by
  intro j
  induction j using scanFrom.induct row target with
  | case1 j h hlt ih =>
      intro k hk he
      rw [scanFrom.eq_def row target j, dif_pos h, if_pos hlt] at he
      exact ih k hk he
  | case2 j h hge =>
      intro k hk he
      rw [scanFrom.eq_def row target j, dif_pos h, if_neg hge] at he
      subst he
      omega
  | case3 j h =>
      intro k hk he
      rw [scanFrom.eq_def row target j, dif_neg h] at he
      omega

theorem firstAtLeast_le (row : Rowj) (target : Nat) :
    firstAtLeast row target ≤ row.size :=
  scanFrom_le row target 0 (Nat.zero_le _)

theorem firstAtLeast_before (row : Rowj) (target i : Nat) (hi : i < row.size)
    (h : i < firstAtLeast row target) : (row[i]'hi).pos < target :=
  scanFrom_before row target 0 i hi (Nat.zero_le _) h

theorem firstAtLeast_at (row : Rowj) (target k : Nat) (hk : k < row.size)
    (h : firstAtLeast row target = k) : target ≤ (row[k]'hk).pos :=
  scanFrom_at row target 0 k hk h

/-- **疎配列を列番号で引く。** 位置が狭義単調で、`position` がちょうど `target` の
セルがあれば、`firstAtLeast` はそのセルを指す。 -/
theorem firstAtLeast_eq_of_mem (row : Rowj) (hmono : PosMono row) (target m : Nat)
    (hm : m < row.size) (hpos : (row[m]'hm).pos = target) :
    firstAtLeast row target = m := by
  have hkm : firstAtLeast row target ≤ m := by
    rcases Nat.lt_or_ge m (firstAtLeast row target) with hlt | hge
    · have := firstAtLeast_before row target m hm hlt
      omega
    · exact hge
  have hk : firstAtLeast row target < row.size := by omega
  have hge := firstAtLeast_at row target _ hk rfl
  rcases Nat.eq_or_lt_of_le hkm with heq | hlt
  · exact heq
  · have := hmono _ m hk hm hlt
    omega

/-- ちょうどのセルが無いときは、`firstAtLeast` が指すセルは `target` より右にある。 -/
theorem firstAtLeast_gt_of_not_mem (row : Rowj) (target k : Nat)
    (hk : k < row.size) (h : firstAtLeast row target = k)
    (hne : (row[k]'hk).pos ≠ target) : target < (row[k]'hk).pos := by
  have := firstAtLeast_at row target k hk h
  omega

end Yukito
