import Equiv.Sparse
import Equiv.RowSucc

/-!
# 疎配列が密表現を表していること

JS の行と Phyrion 版の行の対応を、次の 4 条件で書く。

```
mono   position は狭義単調増加
val    セルの値は密表現の値
live   セルの値は正
cover  生きている列はすべてセルとして現れる
```

これがあれば、疎配列を列番号で引いた値は密表現の値にそのまま一致する
（`rep_read`）。列 `r` 未満については、JS 側は `position ≥ 0` なのでセルが無く 0、
密表現側も 0 である（`rows_value_zero_of_lt`）。

`assignParents` は `par` しか書き換えないので、この 4 条件を保つ。
-/

namespace Yukito

open OneY.Numeric

/-! ## 密表現側：行 `r` では列 `r` 未満は死んでいる -/

/-- 行 `r` では列 `r` 未満の値は 0。列 `c` が行 `r+1` で生きるにはその親が行 `r` で
生きていなければならず、親は左にあるから、生きた列は 1 行ごとに右へ 1 つ以上ずれる。 -/
theorem rows_value_zero_of_lt (base : Row) :
    ∀ r c, c < r → (rows base r).value c = 0 := by
  intro r
  induction r with
  | zero => intro c h; exact absurd h (Nat.not_lt_zero c)
  | succ r ih =>
      intro c hc
      show (rows base r).difference c = 0
      cases hp : (rows base r).forest.parent c with
      | none => simp only [Row.difference, hp]
      | some p =>
          exfalso
          have hpv := ((rows base r).parent_values hp).1
          have hlt := (rows base r).forest.parent_left hp
          rw [ih p (by omega)] at hpv
          omega

/-! ## 表現述語 -/

/-- 疎配列 `row` が、行のずれ `r`・列の上限 `n` のもとで密な値 `V` を表している。

上限が要るのは、`ofSequence` が列 `n` 以降を値 1 で埋めるからである。埋めた列は
値 1 なので親を持てず（親には真に小さい正の値が要る）、他の列の親にもならない。
行 1 以降では死んでいるので、上限が効くのは行 0 だけである。 -/
structure Rep (row : Rowj) (r n : Nat) (V : Nat → Nat) : Prop where
  mono : PosMono row
  val : ∀ i, ∀ hi : i < row.size, (row[i]'hi).val = V ((row[i]'hi).pos + r)
  live : ∀ i, ∀ hi : i < row.size, 0 < (row[i]'hi).val
  bound : ∀ i, ∀ hi : i < row.size, (row[i]'hi).pos + r < n
  cover : ∀ c, r ≤ c → c < n → 0 < V c →
    ∃ i, ∃ hi : i < row.size, (row[i]'hi).pos + r = c

/-- 疎配列を列番号で引く。JS の `while (row[j].position < c - r) j++` と、
その後の「ちょうどか」の判定にあたる。 -/
def readVal (row : Rowj) (r c : Nat) : Nat :=
  let j := firstAtLeast row (c - r)
  if h : j < row.size then
    if (row[j]'h).pos + r = c then (row[j]'h).val else 0
  else 0

/-- **読み替えの正しさ。** `Rep` があれば、疎配列を列番号で引いた値は
密表現の値に一致する。 -/
theorem rep_read (row : Rowj) (r n : Nat) (V : Nat → Nat) (h : Rep row r n V)
    (hzero : ∀ c, c < r → V c = 0) (c : Nat) (hcn : c < n) :
    readVal row r c = V c := by
  show (if hj : firstAtLeast row (c - r) < row.size then
          if (row[firstAtLeast row (c - r)]'hj).pos + r = c then
            (row[firstAtLeast row (c - r)]'hj).val else 0
        else 0) = V c
  rcases Nat.lt_or_ge c r with hcr | hrc
  · -- 列 `r` 未満：セルは無く、密表現も 0
    rw [hzero c hcr]
    split
    · rename_i hj
      split
      · rename_i he
        exfalso
        have := (row[firstAtLeast row (c - r)]'hj).pos
        omega
      · rfl
    · rfl
  · rcases Nat.eq_zero_or_pos (V c) with hv | hv
    · -- 死んだ列：ちょうどのセルがあれば `live` に反する
      rw [hv]
      split
      · rename_i hj
        split
        · rename_i he
          have h1 := h.val _ hj
          have h2 := h.live _ hj
          rw [he] at h1
          omega
        · rfl
      · rfl
    · -- 生きた列：`cover` のセルを `firstAtLeast` が指す
      obtain ⟨i, hi, hci⟩ := h.cover c hrc hcn hv
      have hpi : (row[i]'hi).pos = c - r := by omega
      have hfa : firstAtLeast row (c - r) = i :=
        firstAtLeast_eq_of_mem row h.mono (c - r) i hi hpi
      simp only [hfa, dif_pos hi, if_pos hci]
      rw [h.val i hi, hci]

/-! ## `assignParents` は表現を保つ

`par` しか書き換えないので、`pos` と `val` はそのままである。 -/

theorem assignParents_size (prev : Option Rowj) (row : Rowj) :
    (assignParents prev row).size = row.size := Array.size_mapIdx

theorem assignParents_pos (prev : Option Rowj) (row : Rowj) (i : Nat)
    (hi : i < (assignParents prev row).size) (hi' : i < row.size) :
    ((assignParents prev row)[i]'hi).pos = (row[i]'hi').pos := by
  simp only [assignParents, Array.getElem_mapIdx]
  cases prev <;> rfl

theorem assignParents_val (prev : Option Rowj) (row : Rowj) (i : Nat)
    (hi : i < (assignParents prev row).size) (hi' : i < row.size) :
    ((assignParents prev row)[i]'hi).val = (row[i]'hi').val := by
  simp only [assignParents, Array.getElem_mapIdx]
  cases prev <;> rfl

theorem rep_assignParents (prev : Option Rowj) (row : Rowj) (r n : Nat) (V : Nat → Nat)
    (h : Rep row r n V) : Rep (assignParents prev row) r n V := by
  have hsize := assignParents_size prev row
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j hi hj hij
    rw [assignParents_pos prev row i hi (by omega),
      assignParents_pos prev row j hj (by omega)]
    exact h.mono i j (by omega) (by omega) hij
  · intro i hi
    rw [assignParents_val prev row i hi (by omega),
      assignParents_pos prev row i hi (by omega)]
    exact h.val i (by omega)
  · intro i hi
    rw [assignParents_val prev row i hi (by omega)]
    exact h.live i (by omega)
  · intro i hi
    rw [assignParents_pos prev row i hi (by omega)]
    exact h.bound i (by omega)
  · intro c hrc hcn hv
    obtain ⟨i, hi, hci⟩ := h.cover c hrc hcn hv
    refine ⟨i, by omega, ?_⟩
    rw [assignParents_pos prev row i (by omega) hi]
    exact hci

/-! ## 行 0 -/

theorem row0_size (s : List Nat) : (row0 s).size = s.length := by
  simp only [row0, Array.size_mapIdx, List.size_toArray]

/-- 行 0 は入力列そのものを表す。 -/
theorem rep_row0 (s : List Nat) (hs : ∀ x ∈ s, 0 < x) :
    Rep (row0 s) 0 s.length (ofSequence s).value := by
  have hsize := row0_size s
  have hget : ∀ i, ∀ hi : i < (row0 s).size,
      (row0 s)[i]'hi = { pos := i, val := s[i]'(by omega), par := none } := by
    intro i hi
    simp only [row0, Array.getElem_mapIdx, List.getElem_toArray]
  have hval : ∀ i, ∀ h : i < s.length, (ofSequence s).value i = s[i]'h := by
    intro i h
    show s[i]?.getD 1 = _
    rw [List.getElem?_eq_getElem h]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j hi hj hij
    rw [hget i hi, hget j hj]
    exact hij
  · intro i hi
    rw [hget i hi]
    show s[i]'(by omega) = (ofSequence s).value (i + 0)
    rw [Nat.add_zero, hval i (by omega)]
  · intro i hi
    rw [hget i hi]
    exact hs _ (List.getElem_mem _)
  · intro i hi
    rw [hget i hi]
    show i + 0 < s.length
    omega
  · intro c _ hcn _
    refine ⟨c, by omega, ?_⟩
    rw [hget c (by omega)]
    show c + 0 = c
    omega

end Yukito
