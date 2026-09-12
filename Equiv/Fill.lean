import Equiv.Fuji

/-!
# 値の埋めの構造

`fillRow` は各セルについて 1 つずつ積む折り畳みである。積む値は「それまでに積んだ
配列」を見て決まるが、既に積んだ要素は変わらないので、最終形の前半部分と一致する。
本ファイルはその形を取り出す。
-/

namespace Yukito

/-! ## 1 つずつ積む折り畳み -/

/-- 直前までの結果を見ながら 1 つずつ積む折り畳み。 -/
def pushFold {α β : Type} (g : Array β → α → β) : Array β → List α → Array β
  | acc, [] => acc
  | acc, x :: t => pushFold g (acc.push (g acc x)) t

theorem pushFold_eq {α β : Type} (g : Array β → α → β) :
    ∀ (l : List α) (acc : Array β),
      pushFold g acc l = l.foldl (fun a x => a.push (g a x)) acc := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons x t ih => intro acc; simp only [pushFold, List.foldl_cons, ih]

theorem pushFold_append {α β : Type} (g : Array β → α → β) :
    ∀ (l₁ l₂ : List α) (acc : Array β),
      pushFold g acc (l₁ ++ l₂) = pushFold g (pushFold g acc l₁) l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ acc; rfl
  | cons x t ih => intro l₂ acc; simp only [List.cons_append, pushFold, ih]

/-- 大きさは積んだ個数だけ増える。 -/
theorem pushFold_size {α β : Type} (g : Array β → α → β) :
    ∀ (l : List α) (acc : Array β), (pushFold g acc l).size = acc.size + l.length := by
  intro l
  induction l with
  | nil => intro acc; simp [pushFold]
  | cons x t ih =>
      intro acc
      simp only [pushFold, ih, Array.size_push, List.length_cons]
      omega

/-- 既に積んだ要素は後から変わらない。 -/
theorem pushFold_prefix {α β : Type} (g : Array β → α → β) :
    ∀ (l : List α) (acc : Array β) (j : Nat), j < acc.size →
      (pushFold g acc l)[j]? = acc[j]? := by
  intro l
  induction l with
  | nil => intro acc j _; rfl
  | cons x t ih =>
      intro acc j hj
      have hj' : j < (acc.push (g acc x)).size := by rw [Array.size_push]; omega
      rw [pushFold, ih (acc.push (g acc x)) j hj', Array.getElem?_push]
      rw [if_neg (by omega)]

/-- **積んだ `i` 番目は、`i` 個目までを積んだ時点の配列から決まる。** -/
theorem pushFold_get {α β : Type} (g : Array β → α → β) :
    ∀ (l : List α) (acc : Array β) (i : Nat),
      (pushFold g acc l)[acc.size + i]? = (l[i]?).map (g (pushFold g acc (l.take i))) := by
  intro l
  induction l with
  | nil =>
      intro acc i
      rw [pushFold, Array.getElem?_eq_none (by omega)]
      simp
  | cons x t ih =>
      intro acc i
      match i with
      | 0 =>
          have hlt : acc.size < (acc.push (g acc x)).size := by rw [Array.size_push]; omega
          rw [Nat.add_zero, pushFold, pushFold_prefix g t (acc.push (g acc x)) acc.size hlt,
            Array.getElem?_push, if_pos rfl]
          simp only [List.take_zero, pushFold, List.getElem?_cons_zero, Option.map_some]
      | j + 1 =>
          have hsz : (acc.push (g acc x)).size = acc.size + 1 := by rw [Array.size_push]
          have : acc.size + (j + 1) = (acc.push (g acc x)).size + j := by omega
          rw [pushFold, this, ih (acc.push (g acc x)) j]
          simp only [List.getElem?_cons_succ, List.take_succ_cons, pushFold]

theorem pushFold_get_nil {α β : Type} (g : Array β → α → β) (l : List α) (i : Nat) :
    (pushFold g #[] l)[i]? = (l[i]?).map (g (pushFold g #[] (l.take i))) := by
  have h := pushFold_get g l #[] i
  simpa using h

/-! ## `fillRow` -/

/-- `fillRow` が 1 セルについて積む値。 -/
def fillG (up : Rowj) (acc : Rowj) (c : Cell) : Cell :=
  if c.val ≠ 0 then c
  else { c with val := (match c.par with
                        | none => 0
                        | some p => valAtIdx acc p) + readValAt up (c.pos - 1) }

theorem fillRow_eq (row up : Rowj) : fillRow row up = pushFold (fillG up) #[] row.toList := by
  rw [pushFold_eq, Array.foldl_toList]
  rfl

/-- `fillG` の値の決まり方。 -/
theorem fillG_val (up acc : Rowj) (c : Cell) :
    (fillG up acc c).val
      = if c.val ≠ 0 then c.val
        else (match c.par with
              | none => 0
              | some p => valAtIdx acc p) + readValAt up (c.pos - 1) := by
  unfold fillG
  split
  · rfl
  · rfl

theorem fillRow_size (row up : Rowj) : (fillRow row up).size = row.size := by
  rw [fillRow_eq, pushFold_size]
  simp

theorem valAtIdx_eq (row : Rowj) (i : Nat) :
    valAtIdx row i = match row[i]? with | none => 0 | some c => c.val := by
  unfold valAtIdx
  split
  · next h => rw [Array.getElem?_eq_getElem h]
  · next h => rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)]

/-- `fillRow` の `i` 番目のセルは、`i` 個目までを埋めた配列から決まる。 -/
theorem fillRow_get (row up : Rowj) (i : Nat) (hi : i < row.size) :
    (fillRow row up)[i]?
      = some (fillG up (pushFold (fillG up) #[] (row.toList.take i)) (row[i]'hi)) := by
  rw [fillRow_eq, pushFold_get_nil]
  have hlen : i < row.toList.length := by simpa using hi
  rw [List.getElem?_eq_getElem hlen]
  simp

/-- 参照する親が自分より前にあるとき、`fillRow` の値は最終形の中で閉じている。 -/
theorem fillRow_prefix_val (row up : Rowj) (i p : Nat) (hi : i ≤ row.size) (hp : p < i) :
    valAtIdx (pushFold (fillG up) #[] (row.toList.take i)) p = valAtIdx (fillRow row up) p := by
  have hsz : (pushFold (fillG up) #[] (row.toList.take i)).size = i := by
    rw [pushFold_size]
    simp only [Array.size_empty, List.length_take, Array.length_toList, Nat.zero_add]
    omega
  have key : pushFold (fillG up) #[] row.toList
      = pushFold (fillG up) (pushFold (fillG up) #[] (row.toList.take i)) (row.toList.drop i) := by
    rw [← pushFold_append, List.take_append_drop]
  rw [valAtIdx_eq, valAtIdx_eq, fillRow_eq, key,
    pushFold_prefix (fillG up) (row.toList.drop i)
      (pushFold (fillG up) #[] (row.toList.take i)) p (by omega)]

/-- **`fillRow` の値の決まり方。** 値が 0 でないセルはそのまま、0 のセルは
「同じ行の親の値 + 上の行の 1 つ左の列の値」になる。 -/
theorem fillRow_val (row up : Rowj)
    (hpar : ∀ (i : Nat) (h : i < row.size) (p : Nat), (row[i]'h).par = some p → p < i)
    (i : Nat) (hi : i < row.size) :
    valAtIdx (fillRow row up) i
      = if (row[i]'hi).val ≠ 0 then (row[i]'hi).val
        else (match (row[i]'hi).par with
              | none => 0
              | some p => valAtIdx (fillRow row up) p) + readValAt up ((row[i]'hi).pos - 1) := by
  rw [valAtIdx_eq, fillRow_get row up i hi]
  dsimp only
  rw [fillG_val]
  split
  · rfl
  · cases hcp : (row[i]'hi).par with
    | none => rfl
    | some p =>
        dsimp only
        rw [fillRow_prefix_val row up i p (Nat.le_of_lt hi) (hpar i hi p hcp)]

/-- `pos` は埋めても変わらない。 -/
theorem fillRow_pos (row up : Rowj) (i : Nat) (hi : i < row.size)
    (hi' : i < (fillRow row up).size) : ((fillRow row up)[i]'hi').pos = (row[i]'hi).pos := by
  have := fillRow_get row up i hi
  rw [Array.getElem?_eq_getElem hi'] at this
  have h2 := Option.some.inj this
  rw [h2]
  unfold fillG
  split
  · rfl
  · rfl

/-- `par` は埋めても変わらない。 -/
theorem fillRow_par (row up : Rowj) (i : Nat) (hi : i < row.size)
    (hi' : i < (fillRow row up).size) : ((fillRow row up)[i]'hi').par = (row[i]'hi).par := by
  have := fillRow_get row up i hi
  rw [Array.getElem?_eq_getElem hi'] at this
  have h2 := Option.some.inj this
  rw [h2]
  unfold fillG
  split
  · rfl
  · rfl

end Yukito
