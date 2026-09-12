import Equiv.Yukito

/-!
# Yukito 版の山と Phyrion 版 `OneY.Numeric.rows` の対応

JS は疎配列（生きているセルだけを `position` 昇順に並べる）、Lean は密表現
（値 0 が不在）である。座標は

```
JS の (行 r, position P)  ↔  Lean の (行 r, 列 c = P + r)
```

で対応する。本ファイルはこの対応を述べ、有限族でカーネル検査する。
-/

namespace Yukito

open OneY.Numeric

/-- JS の行 `r` を密表現で読む。列 `c` に生きたセルが無ければ 0。 -/
def valAt (rows : List Rowj) (r c : Nat) : Nat :=
  match rows[r]? with
  | none => 0
  | some row =>
    match row.find? (fun x => x.pos + r == c) with
    | some x => x.val
    | none => 0

/-- JS の行 `r` の列 `c` の親を、配列添字ではなく列番号で読む。 -/
def parAt (rows : List Rowj) (r c : Nat) : Option Nat :=
  match rows[r]? with
  | none => none
  | some row =>
    match row.find? (fun x => x.pos + r == c) with
    | none => none
    | some x =>
      match x.par with
      | none => none
      | some p => if h : p < row.size then some (row[p].pos + r) else none

/-- Phyrion 版の値。 -/
def leanVal (s : List Nat) (r c : Nat) : Nat :=
  (rows (ofSequence s) r).value c

/-- Phyrion 版の親。 -/
def leanPar (s : List Nat) (r c : Nat) : Option Nat :=
  (rows (ofSequence s) r).forest.parent c

end Yukito
