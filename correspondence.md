[← 戻る](README.md)

# `script.js` と `Equiv/Yukito.lean` の対応

`Equiv/Yukito.lean` は [Naruyoko/YNySequence](https://github.com/Naruyoko/YNySequence) の
`script.js` を Lean に写したものである。原本と写しを並べて置く。

引用は次のスナップショットのものである。

```
Naruyoko/YNySequence  コミット 2de1397  script.js  477 行
```

JS 側の引用は、ブロック全体の字下げを詰めた以外そのままである。Lean 側の引用は
docstring を省いた以外そのままである。長い共通部分を省いたところは `…` と書き、
省いた本文は別に引用する。

| `script.js` | `Equiv/Yukito.lean` |
|---|---|
| 15–31 `parseSequenceElement` | `row0` / `clampPar` / `parseDiag` |
| 32–86 `calcMountain` | `calcMountain` / `calcMountainFrom` / `mountainGo` / `assignParents` |
| 87–145 `calcDiagonal` | `calcDiagonal` / `diagList` / `legWalkJS` |
| 146–161 `cloneMountain` | 写していない（不変な値なので複製が要らない） |
| 162–174 `getBadRoot` | `getBadRoot` |
| 175–403 `expand` | `expandJS` / `expandOut` |

## セルと行

```js
// script.js 18-22
return {
  value:numval,
  position:i,
  parentIndex:-1
};
```

```lean
-- Yukito.lean 25-33
structure Cell where
  pos : Nat
  val : Nat
  par : Option Nat
  forced : Bool := false
  deriving Repr, DecidableEq

abbrev Rowj := Array Cell
```

`parentIndex = -1` が `par = none`、`forcedParent` が `forced` である。JS の
`lastLayer` は `position` 昇順の疎配列で、これが `Rowj` にあたる。

段を取り出すところ。JS は範囲内しか触らない。

```js
// script.js 249（段 seamHeight を取り出すところ）
while (mountain[seamHeight][l]&&mountain[seamHeight][l].position+seamHeight<j) l++;
```

```lean
-- Yukito.lean 143
def rowAt (M : List Rowj) (h : Nat) : Rowj := M.getD h #[]
```

位置の走査は JS の随所に出る。

```js
// script.js 53
while (calculatedMountain[calculatedMountain.length-2][p].position<lastLayer[i].position+1) p++;
// script.js 65
while (lastLayer[j].position<calculatedMountain[calculatedMountain.length-2][p].position-1) j++;
// script.js 266
while (mountain[sy][sx].position+sy<j) sx++;
```

```lean
-- Yukito.lean 38-46
def scanFrom (row : Rowj) (target : Nat) (j : Nat) : Nat :=
  if h : j < row.size then
    if row[j].pos < target then scanFrom row target (j+1) else j
  else j
termination_by row.size - j
decreasing_by simp_wf; omega

def firstAtLeast (row : Rowj) (target : Nat) : Nat := scanFrom row target 0
```

走り切ったら `row.size` を返す。JS で `lastLayer[j]` が `undefined` になる位置である。
完全一致で引くところは次を使う。

```js
// script.js 104-106
var m=0; //find up-left of that=left
while (mountain[height][m].position<mountain[height-1][l].position-1) m++;
if (mountain[height][m].position==mountain[height-1][l].position-1){ //left exists
```

```lean
-- Yukito.lean 157-159
def lookupPos (row : Rowj) (t : Nat) : Option Nat :=
  let m := firstAtLeast row t
  if hm : m < row.size then (if (row[m]'hm).pos = t then some m else none) else none
```

## `parseSequenceElement`

```js
// script.js 15-31
function parseSequenceElement(s,i){
  if (s.indexOf("v")==-1||!isFinite(Number(s.substring(s.indexOf("v")+1)))){
    var numval=Number(s);
    return {
      value:numval,
      position:i,
      parentIndex:-1
    };
  }else{
    return {
      value:Number(s.substring(0,s.indexOf("v"))),
      position:i,
      parentIndex:Math.max(Math.min(i-1,Number(s.substring(s.indexOf("v")+1))),-1),
      forcedParent:true
    };
  }
}
```

素の数の枝（16–22）が `row0`。

```lean
-- Yukito.lean 111-112
def row0 (s : List Nat) : Rowj :=
  (s.toArray.mapIdx fun i v => { pos := i, val := v, par := none })
```

`"値v親"` の枝（23–30）が `parseDiag`。`Math.max(Math.min(i-1,p),-1)` が `clampPar`。

```lean
-- Yukito.lean 254-264
def clampPar (i : Nat) (p : Option Nat) : Option Nat :=
  match i, p with
  | 0, _ => none
  | _+1, none => none
  | i'+1, some q => some (min i' q)

def parseDiag (l : List DiagItem) : Rowj :=
  l.toArray.mapIdx fun i x =>
    { pos := i, val := x.val,
      par := if x.forced then clampPar i x.par else none, forced := x.forced }
```

文字列の解析そのものは写していない。`calcDiagonal` の出力を文字列にせず
`List DiagItem` のまま `parseDiag` に渡す。

## `calcMountain`

### 入口

```js
// script.js 32-39
function calcMountain(s){
  //if (!/^(\d+,)*\d+$/.test(s)) throw Error("BAD");
  var lastLayer;
  if (typeof s=="string"){
    lastLayer=s.split(itemSeparatorRegex).map(parseSequenceElement);
  }
  else lastLayer=s;
  var calculatedMountain=[lastLayer]; //rows
```

```lean
-- Yukito.lean 124-130
def calcMountainFrom (base : Rowj) : Nat → List Rowj
  | 0 => []
  | fuel+1 => mountainGo (assignParents none base) fuel

def calcMountain (s : List Nat) (fuel : Nat) : List Rowj :=
  calcMountainFrom (row0 s) fuel
```

JS は文字列でも行の配列でも受け取る。Lean は行から始める `calcMountainFrom` と、
素の数列から始める `calcMountain` に分けた。

### 層のループ

```js
// script.js 40-47, 74-85
while (true){
  //assign parents
  var hasNextLayer=false;
  for (var i=0;i<lastLayer.length;i++){
    if (lastLayer[i].forcedParent){
      if (lastLayer[i].parentIndex!=-1) hasNextLayer=true;
      continue;
    }
    …親の探索…
  }
  if (!hasNextLayer) break;
  var currentLayer=[];
  calculatedMountain.push(currentLayer);
  for (var i=0;i<lastLayer.length;i++){
    if (lastLayer[i].parentIndex!=-1){
      currentLayer.push({value:lastLayer[i].value-lastLayer[lastLayer[i].parentIndex].value,position:lastLayer[i].position-1,parentIndex:-1});
    }
  }
  lastLayer=currentLayer;
}
return calculatedMountain;
```

```lean
-- Yukito.lean 116-120
def mountainGo (cur : Rowj) : Nat → List Rowj
  | 0 => [cur]
  | f+1 =>
    if cur.all (fun c => c.par.isNone) then [cur]
    else cur :: mountainGo (assignParents (some cur) (nextRow cur)) f
```

```lean
-- Yukito.lean 90-97
def nextRow (row : Rowj) : Rowj :=
  row.foldl (init := #[]) fun acc c =>
    match c.par with
    | none => acc
    | some p =>
      if hp : p < row.size then
        acc.push { pos := c.pos - 1, val := c.val - row[p].val, par := none }
      else acc
```

`hasNextLayer` は JS では親の割り当てと同時に立てるフラグだが、Lean では
割り当て後の行を見て `cur.all (fun c => c.par.isNone)` で判定する。同じ条件である。
`while (true)` は止まらないので `fuel` を付けた。

### 親の割り当て

```js
// script.js 43-54
for (var i=0;i<lastLayer.length;i++){
  if (lastLayer[i].forcedParent){
    if (lastLayer[i].parentIndex!=-1) hasNextLayer=true;
    continue;
  }
  var p;
  if (calculatedMountain.length==1){
    p=lastLayer[i].position+1;
  }else{
    p=0;
    while (calculatedMountain[calculatedMountain.length-2][p].position<lastLayer[i].position+1) p++;
  }
```

```lean
-- Yukito.lean 101-108
def assignParents (prev : Option Rowj) (row : Rowj) : Rowj :=
  row.mapIdx fun i c =>
    if c.forced then c
    else
      match prev with
      | none     => { c with par := searchBase row i c.pos }
      | some pv  => { c with par := searchUpper pv row i (pv.size + 1)
                               (some (firstAtLeast pv (c.pos + 1))) }
```

`calculatedMountain.length==1`（＝行 0）が `prev = none` にあたる。

### 親の探索ループ

```js
// script.js 55-73
while (true){
  if (p<0) break;
  var j;
  if (calculatedMountain.length==1){
    p--;
    j=p-1;
  }else{ //ignoring
    p=calculatedMountain[calculatedMountain.length-2][p].parentIndex;
    if (p<0) break;
    j=0;
    while (lastLayer[j].position<calculatedMountain[calculatedMountain.length-2][p].position-1) j++;
  }
  if (j<0||j<lastLayer.length-1&&lastLayer[j].position+1!=lastLayer[j+1].position) break;
  if (lastLayer[j].value<lastLayer[i].value){
    lastLayer[i].parentIndex=j;
    hasNextLayer=true;
    break;
  }
}
```

行 0（58–60 の枝）は `p` を 1 つずつ減らして左へ走るだけなので、こうなる。

```lean
-- Yukito.lean 80-86
def searchBase (row : Rowj) (i : Nat) : Nat → Option Nat
  | 0 => none
  | j+1 => if hj : j < row.size then
             if hi : i < row.size then
               if row[j].val < row[i].val then some j else searchBase row i j
             else none
           else none
```

行 1 以上（61–66 の枝）は 1 つ下の行の親鎖を辿る。

```lean
-- Yukito.lean 58-77
def searchUpper (prev row : Rowj) (i : Nat) : Nat → Option Nat → Option Nat
  | 0, _ => none
  | _+1, none => none
  | fuel+1, some p =>
    if hp : p < prev.size then
      match prev[p].par with
      | none => none                            -- JS: `if (p<0) break;`
      | some p' =>
        if hp' : p' < prev.size then
          let target := prev[p'].pos - 1
          let j := firstAtLeast row target
          if breakHere row j then none
          else if hj : j < row.size then
            if hi : i < row.size then
              if row[j].val < row[i].val then some j
              else searchUpper prev row i fuel (some p')
            else none
          else none
        else none
    else none
```

`p=…[p].parentIndex; if (p<0) break;` が `match prev[p].par with | none => none`、
`while (lastLayer[j].position<…-1) j++` が `firstAtLeast row target`、
`lastLayer[i].parentIndex=j` が `some j`、ループの続行が再帰呼び出しである。

67 行の `break` の条件はこうなる。

```lean
-- Yukito.lean 51-54
def breakHere (row : Rowj) (j : Nat) : Bool :=
  if h : j < row.size then
    if h2 : j + 1 < row.size then row[j].pos + 1 ≠ row[j+1].pos else false
  else true
```

`j` は自然数なので `j<0` は「配列を走り切った」に読み替える。

## `calcDiagonal`

### 列ごとに最上段を探す

```js
// script.js 87-96
function calcDiagonal(mountain){
  var diagonal=[];
  var diagonalTree=[];
  for (var i=0;i<mountain[0].length;i++){ //only one diagonal exists for each left-side-up diagonal line
    for (var j=mountain.length-1;j>=0;j--){ //prioritize the top
      var k=0;
      while (mountain[j][k]&&mountain[j][k].position+j<i) k++;
      if (!mountain[j][k]||mountain[j][k].position+j!=i) continue;
      var height=j;
      var lastIndex=k;
```

```lean
-- Yukito.lean 146-153
def topAt (M : List Rowj) (i : Nat) : Nat → Option (Nat × Nat)
  | 0 => none
  | j+1 =>
    let row := rowAt M j
    let k := firstAtLeast row (i - j)
    if hk : k < row.size then
      if (row[k]'hk).pos + j = i then some (j, k) else topAt M i j
    else topAt M i j
```

```lean
-- Yukito.lean 207-218
def diagEntry (M : List Rowj) (i : Nat) : Option (Nat × Option Nat) :=
  match topAt M i M.length with
  | none => none
  | some (j, k) =>
    let row := rowAt M j
    if hk : k < row.size then
      some ((row[k]'hk).val, legWalkJS M (i + 1) j k)
    else none

def diagList (M : List Rowj) : List (Nat × Option Nat) :=
  (List.range (rowAt M 0).size).filterMap (diagEntry M)
```

JS の `for (j=mountain.length-1;j>=0;j--)` が `topAt` の下向きの再帰、
`for (i=0;i<mountain[0].length;i++)` が `List.range (rowAt M 0).size` である。

### 脚の歩行

```js
// script.js 97-118
while (true){
  if (height==0){
    lastIndex=mountain[height][lastIndex].parentIndex;
  }else{
    var l=0; //find right-down
    while (mountain[height-1][l].position!=mountain[height][lastIndex].position+1) l++;
    l=mountain[height-1][l].parentIndex; //go to its parent=left-down
    var m=0; //find up-left of that=left
    while (mountain[height][m].position<mountain[height-1][l].position-1) m++;
    if (mountain[height][m].position==mountain[height-1][l].position-1){ //left exists
      lastIndex=m;
    }else{
      height--;
      lastIndex=l;
    }
  }
  if (!mountain[height][lastIndex]||mountain[height][lastIndex].parentIndex==-1){
    diagonal.push(mountain[j][k].value);
    diagonalTree.push((mountain[height][lastIndex]?mountain[height][lastIndex].position:-1)+height);
    break;
  }
}
```

1 歩ぶんが `legStepJS`。状態は `(段, その段での添字)` である。

```lean
-- Yukito.lean 162-190
def legStepJS (M : List Rowj) (h idx : Nat) : Option (Nat × Nat) :=
  let row := rowAt M h
  if hi : idx < row.size then
    match h with
    | 0 =>
      match (row[idx]'hi).par with
      | none => none
      | some p => some (0, p)
    | h'+1 =>
      let below := rowAt M h'
      match lookupPos below ((row[idx]'hi).pos + 1) with
      | none => none
      | some l0 =>
        if hl0 : l0 < below.size then
          match (below[l0]'hl0).par with
          | none => none
          | some l =>
            if hl : l < below.size then
              -- JS の目標は `position - 1`。`position = 0` なら `-1` になり、
              -- どのセルにも一致しないので必ず段を下げる。自然数の切り捨て
              -- 引き算では `0` になってしまうので、ここだけ場合分けする。
              if (below[l]'hl).pos = 0 then some (h', l)
              else
                match lookupPos row ((below[l]'hl).pos - 1) with
                | some m => some (h' + 1, m)
                | none => some (h', l)
            else none
        else none
  else none
```

停止条件つきの反復が `legWalkJS`。着いた列 `position+height` を返す。

```lean
-- Yukito.lean 193-204
def legWalkJS (M : List Rowj) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel+1, h, idx =>
    match legStepJS M h idx with
    | none => none
    | some (h', idx') =>
      let row := rowAt M h'
      if hi : idx' < row.size then
        match (row[idx']'hi).par with
        | none => some ((row[idx']'hi).pos + h')
        | some _ => legWalkJS M fuel h' idx'
      else none
```

JS の `diagonalTree.push(…position:-1)+height)` の `-1` の側は `none` にあたる。

### 出力

```js
// script.js 122-144
var pw=[];
for (var i=0;i<diagonal.length;i++){
  var p=-1;
  for (var j=i-1;j>=0;j--){
    if (diagonal[j]<diagonal[i]){
      p=j;
      break;
    }
  }
  pw.push(p);
}
var r=[];
for (var i=0;i<diagonal.length;i++){
  var p=i;
  while (true){
    p=diagonalTree[p];
    if (p<0||diagonal[p]<diagonal[i]) break;
  }
  if (p==pw[i]) r.push(diagonal[i]);
  else r.push(diagonal[i]+"v"+p);
}
//console.log(diagonalTree);
return r.join(",");
```

```lean
-- Yukito.lean 221-232
def pwScan (d : List Nat) (target : Nat) : Nat → Option Nat
  | 0 => none
  | j+1 => if d.getD j 0 < target then some j else pwScan d target j

def treeScan (d : List Nat) (tree : List (Option Nat)) (target : Nat) :
    Nat → Nat → Option Nat
  | 0, _ => none
  | fuel+1, p =>
    match tree.getD p none with
    | none => none
    | some q => if d.getD q 0 < target then some q else treeScan d tree target fuel q
```

```lean
-- Yukito.lean 235-251
structure DiagItem where
  val : Nat
  forced : Bool
  par : Option Nat
  deriving Repr, DecidableEq

def calcDiagonal (M : List Rowj) : List DiagItem :=
  let e := diagList M
  let d := e.map Prod.fst
  let tree := e.map Prod.snd
  (List.range d.length).map fun i =>
    let target := d.getD i 0
    let p := treeScan d tree target (i + 1) i
    let w := pwScan d target i
    if p = w then { val := target, forced := false, par := none }
    else { val := target, forced := true, par := p }
```

`r.push(diagonal[i])` が `forced := false`、`r.push(diagonal[i]+"v"+p)` が
`forced := true` にあたる。`r.join(",")` は写していない。

## `getBadRoot`

```js
// script.js 162-174
function getBadRoot(s){
  var mountain;
  if (typeof s=="string") mountain=calcMountain(s);
  else mountain=cloneMountain(s);
  var diagonal=calcMountain(calcDiagonal(mountain));
  if (diagonal[0][diagonal[0].length-1].value!=1){
    return getBadRoot(diagonal);
  }else{
    for (var i=mountain.length-1;i>=0;i--){
      if (mountain[i][mountain[i].length-1].position+i==mountain[0].length-1) return mountain[i-1][mountain[i-1][mountain[i-1].length-1].parentIndex].position+i-1;
    }
  }
}
```

```lean
-- Yukito.lean 285-300
def getBadRoot (M : List Rowj) (mfuel : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    let d := calcMountainFrom (parseDiag (calcDiagonal M)) mfuel
    if lastVal (rowAt d 0) = 1 then
      match topRowOfLast M (rowAt M 0).size M.length with
      | none => none
      | some i =>
        let prev := rowAt M (i - 1)
        if hp : 0 < prev.size then
          match (prev[prev.size - 1]'(by omega)).par with
          | none => none
          | some p =>
            if hq : p < prev.size then some ((prev[p]'hq).pos + (i - 1)) else none
        else none
    else getBadRoot d mfuel fuel
```

`diagonal[0][diagonal[0].length-1].value` と、最後のセルの列を取るところ。

```lean
-- Yukito.lean 272-282
def lastCol (row : Rowj) (r : Nat) : Nat :=
  if h : 0 < row.size then (row[row.size - 1]'(by omega)).pos + r else 0

def lastVal (row : Rowj) : Nat :=
  if h : 0 < row.size then (row[row.size - 1]'(by omega)).val else 0

def topRowOfLast (M : List Rowj) (n : Nat) : Nat → Option Nat
  | 0 => none
  | i+1 => if lastCol (rowAt M i) i = n - 1 then some i else topRowOfLast M n i
```

`for (i=mountain.length-1;i>=0;i--)` の下向きの走査が `topRowOfLast`、
`mountain[i-1][…parentIndex].position+i-1` が最後の 2 行にあたる。

## `expand` の入口

```js
// script.js 175-191
function expand(s,n,stringify){
  var mountain;
  if (typeof s=="string") mountain=calcMountain(s);
  else mountain=cloneMountain(s);
  var result=cloneMountain(mountain);
  if (mountain[0][mountain[0].length-1].parentIndex==-1){
    result[0].pop();
  }else{
    var result=cloneMountain(mountain);
    var cutHeight=mountain.length-1;
    while (mountain[cutHeight][mountain[cutHeight].length-1].position+cutHeight!=mountain[0].length-1) cutHeight--;
    var actualCutHeight=cutHeight;
    var badRootSeam=getBadRoot(mountain);
    var badRootHeight;
    var diagonal=calcMountain(calcDiagonal(mountain));
    var newDiagonal;
    var yamakazi=diagonal[0][diagonal[0].length-1].value==1; //Yamakazi-Funka dualilty
```

```lean
-- Yukito.lean 578-599
def expandJS (nrep mfuel : Nat) : Nat → List Rowj → List Rowj
  | 0, _ => []
  | efuel + 1, M =>
    let row0 := rowAt M 0
    let n := row0.size
    let hasPar := if h : n - 1 < row0.size then ((row0[n - 1]'h).par).isSome else false
    if !hasPar then
      fillValues (dropEmptyTop (M.set 0 row0.pop))
    else
      let cutH := (topRowOfLast M n M.length).getD 0
      let seam := (getBadRoot M mfuel mfuel).getD 0
      let dg := calcMountainFrom (parseDiag (calcDiagonal M)) mfuel
      let yama := lastVal (rowAt dg 0) = 1
      let nd : Nat → Nat :=
        if yama then yamaVal (rowAt dg 0).pop seam (n - 1)
        else valAtIdx (rowAt (expandJS nrep mfuel efuel dg) 0)
      let cutH' := if yama then cutH - 1 else cutH
      let bh := if yama then cutH - 1 else (topRowWithCol M seam M.length).getD 0
      let res := cutChild M cutH
      let acl := (rowAt res 0).size
      let P : FujiParams := ⟨seam, bh, cutH', acl, yama⟩
      fillValues (dropEmptyTop (fujiIters M P nd res.length mfuel nrep res))
```

対応は上から順に、`mountain[0][…].parentIndex==-1` が `!hasPar`、
`result[0].pop()` が `M.set 0 row0.pop`、`cutHeight` の走査が `topRowOfLast`、
`badRootSeam=getBadRoot(mountain)` が `getBadRoot M mfuel mfuel`、
`diagonal=calcMountain(calcDiagonal(mountain))` が `dg`、`yamakazi` が `yama` である。

### `newDiagonal` の 2 つの枝

```js
// script.js 192-211
if (yamakazi){
  newDiagonal=cloneMountain(diagonal);
  newDiagonal[0].pop();
  for (var i=0;i<n;i++){
    for (var j=badRootSeam;j<mountain[0].length-1;j++){
      newDiagonal[0].push(newDiagonal[0][j]); //who cares about mountains in diagonal?
    }
  }
  cutHeight--;
  badRootHeight=cutHeight;
}else{
  newDiagonal=expand(diagonal,n,false);
  badRootHeight=mountain.length-1;
  while (true){
    var i=0;
    while (mountain[badRootHeight][i]&&mountain[badRootHeight][i].position+badRootHeight<badRootSeam) i++;
    if (mountain[badRootHeight][i]&&mountain[badRootHeight][i].position+badRootHeight==badRootSeam) break;
    badRootHeight--;
  }
}
```

山崎噴火の枝の `newDiagonal` は、最後を落として区間 `[badRootSeam, len)` を
周期的に積むだけなので、値の関数として持つ。

```lean
-- Yukito.lean 569-571
def yamaVal (base : Rowj) (seam len : Nat) (c : Nat) : Nat :=
  if c < len then valAtIdx base c
  else valAtIdx base (seam + (c - len) % (len - seam))
```

そうでない枝の `expand(diagonal,n,false)` が `expandJS nrep mfuel efuel dg` の
再帰、`badRootHeight` の走査が `topRowWithCol` である。

```lean
-- Yukito.lean 563-565
def topRowWithCol (M : List Rowj) (j : Nat) : Nat → Option Nat
  | 0 => none
  | i + 1 => if hasCol M i j then some i else topRowWithCol M j i
```

```lean
-- Yukito.lean 321-325
def hasCol (M : List Rowj) (r j : Nat) : Bool :=
  match lookupPos (rowAt M r) (j - r) with
  | none => false
  | some m =>
    if h : m < (rowAt M r).size then ((rowAt M r)[m]'h).pos + r == j else false
```

### 子を切る

```js
// script.js 212-224
for (var i=0;i<=actualCutHeight;i++) result[i].pop(); //cut child
if (!result[result.length-1].length) result.pop();
var afterCutHeight=result.length;
var afterCutMountain=cloneMountain(result);
var afterCutLength=result[0].length;
var badRootSeamHeight=afterCutHeight-1;
while (true){
  var l=0;
  while (mountain[badRootSeamHeight][l]&&mountain[badRootSeamHeight][l].position+badRootSeamHeight<badRootSeam) l++;
  if (mountain[badRootSeamHeight][l]&&mountain[badRootSeamHeight][l].position+badRootSeamHeight==badRootSeam) break;
  badRootSeamHeight--;
}
badRootSeamHeight++;
```

```lean
-- Yukito.lean 517-522
def cutChild (res : List Rowj) (cutH : Nat) : List Rowj :=
  let res := (List.range (cutH + 1)).foldl
    (fun r i => if i < r.length then r.set i ((r.getD i #[]).pop) else r) res
  if 0 < res.length ∧ (res.getD (res.length - 1) #[]).size = 0 then
    res.take (res.length - 1)
  else res
```

`afterCutHeight` が `res.length`、`afterCutLength` が `acl` である。
`afterCutMountain`（215）と `badRootSeamHeight`（217–224）は JS で計算されるが
その後どこでも読まれないので写していない。

JS が使う 5 つの定数はこうまとめた。

```lean
-- Yukito.lean 377-390
structure FujiParams where
  badRootSeam : Nat
  badRootHeight : Nat
  cutHeight : Nat
  afterCutLength : Nat
  yamakazi : Bool

def FujiParams.len (P : FujiParams) : Nat := P.afterCutLength - P.badRootSeam
```

`FujiParams.len` が JS で何度も出る `(afterCutLength-badRootSeam)` である。

## Mt.Fuji シェル

### 三重ループ

```js
// script.js 225-227
//Create Mt.Fuji shell
for (var i=1;i<=n;i++){ //iteration
  for (var j=badRootSeam;j<afterCutLength;j++){ //seam
```

```lean
-- Yukito.lean 493-498
def fujiIters (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (afterCutHeight ascFuel : Nat) :
    Nat → List Rowj → List Rowj
  | 0, res => res
  | i + 1, res =>
      let res := fujiIters M P nd afterCutHeight ascFuel i res
      fujiSeams M P nd (i + 1) afterCutHeight ascFuel P.len res
```

```lean
-- Yukito.lean 479-490
def fujiSeams (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i afterCutHeight ascFuel : Nat) :
    Nat → List Rowj → List Rowj
  | 0, res => res
  | t + 1, res =>
      let res := fujiSeams M P nd i afterCutHeight ascFuel t res
      let j := P.badRootSeam + t
      let isRep := decide (j = P.badRootSeam)
      let isAsc := isAscending M P.badRootHeight P.badRootSeam j ascFuel
      let seamH := seamHeightOf M j afterCutHeight
      let d := P.cutHeight - P.badRootHeight
      let kmax := if isAsc then seamH + d * i else seamH
      fujiRows M P nd i j isRep isAsc kmax res
```

```lean
-- Yukito.lean 466-476
def fujiRows (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i j : Nat)
    (isRep isAsc : Bool) :
    Nat → List Rowj → List Rowj
  | 0, res => res
  | kmax + 1, res =>
      let res := fujiRows M P nd i j isRep isAsc kmax res
      let sysx := fujiSourceAt P i kmax isRep isAsc
      let sx := sourceIdx M sysx.1 j sysx.2
      let ir := if isRep then 1 else 0
      let topVal := nd (j + P.len * i)
      pushAt res kmax (fujiCell M P (rowAt res kmax) sysx.1 sx kmax i j (i - ir) topVal)
```

### `isAscending` と `seamHeight`

```js
// script.js 228-254
var isAscending;
var p=0; //simplified; may not work
while (mountain[badRootHeight][p].position+badRootHeight<j) p++;
if (mountain[badRootHeight][p].position+badRootHeight==j){
  while (true){
    if (!mountain[badRootHeight][p]||mountain[badRootHeight][p].position+badRootHeight<badRootSeam){
      isAscending=false;
      break;
    }
    if (mountain[badRootHeight][p].position+badRootHeight==badRootSeam){
      isAscending=true;
      break;
    }
    p=mountain[badRootHeight][p].parentIndex;
  }
}else{
  isAscending=false;
}
var seamHeight=afterCutHeight-1;
while (true){
  var l=0;
  while (mountain[seamHeight][l]&&mountain[seamHeight][l].position+seamHeight<j) l++;
  if (mountain[seamHeight][l]&&mountain[seamHeight][l].position+seamHeight==j) break;
  seamHeight--;
}
seamHeight++;
var isReplacingCut=j==badRootSeam;
```

```lean
-- Yukito.lean 333-354
def ascendTo (M : List Rowj) (bh seam : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, p =>
    let row := rowAt M bh
    if hp : p < row.size then
      let col := (row[p]'hp).pos + bh
      if col < seam then false
      else if col = seam then true
      else
        match (row[p]'hp).par with
        | none => false
        | some q => ascendTo M bh seam fuel q
    else false

def isAscending (M : List Rowj) (bh seam j fuel : Nat) : Bool :=
  match lookupPos (rowAt M bh) (j - bh) with
  | none => false
  | some m =>
    if h : m < (rowAt M bh).size then
      if ((rowAt M bh)[m]'h).pos + bh = j then ascendTo M bh seam fuel m else false
    else false
```

```lean
-- Yukito.lean 328-330
def seamHeightOf (M : List Rowj) (j : Nat) : Nat → Nat
  | 0 => 0
  | h + 1 => if hasCol M h j then h + 1 else seamHeightOf M j h
```

JS の `seamHeight--` の下向きの走査と最後の `seamHeight++` が、`hasCol` で
見つけた段 `h` に対する `h + 1` にあたる。`isReplacingCut` は `fujiSeams` の
`isRep := decide (j = P.badRootSeam)` である。

### 枝の選択

```js
// script.js 256-259, 280, 301, 322, 344-352, 372-374
if (isAscending){
  for (var k=0;k<seamHeight+(cutHeight-badRootHeight)*i;k++){
    if (!result[k]) result.push([]);
    if (k<badRootHeight){ //Bb
      var sy=k;
      …
    }else if (k<=badRootHeight+(cutHeight-badRootHeight)*(i-isReplacingCut)){ //Br replace
      var sy=badRootHeight;
      …
    }else if (isReplacingCut&&k<=badRootHeight+(cutHeight-badRootHeight)*i){ //Br extend
      var sy=k-(cutHeight-badRootHeight)*(i-1);
      …
    }else{ //Be
      var sy=k-(cutHeight-badRootHeight)*i;
      …
    }
  }
}else{
  if (isReplacingCut) console.warn("Cut child and not connected to bad root. Makes sense.");
  for (var k=0;k<seamHeight;k++){
    if (!result[k]) result.push([]);
    //if statement is here to line up indents
    if (true){ //Bb
      var sy=k;
      …
    }
  }
}
```

```lean
-- Yukito.lean 450-463
def fujiSource (P : FujiParams) (i k : Nat) (isRep : Bool) : Nat × Bool :=
  let d := P.cutHeight - P.badRootHeight
  let ir := if isRep then 1 else 0
  if k < P.badRootHeight then (k, isRep)
  else if k ≤ P.badRootHeight + d * (i - ir) then
    (P.badRootHeight, !P.yamakazi && isRep)
  else if isRep && k ≤ P.badRootHeight + d * i then
    (k - d * (i - 1), !P.yamakazi && isRep)
  else (k - d * i, !P.yamakazi && isRep)

def fujiSourceAt (P : FujiParams) (i k : Nat) (isRep isAsc : Bool) : Nat × Bool :=
  if isAsc then fujiSource P i k isRep else (k, isRep)
```

返り値の第 1 成分が JS の `sy`、第 2 成分が次の `sx` の選び方である。上りの列の
`for` の上限 `seamHeight+(cutHeight-badRootHeight)*i` と、上りでない列の
`seamHeight` が、`fujiSeams` の `kmax` の 2 つの枝にあたる。

`sx` の選び方は Bb 枝だけ条件が違う。

```js
// script.js 262-267 （Bb 枝）
if (isReplacingCut){
  sx=mountain[sy].length-1;
}else{
  sx=0;
  while (mountain[sy][sx].position+sy<j) sx++;
}
```

```js
// script.js 283-288 （Br replace / Br extend / Be の 3 枝で同じ）
if (!yamakazi&&isReplacingCut){
  sx=mountain[sy].length-1;
}else{
  sx=0;
  while (mountain[sy][sx].position+sy<j) sx++;
}
```

これが `fujiSource` の第 2 成分の `isRep` と `!P.yamakazi && isRep` の違いで、
受け取る側はこうなる。

```lean
-- Yukito.lean 393-394
def sourceIdx (M : List Rowj) (sy j : Nat) (useLast : Bool) : Nat :=
  if useLast then (rowAt M sy).size - 1 else firstAtLeast (rowAt M sy) (j - sy)
```

### 積むセル

4 つの枝はここから先が同じ本文である。

```js
// script.js 268-279 （4 枝で共通）
var sourceParentIndex=mountain[sy][sx].parentIndex;
var parentShifts=i-isReplacingCut;
var parentPosition=mountain[sy][sourceParentIndex]?mountain[sy][sourceParentIndex].position+parentShifts*(afterCutLength-badRootSeam)*(mountain[sy][sourceParentIndex].position+sy>=badRootSeam)-(k-sy):-1;
var parentIndex=0;
while (result[k][parentIndex]&&result[k][parentIndex].position<parentPosition) parentIndex++;
if (!result[k][parentIndex]||result[k][parentIndex].position!=parentPosition) parentIndex=-1;
result[k].push({
  value:parentIndex==-1?newDiagonal[0][j+(afterCutLength-badRootSeam)*i].value:NaN,
  position:j+(afterCutLength-badRootSeam)*i-k,
  parentIndex:parentIndex,
  forcedParent:mountain[sy][sx].forcedParent
});
```

```lean
-- Yukito.lean 397-408
def parentPos (M : List Rowj) (P : FujiParams) (sy sx k shifts : Nat) : Option Nat :=
  let row := rowAt M sy
  if hx : sx < row.size then
    match (row[sx]'hx).par with
    | none => none
    | some sp =>
      if hp : sp < row.size then
        let ppos := (row[sp]'hp).pos
        let shift := if P.badRootSeam ≤ ppos + sy then shifts * P.len else 0
        if k - sy ≤ ppos + shift then some (ppos + shift - (k - sy)) else none
      else none
  else none
```

```lean
-- Yukito.lean 413-421
def fujiCell (M : List Rowj) (P : FujiParams) (cur : Rowj) (sy sx k i j shifts : Nat)
    (topVal : Nat) : Cell :=
  let pp := parentPos M P sy sx k shifts
  let pi := match pp with
    | none => none
    | some q => lookupPos cur q
  let fp := if hx : sx < (rowAt M sy).size then ((rowAt M sy)[sx]'hx).forced else false
  { pos := j + P.len * i - k, val := if pi.isNone then topVal else 0,
    par := pi, forced := fp }
```

```lean
-- Yukito.lean 445-446
def pushAt (res : List Rowj) (k : Nat) (c : Cell) : List Rowj :=
  if k < res.length then res.set k ((res.getD k #[]).push c) else res ++ [#[c]]
```

対応は次のとおり。

* `parentShifts=i-isReplacingCut` が `fujiRows` の `i - ir` で、`parentPos` の
  `shifts` に入る。
* `*(mountain[sy][sourceParentIndex].position+sy>=badRootSeam)` は真偽値を
  0 か 1 として掛ける書き方で、`if P.badRootSeam ≤ ppos + sy then … else 0` である。
* `parentPosition` が負になる場合（`?:` の `-1` 側と、引き算で負になる側）が
  `parentPos` の `none` である。
* `while (result[k][parentIndex]…) parentIndex++` と続く一致判定が `lookupPos cur q`。
* `value:…?…:NaN` の `NaN` を、ここでは値 0 で表す。実際の値はつねに正なので混ざらない。
  確定する側の `newDiagonal[0][j+(afterCutLength-badRootSeam)*i].value` が
  `fujiRows` の `topVal := nd (j + P.len * i)` である。
* `if (!result[k]) result.push([])` が `pushAt` の `else res ++ [#[c]]`。

## 値の埋めと出力

```js
// script.js 378-402
//Build number from ltr, ttb
for (var i=result.length-1;i>=0;i--){
  if (!result[i].length){
    result.pop();
    continue;
  }
  for (var j=0;j<result[i].length;j++){
    if (!isNaN(result[i][j].value)) continue;
    var k=0; //find left-up
    while (result[i+1][k].position<result[i][j].position-1) k++;
    if (result[i+1][k].position!=result[i][j].position-1) throw Error("Mountain not complete");
    result[i][j].value=result[i][result[i][j].parentIndex].value+result[i+1][k].value;
  }
}
var rr;
if (stringify){
  rr=[];
  for (var i=0;result[0]&&i<result[0].length;i++){
    rr.push(result[0][i].value+(result[0].forcedParent?"v"+result[0].parentIndex:""));
  }
  rr=rr.join(",");
}else{
  rr=result;
}
return rr;
```

```lean
-- Yukito.lean 526-539
def fillRow (row up : Rowj) : Rowj :=
  row.foldl (init := #[]) fun acc c =>
    acc.push (if c.val ≠ 0 then c
      else { c with val := (match c.par with
                            | none => 0
                            | some p => valAtIdx acc p) + readValAt up (c.pos - 1) })

def fillValues : List Rowj → List Rowj
  | [] => []
  | [r] => [r]
  | r :: rest =>
      let rest := fillValues rest
      fillRow r (rest.headD #[]) :: rest
```

```lean
-- Yukito.lean 542-547
def dropEmptyTop : List Rowj → List Rowj
  | [] => []
  | a :: t =>
      if ((a :: t).getD (t.length) #[]).size = 0 then
        dropEmptyTop ((a :: t).take t.length)
      else a :: t
```

```lean
-- Yukito.lean 574
def expandOut (M : List Rowj) : List Nat := (rowAt M 0).toList.map (·.val)
```

`for (i=result.length-1;i>=0;i--)`（上から下へ）が `fillValues` の再帰、
`if (!isNaN(…)) continue` が `if c.val ≠ 0 then c`、
`result[i][result[i][j].parentIndex].value` が `valAtIdx acc p`、
`result[i+1][k].value`（1 つ上の段の左上）が `readValAt up (c.pos - 1)` である。
`readValAt` はこれ。

```lean
-- Yukito.lean 435-441
def valAtIdx (row : Rowj) (i : Nat) : Nat := if h : i < row.size then (row[i]'h).val else 0

def readValAt (row : Rowj) (c : Nat) : Nat :=
  match lookupPos row c with
  | none => 0
  | some m => if h : m < row.size then (row[m]'h).val else 0
```

## 意図的に違えたところ

**燃料。** JS の `while (true)` は Lean では停止しないので、`calcMountain` /
`getBadRoot` / `expand` の再帰に燃料を付けた。主定理はどの燃料も十分大きければ
よい、という形になっている。

```
mfuel    山を作る／bad root を探すループの上限
efuel    newDiagonal = expand(diagonal, n, false) の再帰の上限
ascFuel  isAscending の親鎖を辿るループの上限
```

**`-1` と `undefined`。** JS の `parentIndex = -1` は `Option Nat` の `none`、
配列外の `mountain[h][k]` は空行（`rowAt`）または `none`（`lookupPos`）にした。
`parentPosition` が負になる場合は `parentPos` が `none` を返す。

**自然数の切り捨て引き算。** JS が `position - 1` を目標にする所で `position = 0`
だと目標は `-1` になり、どのセルにも一致しない。

```js
// script.js 104-111
var m=0; //find up-left of that=left
while (mountain[height][m].position<mountain[height-1][l].position-1) m++;
if (mountain[height][m].position==mountain[height-1][l].position-1){ //left exists
  lastIndex=m;
}else{
  height--;
  lastIndex=l;
}
```

Lean の `Nat` では `0 - 1 = 0` になってしまうので、`legStepJS` でここだけ
場合分けして「一致しない」側に倒してある。

```lean
-- Yukito.lean 180-187
              -- JS の目標は `position - 1`。`position = 0` なら `-1` になり、
              -- どのセルにも一致しないので必ず段を下げる。自然数の切り捨て
              -- 引き算では `0` になってしまうので、ここだけ場合分けする。
              if (below[l]'hl).pos = 0 then some (h', l)
              else
                match lookupPos row ((below[l]'hl).pos - 1) with
                | some m => some (h' + 1, m)
                | none => some (h', l)
```

**文字列。** `calcDiagonal` の `r.join(",")` と `parseSequenceElement` の解析は
往復して元に戻るだけなので、`List DiagItem` を直接渡す形にした。

**複製。** `cloneMountain`（146–161）は JS が破壊的に書き換えるためのもので、
Lean では要らない。

**使われない変数。** `badRootSeamHeight`（217–224）と `afterCutMountain`（215）は
JS で計算されるがその後どこでも読まれないので写していない。

**`newDiagonal` の重複 `position`。** JS は 197 行で同じセルの参照を積むため
`position` が重複するが、値しか読まれない。Lean では値の関数 `Nat → Nat`
（`yamaVal` か、再帰した `expandJS` の行 0 を読む `valAtIdx`）として持つ。

## 忠実さの検査

この対応は読み合わせであって、証明ではない。`script.js` は Lean の対象ではないので、
写しが原本と同じ関数であること自体は証明できない。代わりに原本を実行した出力と
突き合わせて `#guard` に固定してある（`Equiv/YukitoCheck.lean`）。`calcMountain` /
`calcDiagonal` / `getBadRoot` / `expand` の各段階と、`expand` の分岐を一通り通す例、
および上りでない列が `badRootHeight` より高くなる例を含む。
