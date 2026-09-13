# 1y-expand-equiv

2026 年 9 月 10 日に Phyrion 氏の Lean 4 による 1-Y 数列の整礎性・整列性の[形式化](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean)が公開された。

ただし Phyrion 氏の[論文](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean/blob/6533b2975f3cafb3582dc8f8127e9ea7144d7e69/Well-Ordering%20of%20the%201-Y%20Sequence%20System.pdf)にはこう書かれており、**Phyrion 版は Yukito 版の形式化であるとは主張していない**。

> The precise convention considered here is the ancestor-preserving algorithm below and in
> the fixed source snapshot. No equivalence with every variant described elsewhere is assumed.

それを受けてこのリポジトリでは 1-Y 数列の展開規則について、次の 2 つが同じ関数であることを検証する。

| | 何か | 場所 |
|---|---|---|
| Yukito 版 | Yukito 氏による 1-Y の展開規則 | [Naruyoko/YNySequence](https://github.com/Naruyoko/YNySequence) の [`script.js`](https://github.com/Naruyoko/YNySequence/blob/2de13970b9ac818c935577b8284c41dec01f0039/script.js) の `expand` |
| Phyrion 版 | Phyrion 氏が独自に定めた祖先保存アルゴリズム | [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) の [`OneY.Numeric.expandValues`](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean/blob/6533b2975f3cafb3582dc8f8127e9ea7144d7e69/formalization/OneY/Expansion.lean#L46) |

## 検証方法

```mermaid
flowchart TB
  subgraph Y[Yukito 版]
    A["原本<br>script.js"]
    B["Lean 化<br>Equiv/Yukito.lean"]
  end
  subgraph P[Phyrion 版]
    C["Lean<br>expandValues"]
  end
  A <-->|"1: 読み合わせ"| B
  B <-->|"2: expand_eq で証明"| C
```

| 図の箱 | ファイル |
|---|---|
| 原本 | [`script.js`](https://github.com/Naruyoko/YNySequence/blob/2de13970b9ac818c935577b8284c41dec01f0039/script.js)（Naruyoko/YNySequence コミット 2de1397） |
| Lean 化 | [`Equiv/Yukito.lean`](Equiv/Yukito.lean) |
| Lean | [`OneY.Numeric.expandValues`](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean/blob/6533b2975f3cafb3582dc8f8127e9ea7144d7e69/formalization/OneY/Expansion.lean#L46)（Phyrion1343/1Y-Well-Ordering-Lean コミット 6533b29） |

## 検証結果

### (1) js ⇔ lean の対応

`script.js` の本文と `Equiv/Yukito.lean` の本文を並べて読み合わせた。
[correspondence.md](correspondence.md) にある。

### (2) lean ⇔ lean の証明

[`Equiv/Lower.lean`](Equiv/Lower.lean#L2152) の `expand_eq` で証明した。

```
theorem expand_eq (s : List Nat) (hs : ZeroY.Legal s) (N m efuel : Nat)
    (hm : sequenceBound s ≤ m) (hml : s.length ≤ m) (hef : sequenceBound s ≤ efuel)
    (hn : 0 < s.length) :
    expandOut (expandJS N (m + 1) efuel (calcMountain s (m + 1))) = expandValues s hs N
```

`ZeroY.Legal s` は「すべての要素が正」かつ「先頭が 1」で、Phyrion 版が `expandValues` に
課している条件そのものである。標準形の Y 数列はこれを満たす。`m` と `efuel` は燃料で、
`sequenceBound s`（値の最大）と列の長さ以上あれば足りる。

`sorry` は無く、公理は `propext` / `Classical.choice` / `Quot.sound` のみ。

したがって Phyrion 版の整礎性・整列性の結果は、そのまま Yukito 版の 1-Y についての
結果になる。

## 座標の対応

Yukito 版は疎配列、Phyrion 版は列ごとの値の関数である。対応は次のとおり。

```
Yukito 版 (行 r, position P)  ↔  Phyrion 版 (行 r, 列 c = P + r)
```

この変換のもとで、`script.js` の「右腿で下へ、親を取り、左腿で上へ」という歩行は、
前の行の親チェーンをそのまま辿ることになる。

## 証明の骨格

[Equiv/README.md](Equiv/README.md) にある。

## ビルド

Lean 4.33.1 が要る。依存として Phyrion 版の形式化を兄弟ディレクトリに置く。

```sh
git clone https://github.com/Phyrion1343/1Y-Well-Ordering-Lean
git clone git@github.com:koteitan/1y-expand-equiv
cd 1y-expand-equiv
lake --keep-toolchain --no-cache build Equiv
```

`lakefile.toml` は依存を `../1Y-Well-Ordering-Lean/formalization` として参照する。
