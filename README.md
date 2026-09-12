# 1y-expand-equiv

1-Y 数列の展開規則について、次の 2 つが同じ関数であることの Lean 4 による証明。

| | 定義 | 実装 |
|---|---|---|
| Yukito 版 | Yukito 氏による 1-Y の展開規則 | [Naruyoko/YNySequence](https://github.com/Naruyoko/YNySequence) の `script.js` の `expand` |
| Phyrion 版 | 同上を形式化したもの | [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) の `OneY.Numeric.expandValues` |

Phyrion 版は 1-Y の展開の整礎性と標準生成集合の辞書式整列を Lean 4 で証明している。
本リポジトリが扱うのは、**その形式化の対象が Yukito 版の定義と一致しているか**という別の問題である。

## いま示せていること

`sorry` は無く、公理は `propext` / `Classical.choice` / `Quot.sound` のみ。

| ファイル | 内容 |
|---|---|
| `Equiv/Yukito.lean` | `script.js` の `calcMountain` を Lean へ書き起こしたもの。疎配列・添字演算・`break` の位置まで写す |
| `Equiv/Bridge.lean` | 疎表現（生きたセルだけを並べる）と密表現（値 0 が不在）の読み替え |
| `Equiv/Row0.lean` | **行 0 の親写像が一致する**（`restrictedParent_linear`） |
| `Equiv/Row0Spec.lean` | 行 0 の親の初等的な特徴づけ |
| `Equiv/RowSucc.lean` | 正値条件が「鎖の根を除く」ことと同値（`succ_parent_iff`） |
| `Equiv/RootCase.lean` | 残る義務の明文化と、Lean 側が根を親にしないこと |
| `Equiv/RootZero.lean` | 行 0 について残る義務を証明（`firstLive_not_smaller_zero`） |
| `Equiv/RootGen.lean` | 一般の行への還元。義務が 2 本に減ることを示す |

## 座標の対応

疎表現と密表現は次で対応する。

```
Yukito 版 (行 r, position P)  ↔  Phyrion 版 (行 r, 列 c = P + r)
```

この変換のもとで、`script.js` の「右腿で下へ、親を取り、左腿で上へ」という歩行は、
前の行の親チェーンをそのまま辿ることになる。

## 残っている課題

山（差分山脈）の段について、一般の行では次の 2 つが未証明である。

```
(a) 鎖の根は、根より右で最初に生きている列の祖先である
(1) 上記 2 列の値に U p ≤ U j が成り立つ
```

これがあれば `diff_le_of_a_and_one` で山の段の一致が従う。手がかりとして、
森の辺が真に交差しないという古典的性質が使えると見ている。

山の段が済んでも、抽出・bad root・コピー層が残る。コピー層が全体の大半である。

## ビルド

Lean 4.33.1 が要る。依存として Phyrion 版の形式化を兄弟ディレクトリに置く。

```sh
git clone https://github.com/Phyrion1343/1Y-Well-Ordering-Lean
git clone git@github.com:koteitan/1y-expand-equiv
cd 1y-expand-equiv
lake --keep-toolchain --no-cache build Equiv
```

`lakefile.toml` は依存を `../1Y-Well-Ordering-Lean/formalization` として参照する。
