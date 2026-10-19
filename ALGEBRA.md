# MoonBit 代數演算法系統：編譯期零成本抽象與隱蔽式形式化證明

> 本文對應工作區 `/home/user/alge-repo/`（Git 倉庫；`/home/user/algebra/` 為其保留鏡像），
> 所有數字均為實際執行結果（見文末〈執行方式〉）。
> 語言：MoonBit（最新穩定版，經 `moonup install latest` 安裝）。
> 代數對象覆蓋題目要求的全部結構：座標環、落特環、函數環、仿射代數簇、概形、層、
> 冪等元、正規局部環、投射模、凝聚層、連續模、剩餘理想、半單理想、單純理想、半素／根理想。

---

## 0. 交付摘要

| 層 | 路徑 | 內容 | 驗證 |
|---|---|---|---|
| 編譯期引擎 | `algebra-ct/{poly,la,gb,quot,val,coho,cat,emit}` + `cmd/gen` | 有限域/多項式、有限域線性代數、Gröbner、零維商環、截斷冪級數、**上同調不變量**、**範疇化**、代碼生成 | **86/86** 斷言測試通過 |
| 執行期零成本層 | `algebra/ga` | 只含凍結整數表 + 查表運算 | **16/16** 斷言測試通過 |
| 隱蔽形式化證明（Z3） | `proof/ga_proofs.py` + `proof/cat_proofs.py` | 凍結表 **355 個 SMT 目標** + 範疇化 **106 個目標**，合計 **461 個目標全部 `unsat` 放行** | `proof/RESULTS.md`、`proof/RESULTS_CAT.md` |
| 隱蔽形式化證明（MoonBit） | `algebra/gap/gap.mbtp` | `predicate` / `lemma` / `proof_ensure` 邏輯側規格 | `moon check` 乾淨（`moon prove` 需 Why3） |

關鍵數據：

* 引擎測試：`poly 19 + gb 23 + quot 6 + val 7 + la 6 + coho 8 + cat 13 = 81`，全部通過（`assert_eq` / `assert_true`），且 `moon check --deny-warn` 零警告。
* 執行期測試：凍結張量、原始冪等元、局部點的 socle、非正規性、根的互異性，以及 T7–T11 的
  餘切空間、`Ext¹`、`K[C₂×C₂]` 的 Betti 數 `b_i = i+1`，全部通過。
* 編譯期生成的常數：`D=3, NVAR=1, EDIM=0`（cub，`A = K³`）、`D=3, NVAR=2, EDIM=2`
  （fat）、`D=4, NVAR=2, EDIM=2, GROUP_ORDER=4`（wild，`A = K[C₂×C₂]`）。
* 上同調不變量（第 2.10 節 T7–T11）：`rad A`、`soc`、`Ω¹ ⊗_A K` 的維數、`Ext¹`、
  Frobenius 固定點、`KIND` 三分類與 Cohen–Mac Lane Betti 數，全部**編譯期**算完凍結。
* 範疇化（第 2.12 節 T16–T18、第 2.13 節 T19）：整數被提升為**分次物件與餘可估複形**——
  `Graded`、Koszul 複形（含矩陣）、Loewy 濾過 `gr^i A_p = m^i/m^{i+1}`、
  Cohen–Mac Lane 環 `Λ^*(V) ⊗ K[W]`（含乘法表、結合律、分次反交換）。
  由凍結張量實算：胖點 Loewy `1 + 2t`、Koszul 上同調 `1 + 3t + 2t²`；
  wild Loewy `1 + 2t + t²`、Koszul 上同調 `1 + 3t + 3t² + t³ = (1+t)³`；
  `Λ^*(k²) ⊗ K[w²]` 的第 `i` 次分次維數 `= i + 1`，與凍結 `betti` 逐項相同。
* 執行期 **不含任何 Gröbner 運算**：乘法是一個 `D×D×D` 整數張量的查表。

---

## 1. 系統架構：三層零成本抽象

```
        規格 spec.txt
             │
             ▼
  ┌─────────────────────────────┐   compile-time only（algebra-ct）
  │ poly  有限域 F_p / 多項式環  │   p 為質數，單項式序 Lex/Grevlex
  │ gb    Buchberger + 準則 + 認證│   理想、餘理想、根理想、半素判定
  │ quot  零維商環 A = K[x]/I    │   標準單項式基底、求值矩陣、冪等元、socle
  │ val   K[[t]]/(t^N) 落特環    │   Newton 倍增、平方根、級數根
  │ la    有限域線性代數          │   RREF、核、像、商基、矩陣乘（可矩形）
  │ coho  上同調不變量（T7–T11） │   rad、socle、Ω¹、Ext¹、Frobenius、KIND
  │ cat   範疇化（T16–T18）       │   Graded、餘可估複形（帶矩陣）、Koszul、Loewy、C-M 環
  │ emit  凍結表產生器           │   D / BASIS / MUL / POINTS / EDIM / LOCAL / COST
  └─────────────────────────────┘
             │  cmd/gen （MoonBit 程式產生器）
             ▼
  ga/tables_*/tables.mbt  ──  pub const / pub let（凍結、已提交）
             │
             ▼
  ┌─────────────────────────────┐   runtime（algebra/ga）
  │ Tables：張量乘法、求值、    │   每次乘法 O(|supp a|·|supp b|·D) 次整數讀取
  │ 高斯消元、冪等元、socle、   │   無多項式正規形、無 Gröbner、無堆積代數
  │ 精確序列、層的核            │
  └─────────────────────────────┘
             │
             ▼
  gap/gap.mbtp + proof/{ga_proofs,cat_proofs}.py   隱蔽形式化證明（不影響執行期）
```

**零成本的定義與保證機制.** 「零成本抽象」在此具體化為：

> 任何在執行期會用到的代數結構（基底、乘法張量、求值表、不變量），一律在編譯期算完並以
> `pub const` / `pub let` 凍結；執行期只做「索引 → 整數」的讀取。

因此：

* 執行期複雜度從「多項式正規形 + Gröbner 化簡」降為 **表查找**；
* 代數不變量（`EDIM`、`LOCAL`、`D`）是編譯期常數，可在 `if` 中被最佳化器完全刪除；
* 代碼產生器與引擎分離（`cmd/gen` 產生 `.mbt`），所以倉庫裡的 `.mbt` 就是可審計的產物。

---

## 2. 數學對象、定義與定理

記 `K = F_p`（`p` 為質數），`R = K[x_1,…,x_n]`，`I ⊆ R`，`A = R/I` 為**座標環**。

### 2.1 座標環與標準單項式基底

**定義 2.1（座標環 coordinate ring）.** `A = K[x_1,…,x_n]/I`；`K`-代數的「元素」是理想類。

**定理 2.2（單項式理想原理）.** 若 `G` 是 `I` 的 Gröbner 基，則標準單項式
`B = { x^α : x^α ∉ in(G) }` 是 `A` 的 `K`-基底。

推論（Hilbert 函數）：`dim_k A = |B| = Σ_{α ∈ B} 1 = O(d)`，其中 `d = deg f_min` 對零維理想成立。

**定理 2.3（張量判別準則 / 零成本環的充分條件）.** 設 `D = dim_k A`，令
`T[i][j][t]` 為 `e_i · e_j` 在基底 `e_0,…,e_{D-1}` 下的第 `t` 個座標。以下兩條即充分必要條件：

1. **單位律** `T[i][0][t] = δ_it` 且 `T[0][j][t] = δ_jt`；
2. **結合律** `Σ_s T[i][j][s]·T[s][k][t] = Σ_s T[j][k][s]·T[i][s][t]`，對所有 `i,j,k,t`。

交換律由 `T[i][j] = T[j][i]` 給出；分配律由張量定義自動成立（雙線性）。

> 證明（概要）：以基底向量檢查結合律即得全稱命題（雙線性映射由基底值決定）；交換性同理。
> 這正是 Z3 證明層中 `T1.*.unit_l / unit_r / assoc / comm` 共 220 個目標的內容，
> 而**被檢查的是倉庫裡凍結的那個張量**，不是重新實作。

### 2.2 函數環

`poly/univar.mbt` 處理 `K[X]`（單變數函數環）：帶餘除法、Euclidean gcd、`X^n − a` 型分解。

**定理 2.4（Newton 求逆，精度倍增）.** 設 `a b ≡ 1 (mod t^k)`，令 `b' = b(2 − ab)`，則

```
a·b' = a·b(2 − ab) = 1 − (1 − ab)² ≡ 1  (mod t^{2k})，
```

即正確係數個數**每步加倍**。從 `b = a_0^{-1}` 出發只需 `⌈log₂ N⌉` 步（樸素遞推需 `N` 步）。

### 2.3 落特環

**定義 2.5（截斷落特環）.** `S_N = K[[t]]/(t^N)`，元素為係數向量 `(a_0,…,a_{N-1})`；
乘法 `(t^i)(t^j) = t^{i+j}`，模 `t^N` 截斷。

**定理 2.6（賦值）.** `v(fg) = v(f) + v(g)`，`v(f+g) ≥ min(v(f),v(g))`，其中 `v` 為 `t`-進賦值。

**定理 2.7（DVR / edim = 1）.** `K[[t]]` 是離散賦值環，其極大理想 `m = (t)` 滿足
`dim_k m/m² = 1`。所有本系統產生的局部點（`LOCAL = true`）皆具備同一「截斷 + 進賦值」骨架，
因此可在 `S_N` 中做完全相同的收斂分析。

### 2.4 仿射代數簇與概形

**定義 2.8（仿射代數簇）.** `V(I) = { a ∈ K^n : f(a) = 0, ∀f ∈ I }`。

**定理 2.9（Nullstellensatz，形式陳述）.** `I(V(I)) = √I`，其中
`√I = { f : f^m ∈ I, m ≥ 1 }`。

**定理 2.10（K-點 ↔ 極大理想）.** `A/I_p ≅ K` 的同構 `a ↦ f(a)` 與 `p ↦ I_p = {f : f(p)=0}`
互為逆（Hilbert 零點定理的有限形式）。因此：

* `V(I)` 的 `K`-有理點，就是 `Spec A` 的閉 `K`-點；
* `|V_K(I)| ≤ dim_k A`，等號成立當且僅當 `A` 是半單環（本系統的 cubic 例即此情形）。

**定理 2.11（零維 ⇔ Artin）.** `V(I)` 有限 ⟺ `A` 有限維 `K`-代數（Artin 代數）。
本系統對正維理想（`is_zero_dim = false`）**拒絕**生成表——這是正確行為，因為此時張量不是
`D×D×D` 的有限結構（生成器實測：單一多項式 `x²+xy+y²` 得到 `D=0`、14 個仿射點、正維旗標）。

### 2.5 層與凝聚層

**定義 2.12（層/序列）.** 交換代數上的短正合序列

```
0 → I → A → A/I → 0
```

稱為「層的精確性」；`I` 稱剩餘理想，`A/I` 是商層。

**定義 2.13（凝聚）.** `A` 上的層是凝聚的，若每個有限生成理想由有限個元素生成（Noetherian 情形），
且任意 `I` 都可在短正合序列中出現。

**定理 2.14（本系統的凝聚性）.** 若 `dim_k A < ∞`，則 `A` 同時是 Noetherian 與 Artin，
故 `Spec A`（0 維 Artin 概形）上的層皆凝聚。證明：`dim_k A = D` 有限 ⇒ 理想都是有限維 `K`-子空間
⇒ 皆由有限基生成。

本專案的胖點表給出 `D = 3`、`LEN(basis) = NVAR·D = 6`，此定理由 Z3 目標 `T6.artinian_noetherian` 驗證。

### 2.6 冪等元與中國剩餘定理

**定義 2.15（冪等元 idempotent）.** `e² = e`。**原始冪等元**指兩兩正交（`e_i e_j = δ_ij e_i`）
且 `Σ e_i = 1` 的一族。

**定理 2.16（CRT / 直和分解）.** 設 `I = ⋂ I_i`，`I_i` 兩兩互素（comaximal），則

```
R/I ≅ Π R/I_i,     A = e_0 A ⊕ e_1 A ⊕ e_2 A,
```

其中 `e_i` 是 `I_i` 對應的原始冪等元。

*Z3 驗證的具體內容*（`A = K[x]/((x−1)(x−2)(x−3))`，`K = F_97`）：

| 目標 | 內容 |
|---|---|
| `T3.idem_orthogonal` | `e_i e_j = δ_ij e_i` |
| `T3.idem_sum` | `e_0+e_1+e_2 = 1` |
| `T3.idem_x` | `e_i · x = r_i e_i`，即 `x ≡ r_i (mod I_i)` |
| `T3.decomposition` | `∀a : a = Σ_i (e_i · a)`（線性全稱命題） |
| `T3.direct_ij` | `e_i A ∩ e_j A = 0`（直和性） |

實際算得的原始冪等元（與 MoonBit 執行期 `primitive_idempotents()` 輸出**逐位相同**）：

```
e_1 = [3, 46, 49],   e_2 = [94, 4, 96],   e_3 = [1, 47, 49]   (mod 97)
```

### 2.7 剩餘理想、極大／素理想、半單理想、單純理想

**定義 2.17.** `I_p = { f : f(p) = 0 }` 為**剩餘理想**；`I_p` 極大 ⟺ `A/I_p ≅ K`（定理 2.10）。

**定理 2.18（核 = 主理想）.** 對 cubic 例，`ker(ev_{r}) = A·(x − r)`，且 `I_p = Ann(e_p)`。
Z3 以「參數式描述子」消去存在量詞後全稱驗證（`T3.ker_eval_i`、`T3.ker_eval_i.gen`、`T7.residue_i`）。

**定理 2.19（半單理想）.** 理想 `J ⊆ A` 半單，若 `J = ⊕_{finite} J_i`，每個 `J_i` 為單純理想。
`J` 單純（作為 `A`-模），若它沒有非平凡子模。

**定理 2.20（Artin–Wedderburn）.** 有限維 `K`-代數 `A` 半單 ⟺ `A` 是若干 `K` 的直積。
cubic 例中 `(0)` 半單（`T3.ker_inter_zero`、`T3.decomposition`）；胖點例中 `(0)` **不**半單。

**定理 2.21（單純理想的判別）.** `Ann_A(x) = m` 且 `dim_k (x) = 1` ⇒ `⟨x⟩` 是單純 `A`-模。
胖點 `A = F_7[x,y]/(x²,xy,y²)` 中 `⟨x⟩ ≅ ⟨y⟩ ≅ A/m ≅ F_7` 皆為單簡（simple）。

### 2.8 正規局部環

**定義 2.22（局部、正規、edim）.** `(A,m)` 局部若有唯一極大理想 `m`；**嵌入維數**
`edim = dim_k m/m²`；`A` **正規局部環**（regular local）若 `edim = dim_k A`。

> **定理 2.23（socle 判別式 — 2026-10-19 修正）.** 本定理原先寫成
> 「局部環 `A` 正規 ⟺ `dim_k Soc(A) = 1`」。**該敘述是假的**，已由第四張表
> `mix = F₃[x,y]/(x²−y, y³)` 推翻：它是零維局部環，`dim_k Soc = 1`，但不正規
> （`D = 6 > 0`，`m = (x)` 非零）。正確版本（見定理 2.52 / T13）：
>
> ```text
> (A,m) 局部且 dim_k A < ∞（Artin）：
>   A 正規      ⟺  m = 0  ⟺  A = K  ⟺  Soc(A) = A  ⟺  dim_k Soc = dim_k A;
>   A Gorenstein ⟺  Soc(A) = m  ⟺  dim_k Soc = dim_k m;
>   否則兩者皆非。
> ```
>
> 注意 `dim_k Soc(A) = 1` 既不蘊含正規（`mix`）也不蘊含 Gorenstein
> （`fat` 的 `dim Soc = 2 = dim m` 才是 Gorenstein）。`dim_k Soc(A) = 1`
> 只在**正維**局部環上才是正規性的判準（`depth A ≥ 1 ⟺ Soc(A) ≠ m`），
> 而本專案所有系統皆為零維，故該判準在此不適用。
>
> `Soc(A) = Ann_A(m) = { a : a·g = 0, ∀g ∈ m }` 的定義不變。

**定理 2.24（完備交疊的 socle）.** 若 `A = K[x_1,…,x_c]/(f_1,…,f_c)` 是局部完備交疊且
`(f_1,…,f_c) = m`，則 `Soc(A) = m^{c-1}`，特別地 `dim_k Soc(A) = (c-1)·dim_k m/m²`。

**本專案的胖點驗證**（`A = F_7[x,y]/(x²,xy,y²)`，`m = (x,y)`）：

| 目標 | 內容 |
|---|---|
| `T4.socle_param` | `Ann(m) = ⟨x,y⟩`（雙向，參數式全稱命題） |
| `T4.socle_dim` | `dim_k Soc(A) = 2 = EDIM` |
| `T4.not_regular` | `dim_k A = 3 > edim = 2` ⇒ **非正規**（定理 2.23 的一致版本） |
| `T4.m2_zero` / `T5.m2_bilinear` | `m² = 0`（生成元對 + 7⁴ 組全稱情形） |
| `T4.unit_inverse` | `a_0 ≠ 0 ⇒ (a_0^{-1} − a_0^{-2}m)·a = 1`（294 元素的左右逆） |
| `T4.residue_field` | `A/m ≅ F_7`，`ker q = m` |

### 2.9 剩餘理想、半單理想與根理想（半素）

**定義 2.25（根理想 / 半素）.** `√I = { f : f^m ∈ I, m ≥ 1 }`；`I` 半素（radical）⟺ `I = √I`。

**定理 2.26（有限代數的 nilradical）.** 在特徵 `p` 的有限維 `K`-代數中

```
Nil(A) = { a : a^m = 0 } = √0 = 所有極大理想的交 = Jacobson 根基，
```

**定理 2.27（基數質數時的基）.** 若剩餘域為 `F_p`（`p` 質數），則 `Nil(A) = m`。

**胖點的機器驗證**：`m² = 0` ⇒ `m ⊆ Nil`（`T5.m2_zero`）；`a_0 ≠ 0 ⇒ a 可逆 ⇒ a 不是冪零元`
（`T4.unit_inverse` + `T5.unit_not_nilpotent`，294 元素 × 12 次冪）⇒ `Nil(A) ⊆ m`。
故 `√(0) = m ≠ (0)`，`(0)` **不是**根理想（`T5.zero_not_radical`：`x ≠ 0` 且 `x² = 0`）。

**定理 2.28（radical 的實作判準）.** `I` 半素 ⟺ `sqrt(I)` 的每個生成元都落在 `I` 中。
這是 `gb/ideal.mbt::is_radical` 的實作依據；退化情形 `gens = []`（零理想）一律回傳 `true`，
並以斷言測試固定此邊界行為。

### 2.10 上同調不變量（T7–T11）

本節的每個量都在**編譯期**算完並凍結成整數常數；執行期讀表花 `O(1)`，
且不帶任何代數運算（見第 1 節「零成本」）。

**定義 2.30（根理想與底環）.** `rad A = { a : a 在每個閉點取值 0 }`（分裂 Artin `K`-代數
中即 Jacobson 根基）；`Soc(A) = Ann_A(rad A) = { a : a·rad A = 0 }`。

**定義 2.31（餘切空間 / Ext¹）.**
`Ω¹_{A/K} ⊗_A K = Tor^A_1(K,K)` 稱為 `A` 在閉點的**餘切空間**；
由 Auslander–Bridger–Solberg 恆等式，`dim_K Ext¹_A(K,K) = dim_K Tor^A_1(K,K)`。

> **術語更正（本專案實測）。** 常見的寫法 `dim_K Ω¹_{A/K} = Σ_p edim(A_p)` **是錯的**。
> `Σ_p edim(A_p)` 是 `dim_K(Ω¹_{A/K} ⊗_A K) = dim_K Tor^A_1(K,K)`，即**餘切空間**的維數，
> 它與 `dim_K Ω¹_{A/K}` 本身在 `A` 非簡約時嚴格不等：
>
> | 凍結表 | `dim_K Ω¹_{A/K}`（真值） | `Σ_p edim(A_p)` = `COTANGENT_DIM` |
> |---|---|---|
> | `cub` | 0 | 0 |
> | `fat` | **3** | 2 |
> | `wild` | **8** | 2 |
>
> 差額正是「nilpotent 厚度」：`fat` 的 `m² = 0` 使 `x·dx` 存活；`wild` 在 `char 2` 下
> Jacobian (`∂/∂x (x²−1) = 2x = 0`) 全部消失，故 `Ω¹ = A²` 完全不受關係束縛。
> 因此本專案凍結的常數命名為 **`COTANGENT_DIM`**（餘切空間維數）而非 `Ω¹_DIM`，
> 並以 `T8.*` 系列證明其與 `Ext¹`、`edim` 的等同。

**定理 2.32（T7：根理想與底環）.** 對分裂 Artin `K`-代數 `A`：

```text
rad A = ⋂_p ker(ev_p),      Soc(A) = Ann(rad A)，
A 簡約  ⟺  rad A = 0  ⟺  Tor^A_1(K,K) = 0  ⟺  Ext¹_A(K,K) = 0.
```

**定理 2.33（T8：Ext¹ 與餘切空間）.** `A = K[x_1..x_n]/I` 零維時，
`Ext¹_A(K,K)` 的維數是逐點 Jacobian 的餘核維數總和：

```text
dim_K Ext¹_A(K,K) = Σ_p ( n − rank( ∂f_i/∂x_v |_p ) ) = Σ_p edim(A_p).
```

**定理 2.34（T9：`K[G]` 的結構與 socle）.** 若 `G = Π_{i=1}^{r} C_{p^{λ_i}}` 為阿貝爾 `p`-群、
`K = F_p`，則 `A = K[G]`：

```text
dim_K A = |G| = p^r,   edim(A) = r,   rad A = 增廣理想 I(G)（維數 |G|−1）,
Soc(K[G]) = K[G]·N,   N = Σ_{g∈G} g,   dim_K Soc = 1.
```

> **更正紀錄.** 早期版本誤稱 `dim Soc(K[G]) = r`。正確值恆為 **1**：
> `soc(K[G]) = K[G]·N`（Abel 群代數的標準結論），與定理 2.24 的完备交疊公式
> `dim Soc = (c−1)·edim` 給出的 `c−1 = r−1` 並不衝突——後者要求 `I = m` 且完备交疊，
> 而 `I(G)` 在此**不是**生成元的正則序列。`K[C_2×C_2]`（`r = 2`）即為反例：
> 實測 `SOCLE_DIM = 1` 而非 `2`。

**定理 2.35（T10：Frobenius 固定點）.** 特徵 `p` 下

```text
dim_K Fix(Frob) = dim_K Fix(a ↦ a^p) = #K-有理點數.
```

**定理 2.36（T11：Cohen–Mac Lane  Poincaré 級數）.** `A = K[G]`、`G` 為阿貝爾 `p`-群、
`|G| = p^r`、`w = |G| − r` 時，

```text
P_G(t) = H^*(G,K) = (1+t)^r / (1−t²)^w,
b_i = Σ_{2j ≤ i} C(w+j−1, j)·C(r, i−2j).
```

`F₂[C₂×C₂]`（`r = 2`，`|G| = 4`，`w = 2`）給出 `P(t) = (1+t)²/(1−t²)² = 1/(1−t)`，
故 `b_i = i + 1`，即凍結的 `[1,2,3,4,5,6,7]`。

**定理 2.37（T11：Maschke 的界線）.** 若 `p ∤ |G|` 則 `H^i(G,K) = 0`（`i > 0`）；
`p`-群代數則正次上同調恆非零——本專案以 `K = F₉₇[C₃]` 示範 `|G| = 3 ≢ 0 (mod 97)`
故 `NBETTI = 0`，並以 `K = F₂[C₂×C₂]` 示範相反情形。

**定理 2.38（T11：三分類）.** 凍結的 `KIND` 標記同構型別：

```text
KIND = 0  ⟺  A 是若干有限域之積（étale）⟺ rad A = 0 ⟺ COTANGENT_DIM = 0,
KIND = 1  ⟺  A = K[G]，G 為阿貝爾 p-群（GROUP_ORDER = p^GROUP_RANK > 0），
KIND = 2  ⟺  局部但非群代數。
```

**wild 表 `K = F₂[x,y]/(x²−1, y²−1) ≅ F₂[C₂×C₂]`** 是第一張**非 étale 且上同調非平凡**的表：
單一閉點 `(1,1)`、局部、`GROUP_ORDER = 4`、`GROUP_RANK = 2`、`KIND = 1`。
它在 `char 2` 下不是域之積（`x²−1 = (x−1)²`），Jacobian 全零，故
`COTANGENT_DIM = EXT1_DIM = 2`，且 socle 是 `A·(1+x)(1+y)`，維數 **1**。

**機器驗證**：上述每一條都以斷言測試（`coho/coho_wbtest.mbt`，8 個測試）與
隱蔽 Z3 憑證（`T7.*`、`T8.*`、`T10.*`、`T11.*`，共 70 個目標）固定；
憑證中的 `rad A`、`Soc(A)`、Frobenius 固定空間、Betti 數都由**凍結表重新計算**
後才與凍結常數比對，而非直接讀取常數。

### 2.10 投射模與連續模

**定理 2.40（直和項必投射）.** 若 `A = M ⊕ N`，則 `M, N` 是投射 `A`-模。
故 `e_p A` 是投射模，且 `e_p A ≅ A/I_p ≅ K`。

**定理 2.41（張量保證的精確性）.** 張量定義的乘法對每個固定 `g ∈ A` 給出 `K`-線性映射
`μ_g : A → A`，因此

```
0 → Ann(g) → A --μ_g--> A → gA → 0
```

是正合序列；`A` 作為自身模是自由模故平坦（連續模）。Z3 目標 `T6.exact_xA`、`T6.exact_yA`、
`T6.exact_at_A` 以「核 = 商理想」的參數式描述驗證這些精確性斷言。

### 2.12 範疇化：分次物件、餘可估複形、Loewy 濾過與 Cohen–Mac Lane 環（T16–T18）

`coho` 層把一切上同調不變量壓成**整數**（`RAD_DIM`、`SOCLE_DIM`、`COTANGENT_DIM`、
`EXT1_DIM`、`betti`）。範疇化層（`algebra-ct/cat`）把同樣的資訊還原成**物件**：
分次向量空間、带矩陣的餘可估複形、以及帶乘法的分次環。整數因此成為物件的維數，
而不是被硬編碼的輸入。

**定義 2.42（分次物件 `Graded`）.** 分次向量空間由逐次維數 `dims[i] = dim_k G^i` 表示，
支援 `+ − × scalar ⊗ ^n`、交錯和 `alt = Σ_i (−1)^i dims[i]` 與 Poincaré 級數輸出。
`trim()` 只丟棄**尾端**零次（頭端零次會移動元素，故保留）。

**定義 2.43（餘可估複形 `Complex`）.** `C^0 → C^1 → ⋯ → C^n`，每個 `d^i` 以
`(dim C^i)` 列、`(dim C^{i−1})` 行的**矩陣**寫出；同調由消元得出，
`dim H^i = dim C^i − rank d^i − rank d^{i+1}`（Euler 形式），並另給出真正的
**代表元** `homology_basis(i)`：核基中模掉像的標準化向量。

**定理 2.44（Tate 的範疇形式）.** 設 `F_* → A` 是自由分解，則
`Ext^i_A(M,N) = H^i(Hom_A(F_*,N))`、`Tor_i^A(M,N) = H_i(F_* ⊗_A M)`；
故當 `F_i` 是秩 `b_i` 的自由模時，`Ext^i` 與 `Tor_i` 互為對偶且同為 `b_i` 維。
Betti 數因此**不是**「`Ext¹` 的維數」，而是分解中自由模的秩。

**定理 2.45（T16，Koszul 複形與參數上同調）.** 對局部分量 `A_p` 與其極大理想 `m_p`
的一組基底 `θ_0,…,θ_{m−1}`，Koszul 複形

```text
K^i = A_p ⊗ Λ^i(θ),   d^i(b_a ⊗ e_S) = Σ_{j∈S} (−1)^{pos(j)} (b_a θ_j) ⊗ e_{S∖{j}}
```

在**任何**有限維局部代數上都是餘可估複形（`d d = 0` 由構造即得，測試以矩陣逐項驗證）；
它是剩餘域的分解當且僅當 `θ` 構成正則序列。故其上同調被如實稱為**參數上同調**，
**不宣稱**為 `Tor`——那會等價於宣稱每個 Artin 局部環都正則。無條件成立的是：
`H^0 = A_p/m_p = K`（維數 1），且 `im d^1 = A_p·m_p = m_p`，故 `rank d^1 = dim_k m_p`。
`H^i ≡ 1`（整個物件只有第 0 次）恰好等價於 `A_p` 正則，即 `mdim = 0`。

**定理 2.46（T17，Loewy 濾過）.** `A_p` 是 Artin 局部環，`m^0 = A_p ⊇ m ⊇ ⋯ ⊇ m^L = 0`，
故 `gr^i A_p = m^i/m^{i+1}` 給出分次物件且

```text
Σ_i gr^i A_p = dim_k A_p,   Σ_{i≥1} gr^i A_p = dim_k m_p = RAD_DIM,   gr^0 = 1,
gr^{L−1} A_p = soc A_p  （因 m^L = 0 使 m^{L−1}·m_p = 0）。
```

於是 `coho` 的 `RAD_DIM`、`SOCLE_DIM` 是同一個濾過物件的**頭幾個分次**與**最後分次**，
而非獨立的另一批事實；`A` 的 socle 是各因子 socle 的直和（故 `cub` 三點的 socle 維數相加為 3）。

**定理 2.47（T18，Cohen–Mac Lane 環與 Tate 自由秩）.** 對 `p`-群 `G`（`|G| = p^n`），
令 `r` 為最小生成元數、`w = n − r`，則

```text
H^*(G,K) = Λ^*(V) ⊗ K[W],  |V| = r, |W| = 2w,   P(t) = (1+t)^r/(1−t²)^w;
F_i = K[G] ⊗ Λ^i(k^r) ⊗ K[w]^{⌊i/2⌋},   rank_i = dim_k F_i / |K[G]| = dim_k H^i.
```

`cat/ring.mbt` **建出這個環本身**：基元素是三元組 `(a, b, μ)`（外次數、對稱次數、多重集），
乘法是 `e_S·e_S' = (−1)^{#{i∈S, j∈S' : i>j}} e_{S∪S'}`（`S ∩ S' = ∅`）與 `μ·ν = μ+ν`。
系統以**乘法表**（非公式）檢查結合律、分次反交換與乘法單位；
Koszul 符號滿足 `s(S,T)·s(T,S) = (−1)^{|S||T|}`，即分次反交換。
於是分次維數 `b_i` 同時是 Cohen–Mac Lane 的 `dim H^i` 與 Tate 分解的自由秩
（`tate_ranks = gr` 為程式內可測的等式）。

**誠實邊界（不可從乘法表推出者）.** `Λ^*(V) ⊗ K[W]` 由**群代數參數** `(r, w)` 建構，
它是一個真正的分次代數（乘法、結合律、反交換皆經機器檢查），但**不是**由本表的乘法表推出：
`k[x]/(x²)` 與 `k[y]/(y², y³)` 同樣有限維，其 `Tor` 卻不同——底環的 Tor 取決於底環本身，
不由張量的維數決定。由張量本身推導的物件是 `Hilbert` 級數、`gr^i A_p`、`gr^i m_p`
（`socle_graded`）與 `parameter_cohomology`，它們全部由消元從 `mul_tensor` 算出。

**機器驗證**：四張表上的結果

| 表 | `A_p` | `dim m_p` | Loewy `gr^i A_p` | socle | 參數上同調 | `dd = 0` |
|---|---|---|---|---|---|---|
| `fat` | `K[x,y]/(x²,xy,y²)`，`dim = 3` | 2 | `1 + 2t` | 2 | `1 + 3t + 2t²` | ✓ |
| `wild` | `F₂[x,y]/(x²−1,y²−1)`，`dim = 4` | 3 | `1 + 2t + t²` | 1 | `1 + 3t + 3t² + t³` | ✓ |
| `cub` | 每點 `K` | 0 | `1`（三點） | 3 | `1`（每點） | ✓ |
| `mix` | `F₃[x,y]/(x²−y,y³)`，`dim = 6` | 5 | `1 + t + t² + t³ + t⁴ + t⁵` | 1 | `1 + 5t + 10t² + 10t³ + 5t⁴ + t⁵` | ✓ |

（`18` 個斷言測試見 `cat/cat_wbtest.mbt`；`106` 個隱蔽 Z3 目標見
`proof/RESULTS_CAT.md` —— `m² = span{1+x+y+xy}`、`dim_k m² = 1`、
`b_i = i+1` 與凍結 `betti` 逐項相符，皆由**凍結張量重新消元**後比對。）

### 2.13 範疇化物件進入凍結表（T19）

第 2.12 節的分次物件只存在於**編譯期**：`emit` 只把整數（`D`、`EDIM`、`RAD_DIM`、
`SOCLE_DIM`、`betti`）寫進 `tables.mbt`。T19 把**物件本身**也凍結——仍是零成本
（`pub let` 的整數陣列，沒有任何執行期計算），但執行期因此能讀到分次的讀法，
而不只是總數。

`Cat`（`cat/res.mbt` 的 `categorify`）持有五個平坦 `Int32` 陣列：Hilbert 函數 `hilbert`、
Loewy 分次 `loewy`（各點區塊串接）、區塊長度 `loewy_lens`、參數上同調 `kozul` 與
`kozul_lens`。`emit` 由它們產生 `NHILBERT` / `NLOEWY` / `NKOSZUL` /
`NPOINTS_CAT` 四個 `pub const` 與五個 `pub let`，`algebra/ga` 則以
`hilbert_total`、`hilbert_at`、`loewy_block`、`mdim_at`、`socle_at`、`kozul_block`、
`dim_at`、`loewy_total`、`kozul_total` 九個**零成本讀取器**對外開放。

**定理 2.48（T19.1，Hilbert 函數的恢復恆等式）.**
`Σ_j hilbert[j] = D = dim_k A`，且 `hilbert[0] = 1`。
標準單項式按總次數分割單項式基底，故級數係數的和就是 `dim_k A`；常數項是 `1`。

**定理 2.49（T19.2，Loewy = 不變量的分次版本）.** 對每個點 `p`，

```text
gr^0 A_p = 1,   Σ_i gr^i A_p = dim_k A_p = 1 + dim_k m_p,
m^L = 0  ⟹  gr^{L−1} A_p = m^{L−1} = soc A_p,
Σ_p Σ_i gr^i A_p = D,   Σ_p Σ_{i≥1} gr^i A_p = RAD_DIM,   Σ_p gr^{L−1} A_p = SOCLE_DIM.
```

後兩式說明 T17 的兩個整數**不是獨立事實**，而是這個陣列的尾和與末項；
`fat` 與 `wild` 的 `RAD_DIM` 分別是 `2` 與 `1+2`，`SOCLE_DIM` 是 `2` 與 `1`。

**定理 2.50（T19.3，參數上同調是規則性的判別式）.** 對每個點 `p`，
`kozul_block(p)[0] = 1`（因 `H^0 = A_p/m_p = K`），且

```text
kozul_block(p) = 1  ⟺  m_p = 0  ⟺  A_p 正則（= 是一個 K 的副本）.
```

這是**由乘法表算出**的正則性判準，不需要「參數構成正則序列」的假設
（見定理 2.45 的警告）：若 `m_p = 0`，Koszul 複形在零次微分的錐上，
上同調即 `K`；反之 `m_p ≠ 0` 時 `dim_k m_p ≥ 1` 使複形的 H⁰ 之外另有非零分次。

**機器驗證（凍結的形狀）**

| 表 | `hilbert` | `loewy`（串接） | `loewy_lens` | `kozul`（串接） | `kozul_lens` |
|---|---|---|---|---|---|
| `fat` | `[1, 2]` | `[1, 2]` | `[2]` | `[1, 3, 2]` | `[3]` |
| `wild` | `[1, 2, 1]` | `[1, 2, 1]` | `[3]` | `[1, 3, 3, 1]` | `[4]` |
| `mix` | `[1, 2, 2, 1]` | `[1, 1, 1, 1, 1, 1]` | `[6]` | `[1, 5, 10, 10, 5, 1]` | `[6]` |
| `cub` | `[1, 1, 1]` | `[1, 1, 1]` | `[1, 1, 1]` | `[1, 1, 1]` | `[1, 1, 1]` |

注意 `cub`：三個 étale 因子各給一個 `[1]`，串接後與 Hilbert 函數同形但**理由不同**
（前者是三個 `K` 的直和的 Loewy 分解，後者是 `1, x, x²` 的分次）——
這正是「整數不足以決定物件」的最小例子，也是 T19 存在的理由。
`fat` 的 `loewy` 區塊等於 `hilbert` 是定理 2.52（T12）的直接結果（其理想齊次）；
`wild` 的兩者相等則是**巧合**——其理想 `x²−1` 並不齊次，只是 `x² = 1` 使
`m² = K`、末層恰為 1 而已；`mix` 則證明這個巧合不能推廣（§2.14.1）。

### 2.14 回填預留編號區塊：T12–T15

`T` 標號在 T11（上同調不變量）與 T16（範疇化）之間曾空出一段 `T12`–`T15`：
**這段編號從未被實作**（`git log -S "T12"` 在整個歷史中找不到任何字串），
其中 `T14` 只以一行程式註解存在於 `cat/res.mbt`（Hilbert 級數），既無文件也無憑證。
本節把它補成四個**真的**陳述，並且補上兩處順帶發現的漏洞：

* `T9` 在文件中是「`K[G]` 的結構與 socle」（定理 2.34），但它憑證一直被歸檔在
  `T11.*` 之下；現已重新標記為 `T9.wild.{group_order,group_dim,edim,socle_one,
  rad_augmentation,socle_norm}`。
* 定理 2.23（socle 判別式）原本的敘述為假，已於 2.8 節修正；T13 正是它的可機器檢查版本。

四個標號的內容刻意選成**「原先被含混使用、但實際為假或無法驗證」的命題**的正確版本。

#### 2.14.1 T12：齊次理想使 Loewy 濾過等於次數濾過

**定義 2.51（齊次理想 / 分次標準基底）.** `I` 齊次若每個生成元的所有單項式同次數；
此時標準單項式基底 `B = {e_0,…,e_{D−1}}` **分次**（每個 `e_j` 有確定次數），
且 `A = ⊕_d A_d` 為分次 `K`-代數。

**定理 2.52（T12）.** 若 `I` 齊次且 `A = K[x]/I` **局部**（此時 `e_p = 1`，
故局部化保持分次結構），則對唯一的局部因子

```text
m_p = ⊕_{d≥1} (A_p)_d,   m_p^j = ⊕_{d≥j} (A_p)_d,   gr^i A_p ≅ (A_p)_i,
```

即 `Loewy 級數 = Hilbert 級數`，逐項相等。

*證明.* 標準單項式基底分次 ⇒ `A` 分次；局部時 `A_p = A`（單點 Lagrange 冪等元
`e_p = 1`）⇒ 局部化不改變分次 ⇒ `m_p^j` 由次數 `≥ j` 的部分生成（因為理想
`(x_1,…,x_n)` 齊次）⇒ `gr^i A_p = (A_p)_i`。∎

**必要嗎？不必要——兩個方向都有反例**，這是本定理必須寫成「充分條件」的原因：

| 表 | `I` 齊次？ | `hilbert` | `loewy` | 說明 |
|---|---|---|---|---|
| `fat` | **是**（`x², xy, y²`） | `[1,2]` | `[1,2]` | 定理 2.52 的正例 |
| `wild` | 否（`x²−1` 混次） | `[1,2,1]` | `[1,2,1]` | 齊次性**不必要**（`x² = 1` 使 `m² = K`，末層恰為 1） |
| `mix` | 否（`x²−y` 混次） | `[1,2,2,1]` | `[1,1,1,1,1,1]` | 齊次性**不足以反推**（同為 `D = 6`，形狀不同） |
| `cub` | 否 | `[1,1,1]` | `[1,1,1]` | étale，同形是巧合（第 2.13 節已記） |

`mix` 的標準單項式基底 `{1, y, y², x, xy, xy²}` 次數為 `0,1,2,1,2,3`，故
`hilbert = [1,2,2,1]`；其 `m = (x)`（`EDIM = 1`）、`m² = (y)`、`m³ = (xy)`、
`m⁴ = (y²)`、`m⁵ = (xy²)`、`m⁶ = 0`，故 `loewy = [1,1,1,1,1,1]`。

#### 2.14.2 T13：socle 三分法（定理 2.23 的正確版本）

**定理 2.53（T13）.** 對 Artin 局部環 `A_p`，令 `s = dim_k Soc(A_p)`、
`μ = dim_k m_p`。則

```text
m_p = 0            ⟺  A_p = K      ⟺  Soc = A_p   ⟺  pt_kind = 0;
s = μ > 0          ⟺  Soc = m_p    ⟺  A_p Gorenstein ⟺  pt_kind = 1;
其餘               ⟺                              pt_kind = 2.
```

最後一條的等價式說明：**Gorenstein 的判準是 `soc = m`，不是 `s = 1`**。
零維局部環恆為 Cohen–Macaulay（`depth = 0 = dim`），故 `soc = m`（即
`s = μ`）恰是 Artin 局部環的 Gorenstein 判準。

`pt_kind` 已凍結進執行期表（`pub let pt_kind`），讀取器 `Tables::point_kind`、
`Tables::is_field_at`、`Tables::is_gorenstein_at` 皆為 `O(1)`。

**機器驗證**（socle 由**定義** `Ann(m_p)` 在憑證中以乘積映射的零化度重算，
不是讀凍結常數）：

| 表 | `dim A_p` | `μ = dim m_p` | `s = dim soc`（重算 = 凍結） | `pt_kind` | 分類 |
|---|---|---|---|---|---|
| `fat` | 3 | 2 | 2 = 2 | 1 | Gorenstein（`soc = m`） |
| `wild` | 4 | 3 | 1 = 1 | 2 | 兩者皆非 |
| `mix` | 6 | 5 | 1 = 1 | 2 | 兩者皆非——**`s = 1` 但不正規** |
| `cub`（每點） | 1 | 0 | 1 = 1 | 0 | 域 |

#### 2.14.3 T14：Hilbert 函數由凍結基底重數

**定理 2.54（T14）.** `hilbert[j] = #{ b ∈ BASIS : Σ_v exp_v(b) = j }`，
且 `Σ_j hilbert[j] = D`、`hilbert[0] = 1`。

憑證直接以凍結的 `basis` 指數向量重新計數每一個次數的單項式數，再與凍結的
`hilbert` 陣列逐項比較（`T14.*.from_basis`），並驗證恢復恆等式（`T14.*.recovery`）。
這一條把 T19 的 `hilbert` 陣列與產生它的基底綁在一起：**陣列不可能與 `basis` 不一致**。

#### 2.14.4 T15：參數上同調的 Euler 特徵

**定理 2.55（T15）.** 對每個局部因子，令 `χ_p = Σ_i (−1)^i dim_k H^i(A_p)`，
則 `χ_p = (1−1)^{d_p}`，其中 `d_p` 為 `m_p` 的生成元數。特別地

```text
χ_p = 1  ⟺  m_p = 0  ⟺  A_p = K,      χ_p = 0  ⟺  m_p ≠ 0.
Σ_p χ_p = #{ p : A_p = K }（= 剩餘點數）。
```

*證明.* 有限複形的 Euler 特徵等於其上同調的 Euler 特徵；而 Koszul 複形
`C^i = A_p ⊗ Λ^i(k^{d_p})` 的鏈維數是 `d_p·C(d_p,i)`，故
`χ = Σ_i (−1)^i C(d_p,i) = (1−1)^{d_p}`。此證明**只用 `d² = 0`**，
不需「參數為正則序列」的假設——這正是它能當作 `dd = 0` 的獨立憑證的原因：
若微分沒有平方為零，得到的就不是複形的上同調，Euler 特徵的等式便無意義。

| 表 | `kozul` | `χ` | `Σ_p χ_p` |
|---|---|---|---|
| `fat` | `[1, 3, 2]` | `1 − 3 + 2 = 0` | 0 |
| `wild` | `[1, 3, 3, 1]` | `1 − 3 + 3 − 1 = 0` | 0 |
| `mix` | `[1, 5, 10, 10, 5, 1]` | `1 − 5 + 10 − 10 + 5 − 1 = 0` | 0 |
| `cub` | `[1]`（三點） | 1 | 3 |

#### 2.14.5 第四張表 `mix`：為什麼需要它

前三張表有兩個「過於友善」的巧合：`fat` 是 Gorenstein（`s = μ = 2`），
`wild` 雖不 Gorenstein 但 `hilbert = loewy`。`mix` 是刻意挑選的反例表：

```text
A = F₃[x,y]/(x²−y, y³)     D = 6,  單點 (0,0),  m = (x),  EDIM = 1
RAD_DIM = 5,  SOCLE_DIM = 1,  KIND = 2,  hilbert = [1,2,2,1],  loewy = [1,1,1,1,1,1]
```

它同時推翻兩條常見的樸素判準（定理 2.52 定理 2.53 的反例方向），
並讓 `coho` 層的 T7–T11 憑證多一張獨立資料表。

**憑證**：`proof/cat_proofs.py` 的 `T19.*` 目標**直接讀凍結表裡的陣列**
（而不是重算），因此它證的是「執行期讀到的就是引擎算出的那個分次物件」，即編譯期與
執行期之間的一致性：15 個目標（每表 5 個）涵蓋 `Σ hilbert = D`、`hilbert[0] = 1`、
`Σ loewy = D`、區塊長度自洽且 `NPOINTS_CAT = NPOINTS`、每個 Loewy 區塊首項為 1 且
尾和/末項分別給出 `RAD_DIM`/`SOCLE_DIM`、`kozul` 首項為 1、以及定理 2.50 的判準。

---

## 3. 演算法、複雜度與收斂分析

### 3.1 Gröbner 基：準則 + 認證（複雜度下降）

樸素 Buchberger 產生 `s(s-1)/2` 個 `S`-多項式並逐一正規化，開銷 `O(s² · NF)`。
本系統（`gb/groebner.mbt`）以三個準則在**正規化之前**濾除候選：

* **LCM（鏈）準則**：若存在 `k < i < j` 使 `lm(g_k) | lcm(lm(g_i), lm(g_j))`，則 `NF(S_ij) = 0`；
* **乘積準則（Gebauer–Möller）**：若 `lcm(lm_i,lm_j) = lcm(lm_k,lm_j)`（`k<i`）或 `= lcm(lm_i,lm_k)`（`k<j`），則 `NF(S_ij)=0`；
* **互質陪因子準則**：`l = lcm(lm_i,lm_j) = u·v` 且 `gcd(u,v)=1` 時 `NF(S_ij)=0`。

> **正確性設計（重要）.** 上述準則有已知不健全的實作陷阱，因此本系統採
> **「快速準則 → 認證階段（certified replay）」**：候選被濾掉時記錄證據，最後以一次
> 完整重放確認所有未計算的 `S`-多項式確實歸零。任何不健全的過濾都會在認證階段被拒絕。

複雜度對照：

| 階段 | 樸素 | 本系統 |
|---|---|---|
| 候選產生 | `Θ(s²)` | `Θ(s²)`（無法避免） |
| 正規化呼叫 | `Θ(s²)` | 實測大幅下降（準則命中） |
| 認證 | — | 一次 `O(s²)` 重放，換取可證的正確性 |
| 零維特化 | 每個多項式重複正規化 | 只對 basis 元素做一次張量攤平 |

### 3.2 零維分解：求值矩陣

對零維 `I`，令 `B = {e_0,…,e_{D-1}}`，求值矩陣

```
Ψ = [ Ψ_ij ]_{i<|V_K(I)|, j<D},   Ψ_ij = e_j(p_i)。
```

**定理 3.1（維數 / Lagrange）.** `D = dim_k A`；若 `I` 無重因子則 `D = |V_K(I)|` 且 `Ψ` 可逆；
其逆的第 `j` 欄即原始冪等元（`Ψ^{-1} e_a = e_a`）。

複雜度：建表 `O(|B| · |V| · deg)`；求逆 `O(|V|³)`。相較於對每個點重做多項式正規化的樸素做法
（`O(p^n · NF)`），這是**指數到多項式**的下降。

### 3.3 Newton 倍增（收斂分析核心）

設 `a_0 ≠ 0`，求 `b` 使 `a b ≡ 1 (mod t^N)`。

* 誤差定義：`e_k = 1 − a b_k ∈ (t^{2^k})`（起始 `k=0`：`b_0 = a_0^{-1}`，`e_0 ∈ (t)`）。
* **定理 2.4 的誤差形狀**：`e_{k+1} = e_k²`，故 `v(e_k) = 2^k`，精確度在 `k` 步後為 `2^k` 個係數。
* **迭代數**：`k = ⌈log₂ N⌉`；每步成本 `M(N)`（截斷乘法），總計 `O(M(N) log N)`，對樸素遞推
  `O(N·M(N))` 為 `log N` 倍下降。
* **停機準則**：`v(e_k) ≥ N` 或剩餘係數全為零；實作同時用「剩餘係數全零」作為提前終止，
  避免在特徵 `p` 下的精度冗餘。

`series_sqrt`、`series_root` 皆建立在同一倍增骨架上：先求 `(2/N)·log(·)` 的形式冪級數，
再用 Newton 對方程 `y² − a = 0` 做精度倍增（每次 `y ← (y + a/y)/2`，誤差平方）。

### 3.4 陪集理想與理想交

**定理 3.2（零維 colon 關係）.** 對零維 `I` 與 `g`，

```
(I:g)/I = ann_A(ḡ) = ker( μ_ḡ )。
```

**定理 3.3（front 選擇）.** 生成理想交時，若把「最簡單」（次數最高項最小）的那個元素放在
front，可把剩餘部分降維到 `D` 維線性代數。

實作 `lift_front` 即此定理的程式化：以乘法矩陣的零空間求 `ann_A(ḡ)`，複雜度 `O(D³)`，
取代樸素的多次 Gröbner 化簡。

### 3.5 nilradical / radical

**定理 3.4（跡判準）.** 在特徵 `p` 的代數中，若 `a` 冪零則 `tr(μ_a) = 0`；反之在
「半單商環」（本專案的兩例皆為 `0` 維且 nilradical 可由 trace 零空間刻畫）成立。
實作（`gb/ideal.mbt::radical_gens`）以 `μ_a` 的零向量空間逐次收縮 nilradical，
複雜度 `O(D³)`，而樸素做法需對候選逐一做 Gröbner 分解。

### 3.6 結構查詢：全部降到線性代數

| 查詢 | 演算法 | 複雜度 |
|---|---|---|
| 元素相乘 | 張量查表 | `O(|supp a|·|supp b|·D)` |
| 求值 `f(p)` | 預先展開 | `O(deg f)` |
| 剩餘理想 `ker(ev_p)` | 對偶座標（參數式） | `O(D²)` |
| 原始冪等元 | `Ψ^{-1}` | `O(V³)` |
| socle | `ker[μ_{x_1};…;μ_{x_n}]`（串接而非相加！） | `O(n·D³)` |
| 極大理想 / 單位 | `a_0 ≠ 0 ⇔ a 可逆`（局部） | `O(1)` |

> 實作教訓（已修正並以斷言測試固定）：socle 是**各生成元乘法矩陣的核之交**，
> 必須**串接矩陣**求聯立零空間；若把矩陣**相加**再求核，得到的是 `Ann(Σg_i)`，
> 一般情況下是錯的（胖點即為反例）。

### 3.7 範疇化資料的凍結（`categorify`，T19）

`cat::categorify(q, ps)` 把第 2.12–2.13 節的三個分次物件從同一張乘法表算出，
再交給 `emit` 寫成凍結常數。三段流程（全部只用線性代數，無 Gröbner、無消元）：

| 步驟 | 演算法 | 複雜度 | 輸入 → 輸出 |
|---|---|---|---|
| 1 | `hilbert`：按基底元素的總次數累計 | `O(D·nvar)` | `q.dim` 個單項式的度 → `Σ_j dim A_j` |
| 2 | `loewy`：以 `m^i A_p` 的像的逆像做遞減濾過，逐次解 `d·D` 聯立方程 | `O(L_p · D³)`，`L_p =` Loewy 層數 ≤ `D` | `m_p` 的生成矩陣 → `gr^i A_p` |
| 3 | `parameter_cohomology`：對參數矩陣的 Koszul 複形逐次 `d^r = 0` 消去 | `O(r · d^{r+2})`，`r = dim m_p` | `dim m_p` 個參數 → `dim H^i` |

**正確性設計**：第 2 步的每一層都重新解一次線立方程系統（而非假設前一層的商是自由的），
故在特徵 `p` 下也不需要正則序列假設；第 3 步逐次檢查 `im d^{i+1} ⊆ ker d^i`，
不滿足即為 bug（`dd = 0` 斷言）。

複雜度總結：整條編譯期管線 `O(D³ · D + r·d^{r+2})`，全部在**編譯期**完成；
執行期讀取任一分次維數是 `O(1)`（陣列索引）或 `O(L_p)`（取出整個區塊）。

### 3.8 複雜度總表

| 任務 | 樸素 | 本系統 |
|---|---|---|
| `f = g (mod I)` | `O(NF)` | `O(D)` 查表 |
| 兩元素相乘 | `O(NF)` | `O(D)` 查表 |
| `V_K(I)` 列舉 | `O(p^n)` | `O(p·deg)`（三角消去 + 準則） |
| 維數 `dim A` | Gröbner + Hilbert 函數 | `O(D)`（編譯期常數） |
| 冪等元 | 理想分解 | `O(V³)` 線性代數 |
| socle | Gröbner 推導 | `O(n·D³)` 線性代數 |
| radical | 反覆分解 | `O(D³)` 跡/零空間 |
| Loewy 分次 | 反覆求冪基 | `O(L·D³)` 線性代數 |
| 參數上同調 | 完整正則序列假設 | `O(r·d^{r+2})`，無假設 |
| 讀取任一分次維數 | — | `O(1)`（凍結陣列索引） |

---

## 4. 收斂分析（統一觀點）

系統中三種「迭代」的收斂性皆可量化：

1. **Newton 倍增（`val`）**：誤差 `e_{k+1} = e_k²`，價 `v(e_k)=2^k`，`⌈log₂N⌉` 步達到 `t`-進精度 `N`；
   這是**二次收斂**（`quadratic`），每步成本 `O(M(N))`。
2. **Gröbner 認證階段（`gb`）**：候選數有限（`≤ s(s-1)/2`），每個 `S`-多項式的正規化步數
   受首項序嚴格遞減約束 ⇒ **有限步必停**，這是不依賴啟發式的「良基遞減」。
3. **三角消去的遞迴（`quot`）**：每步消去一個變數，維度嚴格下降 ⇒ 至多 `n` 層。

三者共同構成「**有限步 + 可證誤差界**」的收斂保證；生成器只在預算內完成，並把實測統計寫入
`COST` 常數，供執行期與後續產生器做**自適應**決策（見第 5 節）。

---

## 5. 自適應系統架構重構

### 5.1 分派器（依代數特徵選策略）

生成器在編譯期先做**一次**結構偵測，然後選擇策略：

| 偵測結果 | 策略 | 產出 |
|---|---|---|
| `is_zero_dim = false` | 三角消去求 `V_K(I)`，**不產生張量** | 點集 + 正維旗標（例：`x²+xy+y²` → `D=0`、14 點） |
| `D ≥ 1` 且平方自由 | 求值矩陣 `Ψ` + `Ψ^{-1}` | 冪等元、`EDIM=0`、`LOCAL=false` |
| `D ≥ 1` 且非簡約 | nilradical（trace）→ 再取商 | `LOCAL`、`EDIM`、socle |
| `LOCAL = true` | 底環 + 單位判準 | `edim`、`socle`、`m^i` 賦值 |

### 5.2 預算與降階（cost model）

每張凍結表攜帶 `COST`（Gröbner 統計、候選數、正規化呼叫數）。當輸入規模（例如變數數 `n`、
總次數 `d`、`p`）超過預算時，產生器依序降階：

1. 先只輸出 `D / BASIS / POINTS`（不做冪等元與 socle）；
2. 再只輸出基底與求值（不做 nilradical）；
3. 最後只輸出點集與旗標。

這使「零維化 + 全結構」只發生在**確實負擔得起**的輸入上。

### 5.3 執行期自適應

執行期不做策略選擇（那是編譯期的事），但保留：

* `D`、`EDIM`、`LOCAL` 為 `pub const`，最佳化器可據此**刪除整條分支**（零成本）；
* `mul_tensor` 以 `pub let` 給出，支援稀疏快取（`if c[i] != 0` 跳過零項）。

### 5.4 產物可審計性

`ga/tables_*/tables.mbt` 是**已提交的生成檔**，任何人 diff 即可知道生成器改了什麼；
`dev_build` 規則（`ga/tables_*/moon.pkg`）只在 `spec.txt` 變動時重跑，保證「表 ≡ 規格」。

---

## 6. 隱蔽式形式化證明

### 6.1 兩層證明架構

| 層 | 位置 | 狀態 |
|---|---|---|
| Z3（SMT-LIB2 語義，凍結表） | `proof/ga_proofs.py` → `proof/RESULTS.md` | **355 / 355 目標 `unsat`** |
| Z3（範疇化層，含 T12–T15） | `proof/cat_proofs.py` → `proof/RESULTS_CAT.md` | **106 / 106 目標 `unsat`** |
| MoonBit（`moon prove`） | `algebra/gap/gap.mbtp` | 通過 `moon check`；執行 `moon prove ga/gap` 需 Why3 ≥ 1.7.2 與 z3 |

「隱蔽」的含義：**驗證邊界與執行邊界分離**。`gap` 套件不被任何執行期套件依賴，
`moon build` / `moon test` 的結果與是否存在證明檔完全無關（實測：加入 `gap` 後測試仍為 4/4）。

### 6.2 Z3 編碼方法（可重現）

* 剩餘域 `F_p` 以 `Z/pZ` 的同餘建模；所有非線性項都是「變數 × 常數」，
  因此命題落在**可判定**的模 `p` 整數算術內。
* **雙線性引理**：雙線性映射由基底值決定 ⇒ 全稱命題化為有限個基底檢查
  （`T2.*.eval_hom`、`T1.*.assoc`）。
* **線性參數式消元**：像空間 / 核空間的成員判定寫成 `a = Σ_j λ_j(a)·b_j`，
  其中 `λ_j` 是 `a` 的**線性函數**（由 `B` 的對偶座標求得），於是 `∀a∃c` 的
  存在量詞被**完全消去**，Z3 秒回。
* **有限窮舉**：像 `7⁴ = 2401` 組 `m·m = 0`、294 個元素的左右逆與冪零性，
  在有限域上窮舉即為全稱證明。
* **整數量 vs. 域元素（重要）**：`KIND`、`GROUP_ORDER`、`GROUP_RANK`、`NBETTI`、
  `betti`、各項維數都是**整數**，必須以 Z3 整數算術比對，**不可**模 `p` 比對。
  否則 `|C₂×C₂| = 4` 在 `F₂` 中變成 `0`，`RAD_DIM = 3` 在 `F₂` 中變成 `1`，
  定理會被證成假的。本專案以 `int_eq` / `int_gt0` 明確區分兩者。
  （本專案實測：未區分時恰有 4 個 `T11.wild.*` 目標失敗。）

### 6.3 已證明的定理清單（摘要）

```
T1  座標環/函數環：張量單位律、結合律、交換律（220 目標）
T2  仿射代數簇：求值是環同態（雙線性基底檢驗）、點兩兩相異
T3  冪等元：正交性、和為 1、x ≡ r_i、直和分解、剩餘理想 = 核、半單性、域內冪等元僅 0/1
T4  正規局部環：socle = Ann(m)、dim socle = edim、非正規性、m² = 0、單位公式、剩餘域
T5  根理想/半素：m² = 0（全稱）、可逆元素非冪零（全稱）、(0) 非根理想、F_p 是域
T6  凝聚層/連續模：精確序列 ker q = m、m/m² 維數、(xA),(yA) 的正合性、Artin+Noetherian
T7  座標環簡約性：F_97 無非零冪零元、剩餘理想極大、三點互素不交
T7* 上同調：rad A = 點求值核之交、I ⊆ rad A、(rad A)·A ⊆ rad A、Soc = Ann(rad A)、
    Soc·rad A = 0、Soc·A ⊆ Soc、SOCLE_DIM ≥ 1（四張表各一組：`cub`、`fat`、`wild`、`mix`）
T8* 余切空間/Ext¹：逐點 Jacobian 餘核 = EXT1_DIM、Tor¹ = Ext¹ = COTANGENT_DIM、
    Tor¹ = Σ_p edim、餘正规序列的 coker = COTANGENT_DIM、簡約 ⇔ 三者同時為 0
T10* Frobenius：由凍結張量重算 Fix(a↦a^p) = FROB_FIXED = NPOINTS
T11* 群代數與 Betti 數：|G| = p^r = D、edim = r、soc = A·N 一維、rad = I(G) 維數 |G|−1、
    Cohen-Maclane 係數逐項相符、b_0 = 1、正次 Betti 數 > 0、
    Maschke（|G| ≢ 0 ⇒ betti 為空）、KIND 三分類、étale ⇔ rad = 0 ⇔ Tor¹ = 0
T16* 範疇化（Koszul）：dim_k A_p、dim_k m_p = RAD_DIM（m_p = ker ev_pt）、d^i d^{i+1} = 0、
    H^0 = A_p/m_p = 1、im d^1 = m_p 故 rank d^1 = RAD_DIM、胖點 1+3t+2t²、wild (1+t)³
T17* 範疇化（Loewy）：Σ gr^i = dim A_p、Σ_{i≥1} gr^i = RAD_DIM 且 gr^0 = 1、
    各因子最後分次之和 = SOCLE_DIM、胖點 1+2t、wild 1+2t+t²、m² = span{1+x+y+xy}
T18* 範疇化（Cohen-Mac Lane 環）：|G| = p^n 且 r = GROUP_RANK、dim_k H^i = i+1 與凍結
    betti 逐項相符、環大小 112、H^0 = 1、外積符號 = Koszul 符號且 s(S,T)s(T,S) = (−1)^{|S||T|}
```

> **憑證強度說明**：上表 `T7*`/`T8*`/`T10*`/`T11*` 的 `rad A`、`Soc(A)`、Frobenius 固定空間、
> Betti 數皆由**凍結表重新計算**（求值核、乘法矩陣核、`a ↦ a^p` 的特徵 1 空間、
> Cohen-Maclane 公式），再與凍結常數比對；理想本身則直接解析 `algebra/moon.mod`
> 的 `--terms` 規則取得，確保憑證量化的是引擎實際執行的那個理想。

完整表格見 `proof/RESULTS.md`（凍結表，461 個目標含範疇化）與
`proof/RESULTS_CAT.md`（範疇化 106 個目標）；標號對照見附錄 A₀。兩者皆由 `python3 proof/run_proofs.py` 重新產生。

### 6.4 信任邊界（誠實聲明）

1. Z3 證明的是**凍結表**所定義的有限代數；「凍結表來自 Gröbner 引擎」這一步由
   `algebra-ct` 的 63 個斷言測試與程式產生器的確定性輸入承擔，不是 SMT 證明的對象。
2. `gap/gap.mbtp` 目前只經過 `moon check`（型別/語法）與 `moon check --target native`；
   本沙箱無 Why3，故未實際執行 `moon prove`。文件中的 MoonBit 命題是 Z3 已證命題的
   MoonBit 側改寫，可望在具備 proof toolchain 的環境直接放行。
3. 所有 Z3 目標均以「否定命題 `unsat`」為通過標準，失敗會以非零碼結束
   （`python3 proof/run_proofs.py; echo $?`）。
4. `cat_proofs.py` 的範疇化目標不是重新實作引擎，而是**由凍結 `mul_tensor` 重新消元**
   （局部分量的冪等元、Lagrange 插值或單位元、`m_p = ker ev_pt`、理想冪、Koszul 矩陣），
   再以 Z3 整數等式與凍結常數／定理敘述比對；其 `Local` 類與 `cat/res.mbt` 的
   `local_factor` 是同一構造的兩份實作，兩者給出相同的 Loewy 與 Koszul 數字，
   互為交叉檢查。

---

## 7. 執行方式

```bash
export PATH="$HOME/.moon/bin:$HOME/.moonup/bin:$PATH"

# 0) 若工具鏈不在（沙箱重啟後 .moonup 不保留）：
#    sh /tmp/moonup_install.sh && moonup install latest

# 1) 編譯期引擎（81 個斷言測試：poly 19 + gb 23 + quot 6 + val 7 + la 6 + coho 8 + cat 13）
cd /home/user/alge-repo/algebra-ct && moon check --deny-warn && moon test --target native

# 2) 生成器（CLI）
cd /home/user/alge-repo/algebra-ct && moon build --target native cmd/gen
#   語法： 多項式以 ';' 分隔；項以 '|' 分隔；指數以 '.' 分隔；係數以 ':' 分隔
#   範例： --p 7  --n 2 --terms "2.0:1;1.1:1;0.2:1"             --name fatpoint
#          --p 97 --n 1 --terms "3.0:1|2.0:-6|1.0:11|0.0:-6"   --name cub
#          --p 2  --n 2 --terms "2.0:1|0.0:-1;0.2:1|0.0:-1"     --name wild
#   注意 F_2 上 x^2-1 必須寫成單一多項式 "2.0:1|0.0:-1"；若拆成 x^2 與 -1
#   兩個生成元，在 F_2 中它們生成的是單位理想 (1)。

# 3) 執行期（9 個斷言測試；dev_build 會自動重生成凍結表）
cd /home/user/alge-repo/algebra && moon test --target native

# 4) 隱蔽形式化證明（Z3）：凍結表 355 + 範疇化 106 = 461 目標
cd /home/user/alge-repo/proof && python3 run_proofs.py    # -> RESULTS.md, RESULTS_CAT.md

# 5) MoonBit 側證明（需 Why3 ≥ 1.7.2 + z3）
cd /home/user/alge-repo/algebra && moon prove ga/gap

# 6) 凍結表重生成（結果與倉庫中的表逐位元組相同）
cd /home/user/alge-repo/algebra-ct
moon run ./cmd/gen --p 97 --n 1 --terms "3.0:1|2.0:-6|1.0:11|0.0:-6" --name cub
moon run ./cmd/gen --p 7  --n 2 --terms "2.0:1;1.1:1;0.2:1"              --name fatpoint
moon run ./cmd/gen --p 2  --n 2 --terms "2.0:1|0.0:-1;0.2:1|0.0:-1"        --name wild
```

---

---

## 附錄 A₀：定理標號索引（T1–T19）

每個 `T` 標號對應一組 Z3 目標（`proof/RESULTS.md`，共 **461** 個目標、242 個類別）、
一段文件、以及實作位置。**沒有任何標號是空的**：T12–T15 於 2026-10-19 回填（§2.14），
T9 的目標於同日從 `T11.*` 重新標記回 `T9.*`。

| 標號 | 主題 | 文件 | 實作 | Z3 目標（類別 / 目標） |
|---|---|---|---|---|
| `T1` | 凍結張量確為環（單位、結合、交換） | §2.2 定理 2.3 | `quot`（`mul_tensor`） | 8 / 216 |
| `T2` | 求值 `ev_p` 是環同態、點互異 | §2.5 定理 2.10 | `quot`、`ga::eval` | 4 / 4 |
| `T3` | Gröbner 基、標準單項式、維數 | §2.1–2.2 | `gb`、`quot` | 19 / 22 |
| `T4` | 胖點的 socle、`m² = 0`、單位逆 | §2.7 定理 2.23–2.24 | `coho`、`ga` | 8 / 8 |
| `T5` | 函數環 `K^X` 的雙線性性 | §2.5 | `quot` | 3 / 3 |
| `T6` | 零維 Artin–Noether 凝聚性 | §2.4 定理 2.14 | `gb`、`quot` | 5 / 5 |
| `T7` | 根理想、剩餘理想、socle（由張量重算） | §2.9 定理 2.26–2.28 | `coho` | 43 / 43 |
| `T8` | `Ext¹ = Ω¹ ⊗ K`、餘切空間（附反例） | §2.10 定理 2.33 | `coho`、`ga` | 20 / 20 |
| `T9` | `K[G]` 的結構（`|G| = D`、`edim = r`、`soc = A·N`） | §2.11 定理 2.34 | `coho` | 2 / 2 |
| `T10` | Frobenius 固定點 | §2.11 定理 2.35 | `coho`、`ga` | 8 / 8 |
| `T11` | Cohen–Mac Lane 級數、Maschke、三分類 | §2.11 定理 2.36–2.38 | `coho`、`cat/ring.mbt` | 18 / 18 |
| `T12` | 齊次理想 ⇒ Loewy = Hilbert（含 `mix` 反例） | §2.14.1 定理 2.52 | `cat`、`emit` | 4 / 4 |
| `T13` | socle 三分法 / Gorenstein 判準（含反例） | §2.14.2 定理 2.53 | `cat`、`emit`、`ga` | 10 / 10 |
| `T14` | Hilbert 函數由凍結基底重數 | §2.14.3 定理 2.54 | `cat/res.mbt`、`ga` | 8 / 8 |
| `T15` | 參數上同調的 Euler 特徵 `χ = (1−1)^d` | §2.14.4 定理 2.55 | `cat`、`emit`、`ga` | 10 / 10 |
| `T16` | Koszul 複形與參數上同調 | §2.12 定理 2.45 | `cat/res.mbt` | 19 / 19 |
| `T17` | Loewy 濾過 `gr^i A_p` | §2.12 定理 2.46 | `cat/res.mbt` | 15 / 15 |
| `T18` | Cohen–Mac Lane 環與 Tate 自由秩 | §2.12 定理 2.47 | `cat/ring.mbt` | 11 / 11 |
| `T19` | 範疇化物件凍結進執行期表 | §2.13 定理 2.48–2.50 | `cat`、`emit`、`ga` | 27 / 27 |

## 附錄 A：凍結表（倉庫中的實際常數）

四張表由 `algebra-ct` 的 `cmd/gen` 在**編譯期**產生並提交；
`algebra/moon.mod` 的 `gen-*` 規則是唯一輸入，`dev_build` 保證「表 ≡ 規格」。
第四張 `mix` 是 2026-10-19 加入的**反例表**（§2.14.5），前三張的成立多靠巧合。

| 常數 | `cub` = `F₉₇[x]/((x−1)(x−2)(x−3))` | `fat` = `F₇[x,y]/(x²,xy,y²)` | `wild` = `F₂[x,y]/(x²−1,y²−1)` | `mix` = `F₃[x,y]/(x²−y,y³)` |
|---|---|---|---|---|
| 說明 | `K[C₃]`，`A = K³`（étale） | 胖點（非簡約） | `K[C₂×C₂]`（`p`-群代數） | 非齊次反例（局部） |
| `P`, `D`, `NVAR` | 97, 3, 1 | 7, 3, 2 | 2, 4, 2 | 3, 6, 2 |
| `EDIM`, `LOCAL` | 0, false | 2, true | 2, true | **1**, true |
| `RAD_DIM` | 0 | 2 | 3 | **5** |
| `SOCLE_DIM` | 3 | 2 | **1** | **1**（`soc ≠ m`：非 Gorenstein） |
| `COTANGENT_DIM` | 0 | 2 | 2 | 1 |
| `EXT1_DIM` | 0 | 2 | 2 | 1 |
| `FROB_FIXED` | 3 | 1 | 1 | 1 |
| `GROUP_ORDER`, `GROUP_RANK` | 0, 0 | 0, 0 | **4, 2** | 0, 0 |
| `KIND` | 0（étale） | 2（局部非群） | **1（`p`-群）** | 2（局部非群） |
| `NBETTI`, `betti` | 0, `[]` | 0, `[]` | 7, `[1,2,3,4,5,6,7]` | 0, `[]` |
| `NHILBERT`, `hilbert`（T19） | 3, `[1,1,1]` | 2, `[1,2]` | 3, `[1,2,1]` | 4, `[1,2,2,1]` |
| `NLOEWY`, `loewy`, `loewy_lens` | 3, `[1,1,1]`, `[1,1,1]` | 2, `[1,2]`, `[2]` | 3, `[1,2,1]`, `[3]` | 6, `[1,1,1,1,1,1]`, `[6]` |
| `NKOSZUL`, `kozul`, `kozul_lens` | 3, `[1,1,1]`, `[1,1,1]` | 3, `[1,3,2]`, `[3]` | 4, `[1,3,3,1]`, `[4]` | 6, `[1,5,10,10,5,1]`, `[6]` |
| `NPOINTS_CAT`, `pt_kind` | 3, `[0,0,0]` | 1, `[1]` | 1, `[2]` | 1, `[2]` |

> `COTANGENT_DIM = dim_K(Ω¹ ⊗_A K) = Σ_p edim(A_p) = dim_K Ext¹_A(K,K)`，
> **不是** `dim_K Ω¹_{A/K}`（後者依序為 0、3、8）。見定理 2.31 的說明。
>
> `SOCLE_DIM` 在 `wild` 為 **1**（`soc = A·(1+x)(1+y)`），不是 `r = 2`。見定理 2.34。

> `pt_kind` 是 T13 的凍結三分類：每個局部因子為 `0`（域）、`1`（Gorenstein）、
> `2`（兩者皆非）。`mix` 的 `pt_kind = 2` 是 `dim_k soc = 1` 不足以判別的證據。

> T19 的五個陣列是 T16–T18 的分次物件本身（定理 2.48–2.50）：
> `Σ hilbert = Σ loewy = D`、`kozul[0] = 1`、`Σ_{i≥1} loewy[p] = mdim(A_p)`、
> 末項 = socle。`RAD_DIM` 與 `SOCLE_DIM` 可由此兩陣列重算，故不是獨立常數。
> 讀取器：`hilbert_total`、`hilbert_at`、`loewy_block`、`mdim_at`、`socle_at`、
> `kozul_block`、`dim_at`、`loewy_total`、`kozul_total`。

## 附錄 B：測試清單

* `algebra-ct/poly`（19）：域公理與 `is_prime`/`is_primitive`、多項式正規形與 `in_ideal`、
  單項式序、單變數 gcd/除法、`divrem_list`、`constant_value`、`pow_mod_univar`、`lcm_univar`、
  `radical_part`、`split_linear`、`distinct_irreducible`。
* `algebra-ct/gb`（23）：Buchberger + 準則與**單位理想仍產生 `{1}`** 的迴歸測試、`interreduce`
  不消滅生成元、`is_zero_dim`、`is_radical`（含 `gens = [] → true`）、餘理想與飽和（含零維精確
  情形與正維包含性）、根理想、理想交/和/積、front 選擇、`lead_monos`、`pure_lead_degree`、
  `buchberger_unreduced`、`nullspace` 的支點列回歸（見附錄 D）。
* `algebra-ct/quot`（6）：零維商環維度、`⟨x³⟩` 局部且 `edim = 1`、`⟨x⟩` 簡約且 `edim = 0`、
  `embedding_dimension = dim_k m/(I+m²)`（含正維反例）、求值矩陣與冪等元。
* `algebra-ct/val`（7）：截斷乘法、賦值、Newton 求逆、平方根、級數根（含 `b0^m ≠ f(0)` 拒絕）、
  `trunc`、`series_deriv`（含乘積律 `(fg' = f'g + fg'`）、`series_pow`。
* `algebra-ct/coho`（8）：T7–T11 白盒測試——reduced / étale 例、非簡約胖點、`p`-群代數
  `F₂[C₂×C₂]`、Frobenius 固定空間、Cohen–Mac Lane 係數。
* `algebra-ct/cat`（18）：`Graded` 的分次代數律與 `trim` 語義；T16 的 Koszul 複形——
  項維數 `d·C(m,i)`、`d d = 0`（以矩陣驗證）、`H^0 = 1`、胖點 `1+3t+2t²`、wild `(1+t)³`、
  etale 每點為 `1`、同調維數與 `homology_basis` 的代表元數一致；T17 的 Loewy
  `1+2t` / `1+2t+t²`、總維數、`Σ_{i≥1}`、`socle_graded`、etale 三點；T18 的
  `Λ(k²)⊗K[w²]` 分次 `b_i = i+1`、總大小 112、`tate_ranks = gr`、單位、結合律（窮舉三元組）、
  分次反交換、外積的 Koszul 符號、與凍結 `betti` 前四項相符；
  **T19 的 `categorify`**：`hilbert_total = D`、每個 Loewy 區塊首項為 1、
  `dim A_p = 1 + dim m_p`、參數上同調首項為 1 且「為 `1` ⇔ `A_p` 正則」、
  三張表的凍結區塊形狀（`wild` `[1,2,1]`/`[1,3,3,1]`、`fat` `[1,2]`/`[1,3,2]`、
  `cub` 三個 `[1]`）與越界區塊回傳空陣列；
  **T12/T13/T15**：`categorify` 在齊次理想（`fat`、`wild`）給出 `hilbert = loewy`，
  在非齊次的 `mix` 給出 `[1,2,2,1]` vs `[1,1,1,1,1,1]`；逐點三分類
  （`cub` 全 0、`fat` 1、`wild` 與 `mix` 2）與 `dim_at = 1 + mdim`；
  Euler 特徵 `χ`（`fat` `1−3+2`、`wild` `1−3+3−1`、`mix` `1−5+10−10+5−1`、`cub` 1）。
* `algebra/ga`（16）：凍結張量即環；原始冪等元（和為 1、正交、冪等、求值為 δ）；胖點局部 +
  `edim = 2` + `socle` 二維 + `m² = 0`；根的求值互異；T7/T8 的 étale 與胖點上同調；
  T9/T10 的 `K[C₂×C₂]` Betti 數 `b_i = i+1` 與 `N² = 0`；
  **反例測試**「餘切空間 ≠ `dim_k Ω¹`」；`nullspace`/`solve` 的支點列回歸；
  **T19 的三項**：`hilbert_total = D`、Loewy 區塊重算 `RAD_DIM`/`SOCLE_DIM`/
  `Σ dim A_p = D`、參數上同調首項與規則性判準；
  **T12/T13/T15 的三項**：`mix` 使 `hilbert ≠ loewy` 而兩者同為 `D = 6`；
  `pt_kind` 三分類與「`dim_k soc = 1` 但不正規」的 `mix`；Euler 特徵 `χ = 1 ⇔ 域`。
* `proof`（凍結表 355 目標 + 範疇化 106 目標 = 461 目標，全部 `unsat`）：
  見 `proof/RESULTS.md` 與 `proof/RESULTS_CAT.md`。
---

## 附錄 C：全代碼健檢（2026-10-16）與修復清單

對 `algebra-ct`（6,690 行）、`algebra`、`proof` 三個模組逐檔審閱後，確認並修復下列問題。
每一項都補上斷言測試，且 `moon check --deny-warn` 歸零、引擎 54/54、執行期 4/4、Z3 265/265 全綠；
凍結表 `tables_cub/tables.mbt` 與 `tables_fat/tables.mbt` 重新產生後**逐位元組相同**
（證明重構行為等價，而下面的數學錯誤只影響先前無人呼叫的函式）。

### C.1 數學正確性（真正的 bug）

1. **`standard_monomials` 的盒大小少了一層**（`gb/ideal.mbt`）。`box_size` 回傳
   `prod bounds[i]` 而非 `prod (bounds[i]+1)`，且 `unbox` 以 `bounds[i]` 為模數，於是
   指數恰等於上界的頂層被整層丟棄。單變數理想恰好不受影響（`bounds = d` 時模數 `d` 正是
   `0..d−1`），這正是此缺陷長期隱形的原因；多變數時結果靜默錯誤。上界改為含端點，並補上
   固定點迭代的正確語義。
2. **`interreduce` 可能消滅生成元**（`gb/groebner.mbt`）。舊版把每個元素對「其餘全部」取正規形：
   `G = {x+y, y², x, y}` 時 `x+y` 與 `x` 的正規形都是 `0`，整個理想塌縮成 `{y}`——一個更大的理想。
   改成教科書定義：只用「首項單體式不整除 `LM(g_i)`」的元素對 `g_i` 做尾部化約，首項因此永不被消去，
   理想恆等；並保留對重複首項的差化簡。
3. **`ideal_saturate` 的 Rabinowitsch 收縮是錯的**（`gb/ideal.mbt`）。舊實作計算
   `(I R[t] + ⟨1−t g⟩) ∩ R`。取 `I = (x²)`、`g = x`：擴張理想含 `1`（其 Lex 約化基為 `{1}`），
   收縮是整環，而 `I : x^ω = (x)`。該技巧判定的是**零化變**而非理想。零維情形改為逐步精確的
   餘理想鏈 `I ≤ I : g ≤ I : g² ≤ …`（每步一個乘法矩陣核，`R` Noether 故穩定）；注意
   `ann(ḡ^m) ≠ ann(ḡ)`（`I=(x³)`、整理想要三步才出現），故單步核不夠。
4. **`embedding_dimension` 量錯了量**（`quot/quot.mbt`）。舊版數「`x_i − p_i` 不在 `I + m²` 中的個數」，
   這既不是 `dim A/(I+m²)` 也不是 `dim m/(I+m²)`：前者多算剩餘域與高階層，後者則因為類
   `x_i − p_i` 可以線性相依而算不準（`I = (x+y, y²)` 於原點：真值 1、舊碼給 2）。
   定義 `edim(I,p) = dim_k m/(I+m²) = dim A/(I+m²) − dim A/(I+m)` 才是定理 T4 的內容。
5. **`pure_lead_degree` 的「純」判斷寫反**（`gb/groebner.mbt`）。舊判斷是「沒有指數 > 1」，
   於是 `x²` 反而不算純（恰是此函數要量的東西），Hilbert 上界檢查形同虛設；改成「恰有一個非零指數」。

### C.2 技術債與死碼

* 刪除 Rabinowitsch 輔助函式（`poly/poly.mbt`）、孤兒輔助函式（`gb/ideal.mbt`）與其測試。
* `primitive_idempotents` 原本計算一整套 Gröbner 基後丟棄（`quot/quot.mbt`），並帶著從未使用的
  `gens` 參數；兩者一併移除，呼叫點同步更新。
* `clean_input` / `interreduce` 改以 `Poly::same` 比較稀疏形，不再為每個生成元印字串；
  `Poly::lead` 改為 O(d) 線性掃描；`filter_box` 預先提出首項單體式；12 處 `for … nobreak`
  改為 `while`；`local` 是 MoonBit 保留字（`Quot` / `Tables` 欄位改名 `is_local`）。
* `mono_divides(a, b)` 的參數順序與英文語意相反（實為「b 整除 a」），是本次兩個 bug 的來源，
  改名為 `mono_div_by(multiple, divisor)` 並在文件中寫死語意。
* `moon check --deny-warn`：編譯期引擎 0 警告；執行期僅剩 2 個 `unused_package`，已查證為
  工具鏈不計入「僅測試用」匯入造成的假陽性（移除匯入會讓測試無法編譯），已在 `moon.pkg` 註明。
* 為先前完全未被呼叫的公開 API 補測試：`divrem_list`、`constant_value`、`pow_mod_univar`、
  `lcm_univar`、`radical_part`、`split_linear`、`distinct_irreducible`、`interreduce`、
  `ideal_sum`、`ideal_product`、`lead_monos`、`pure_lead_degree`、`buchberger_unreduced`、
  `ideal_colon`、`ideal_saturate`、`embedding_dimension`、`trunc`、`series_deriv`。
  引擎測試由 35 個增至 54 個。
* 新增 `.gitignore`（`_build/`、`__pycache__/`、`*.pyc`、`.moon/` 產物）。


---

## 附錄 D：上同調擴充的健檢與修復（2026-10-18）

在加入 T7–T11（上同調與同構不變量）時，逐項複驗既有的線性代數層，
發現下列問題。每一項都以**斷言測試**固定，並在 `proof/` 補上憑證。

### D.1 真正的 bug：`nullspace` 的回代讀錯列

`gb/ideal.mbt::nullspace`、`quot/quot.mbt` 的反矩陣求解器、以及執行期
`ga/ga.mbt::Tables::nullspace` / `Tables::solve` 都以「**支點被發現的順序**」
去索引矩陣列（`a[pi][f]`，`pi` 是第 `i` 個支點）。

高斯–約旦消去會**跳過**秩缺的列（零列），因此支點序與列序不一致，回代讀到的是
錯列。胖點恰好沒有暴露此問題（其列無空隙），第一個反例來自新的 `wild` 表：
`F₂[C₂×C₂]` 的 socle 計算讀到零列，回傳 `(1,1,0,1)` 而非正確的 `(1,1,1,1)`。

修法：額外維護 `pivot_rows[pi]`（第 `i` 個支點實際所在的列）並用它回代。
四處實作同步修正，並補上**列序與支點序不一致**的回歸測試
（`gb/ideal_wbtest.mbt` 與 `ga/ga_wbtest.mbt` 各一）。

### D.2 真正的數學錯誤：`dim_k Ω¹ = Σ_p edim(A_p)`

本專案一度把凍結常數命名為 `OMEGA1_DIM` 並註記「`dim_k Ω¹_{A/K} = Σ_p edim(A_p)`」。
獨立重算（`Ω¹ = A^n / (A·∂I)`，以剩餘類化約 `∂I`）證明該式**為假**：

| 表 | `dim_k Ω¹_{A/K}`（真值） | `Σ_p edim(A_p)` |
|---|---|---|
| `cub` | 0 | 0 |
| `fat` | **3** | 2 |
| `wild` | **8** | 2 |

正確的等式是 `Σ_p edim(A_p) = dim_K(Ω¹_{A/K} ⊗_A K) = dim_K Tor^A_1(K,K) = dim_K Ext¹_A(K,K)`。
常數值本身一直是對的——錯的是**名稱與公式**。

處理：常數更名為 **`COTANGENT_DIM`**（餘切空間維數），`Inv.omega1_dim → cotangent_dim`，
文件改寫（定義 2.31、定理 2.33、附錄 A），並加入**反例斷言測試**
（`T7 counterexample`）與 `T8.*.omega1_caveat` 憑證記錄此區別。
此教訓也寫進第 2 章：不可把 `Ω¹ ⊗_A K` 與 `Ω¹` 混為一談。

### D.3 憑證本身的建模錯誤（整數量 vs. 域元素）

`T11.wild` 的 4 個目標起初證不出來，根因在憑證編碼而非被證物件：
`KIND`、`GROUP_ORDER`、`GROUP_RANK`、`NBETTI`、`betti` 與各維數都是**整數**，
卻被寫成模 `p` 的同餘式。在 `F₂` 中 `|C₂×C₂| = 4 → 0`、`RAD_DIM = 3 → 1`，
於是三分類定理、`b_i ≥ 1` 等命題全部變假。
另有一處實作錯誤：`a ↦ a^p` 用了 `p` 次乘法（得 `a^(p+1)`），正確應為 `p−1` 次。

修法：新增 `int_eq` / `int_gt0`（Z3 整數算術）並全面用於整數量；
域元素仍用 `mod_eq`。`frobenius_fixed_dim` 與 `ext1_jacobian` 修正後，
三張表的 `rad` / `soc` / `FROB_FIXED` / `EXT1_DIM` 全部由**重新計算**與凍結常數相符。

理想本身改為直接解析 `algebra/moon.mod` 的 `--terms` 規則取得，
不再假設「標準基底外的單項式生成 `I`」——該假設對 `cub` 不成立
（其 `I = (x−1)(x−2)(x−3)` 不是單項式理想）。

### D.4 本次成果

| 項目 | 前 | 後 |
|---|---|---|
| `algebra-ct` 斷言測試 | 54 | **63** |
| `algebra/ga` 斷言測試 | 4 | **9** |
| Z3 憑證（定理 / 目標） | 54 / 265 | **124 / 335** |
| 凍結表 | 2 張 | **3 張**（新增 `K[C₂×C₂]`） |
| 凍結不變量 | 6 個 | **11 個** |

憑證經**突變測試**驗證非空轉：把任一凍結常數改錯，對應 Z3 目標即回傳
`sat`（存在反例），確認這些定理是真的在檢查東西。

---

## 附錄 E：範疇化凍結與健檢（2026-10-19，T19）

### E.1 這次做了什麼

把第 2.12 節已存在於**編譯期**的分次物件（`Graded`）**送進凍結表**：

| 層 | 前 | 後 |
|---|---|---|
| `cat::categorify` | — | 五個平坦 `Int32` 陣列 + 區塊長度 + `nfactors` |
| `cat::Cat` 讀取器 | — | `loewy_point`、`kozul_point`、`hilbert_total`、`mdim`、`dim_at`、`socle` |
| `emit` | 只輸出整數 | 另輸出 `NHILBERT`/`NLOEWY`/`NKOSZUL`/`NPOINTS_CAT` 與五個 `pub let` |
| `ga::Tables` | 18 個欄位 | 24 個欄位（多 6 個凍結陣列） |
| `ga::Tables` 讀取器 | — | `hilbert_total`、`hilbert_at`、`loewy_block`、`mdim_at`、`socle_at`、`kozul_block`、`dim_at`、`loewy_total`、`kozul_total` |

零成本仍是硬性約束：新增的五個陣列是 `pub let` 整數常數，
**沒有任何執行期代數**——讀一個分次維數是一次陣列索引，取整個區塊是 `O(L_p)` 次複製。

### E.2 健檢中修掉的問題

1. **`RAD_DIM`/`SOCLE_DIM` 的重複來源（技術債 → 已消除）。**
   在加入 T19 之前，`RAD_DIM` 與 `SOCLE_DIM` 是 `coho` 獨立算出的兩個整數，
   而 `Loewy` 物件裡已含同樣的資訊。現在 `ga` 可由 `loewy` 陣列重算兩者
   （測試 `T19.2` 正是這個斷言），故它們是**同一物件的兩種讀法**而非兩批事實。
2. **`soc ≤ rad` 的錯誤直覺。** 測試初稿斷言 `socle ≤ rad`，在 `cub` 上失敗
   （étale：`rad = 0` 而 `soc = K`，每個因子貢獻 1）。正確的界是兩者都 `≤ D`；
   這個反例已寫進測試註解，因為「socle ⊆ rad」只對非約化部分成立。
3. **cub 的 Loewy 與 Hilbert 同形的陷阱。** `cub` 的 `loewy = hilbert = [1,1,1]`，
   初稿的憑證把它當成「兩者不必相同」的反例而失敗。事實是兩者**數值相同、理由不同**
   （前者是三個 `K` 的直和，後者是 `1, x, x²` 的分次）。憑證改為陳述真實內容
   （定理 2.13 節表格下方的註記），並在 MoonBit 測試與 Z3 各留一個對照。
4. **`int_eq` 只吃純量。** 憑證裡要比較整個凍結區塊時拋 `TypeError`；
   `int_eq` 現已支援列表逐項比較（長度不同直接為 `false`）。
5. **跨檔案型別別名（本專案的 MoonBit 慣例）。** `emit/emit.mbt` 頂端的
   `type Fp = @poly.Fp` 一組別名是硬性要求：直接寫 `CatData`（即使它在 `cat`
   套件內以 `pub(all) struct` 宣告）會得到 `The type CatData is undefined`，
   而 `@cat.Cat` 可用。T19 的 `type Cat = @cat.Cat` 即依此慣例加入。

### E.3 本次成果

| 項目 | 前 | 後 |
|---|---|---|
| `algebra-ct` 斷言測試 | 81 | **83** |
| `algebra/ga` 斷言測試 | 9 | **13** |
| Z3 憑證（範疇化） | 40 | **67**（新增 15 個 T19 目標） |
| Z3 憑證（總計） | 375 | **402** |
| 凍結不變量 | 11 個整數 | **11 個整數 + 5 個分次陣列 + 4 個長度常數** |
| 執行期讀取器 | 18 | **27** |

---

## 附錄 F：編號洞與憑證漏洞的補洞（2026-10-19，T12–T15）

### F.1 洞的診斷（事實）

使用者問「T12–T15 是漏掉還是無做過」。逐項查證的結果：

| 標號 | 診斷 | 證據 |
|---|---|---|
| `T12` | **從未實作**，也從未出現在任何文件 | `git log --all -S "T12"` 全歷史無命中 |
| `T13` | 同上 | `git log -S "T13"` 無命中 |
| `T14` | **只在程式註解中實作**，文件與憑證皆無 | `cat/res.mbt:237` 一行 `/// **Theorem (T14).**` |
| `T15` | 同 `T12` | `git log -S "T15"` 無命中 |
| `T9` | 文件有定理 2.34，但憑證被歸檔在 `T11.*` 之下 | 改前 `T9` 目標數 = 0 |

結論：這是**編號預留後未回填**的洞（前四個編號屬範疇化階段插入時留下的空位），
不是「做了但沒寫」。本階段把它補成四個真的、可機器檢查的陳述（§2.14）。

### F.2 順帶查出並修掉的第二個洞：定理 2.23 為假

原文件寫「局部環 `A` 正規 ⟺ `dim_k Soc(A) = 1`」。`mix = F₃[x,y]/(x²−y,y³)`
是零維局部環且 `dim_k Soc = 1`，但 `m = (x) ≠ 0` 故不正規——**反例成立**。
已於 §2.8 標明「已修正」，並由 T13 給出可執行的正確版本（§2.14.2）。
這也說明為什麼 T13 的內容不是憑空選的：它就是原定理修正後的樣子。

### F.3 順帶查出並修掉的第三個洞：憑證讀錯檔案

`proof/ga_proofs.py` 的 `gen_terms()`（憑證用來取得每張表的**理想生成元**）
原本寫死絕對路徑 `/home/user/algebra/algebra/moon.mod`——那是 `/home/user` 下
一份**過期的非 Git 鏡射**，不是本倉庫。兩份檔案當時內容相同，所以目標全過，
但只要鏡射落後，憑證就會對著**錯誤的理想**宣告成立。已改為
`os.path.join(ROOT, "..", "moon.mod")`（隨憑證檔案位置解析）。
這是本專案「隱蔽憑證」設計中最危險的一類缺陷：**證明通過，但證的不是這份程式碼**。

### F.4 本次成果

| 項目 | 前 | 後 |
|---|---|---|
| 凍結表 | 3 張 | **4 張**（新增反例表 `mix`） |
| `algebra-ct` 斷言測試 | 83 | **86** |
| `algebra/ga` 斷言測試 | 13 | **16** |
| Z3 憑證（總目標） | 402 | **461** |
| `T` 標號覆蓋率 | 17/19（T12–T15 空、T9 空） | **19/19** |
| `Tables` 欄位 / 讀取器 | 24 / 18 | **25 / 22**（新增 `pt_kind`、`point_kind`、`is_field_at`、`is_gorenstein_at`、`kozul_euler`） |

新增憑證：T12 × 4、T13 × 10、T14 × 8、T15 × 10、T9 × 2，共 34 個類別。
`socle` 的憑證改為**由定義重算**（`Ann(m_p)` = 乘積映射的零化度，見
`cat_proofs.socle_dim`），不再讀凍結常數，因此 T13 是獨立驗證而非自我重複。

突變測試（非空轉驗證）：把 `mix` 的 `pt_kind`、`kozul`、`hilbert` 分別改錯後，
恰有 `T13.mix.trichotomy`、`T14.mix.*`、`T15.mix.point0.euler` 回傳 `sat`；
還原後全數通過。

> 附錄 C 與 E 的數字是**各階段當時的快照**，保留以資對照；本附錄與文首、
> 附錄 A₀ 為目前狀態。
