# MoonBit 代數演算法系統：編譯期零成本抽象與隱蔽式形式化證明

> 本文對應工作區 `/home/user/algebra/`，所有數字均為實際執行結果（見文末〈執行方式〉）。
> 語言：MoonBit（最新穩定版，經 `moonup install latest` 安裝）。
> 代數對象覆蓋題目要求的全部結構：座標環、落特環、函數環、仿射代數簇、概形、層、
> 冪等元、正規局部環、投射模、凝聚層、連續模、剩餘理想、半單理想、單純理想、半素／根理想。

---

## 0. 交付摘要

| 層 | 路徑 | 內容 | 驗證 |
|---|---|---|---|
| 編譯期引擎 | `algebra-ct/{poly,gb,quot,val,coho,emit}` + `cmd/gen` | 有限域/多項式、Gröbner、零維商環、截斷冪級數、**上同調不變量**、代碼生成 | **63/63** 斷言測試通過 |
| 執行期零成本層 | `algebra/ga` | 只含凍結整數表 + 查表運算 | **9/9** 斷言測試通過 |
| 隱蔽形式化證明（Z3） | `proof/ga_proofs.py` | 124 條定理、**335 個 SMT 目標，全部 `unsat` 放行（3.3 秒）** | `proof/RESULTS.md` |
| 隱蔽形式化證明（MoonBit） | `algebra/gap/gap.mbtp` | `predicate` / `lemma` / `proof_ensure` 邏輯側規格 | `moon check` 乾淨（`moon prove` 需 Why3） |

關鍵數據：

* 引擎測試：`poly 19 + gb 23 + quot 6 + val 7 + coho 8 = 63`，全部通過（`assert_eq` / `assert_true`），且 `moon check --deny-warn` 零警告。
* 執行期測試：凍結張量、原始冪等元、局部點的 socle、非正規性、根的互異性，以及 T7–T11 的
  餘切空間、`Ext¹`、`K[C₂×C₂]` 的 Betti 數 `b_i = i+1`，全部通過。
* 編譯期生成的常數：`D=3, NVAR=1, EDIM=0`（cub，`A = K³`）、`D=3, NVAR=2, EDIM=2`
  （fat）、`D=4, NVAR=2, EDIM=2, GROUP_ORDER=4`（wild，`A = K[C₂×C₂]`）。
* 上同調不變量（第 2.10 節 T7–T11）：`rad A`、`soc`、`Ω¹ ⊗_A K` 的維數、`Ext¹`、
  Frobenius 固定點、`KIND` 三分類與 Cohen–Mac Lane Betti 數，全部**編譯期**算完凍結。
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
  gap/gap.mbtp + proof/ga_proofs.py   隱蔽形式化證明（不影響執行期）
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

**定理 2.23（socle 判別式）.** 局部環 `A` 正規 ⟺ `dim_k Soc(A) = 1`，其中
`Soc(A) = Ann_A(m) = { a : a·g = 0, ∀g ∈ m }`。

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

### 3.7 複雜度總表

| 任務 | 樸素 | 本系統 |
|---|---|---|
| `f = g (mod I)` | `O(NF)` | `O(D)` 查表 |
| 兩元素相乘 | `O(NF)` | `O(D)` 查表 |
| `V_K(I)` 列舉 | `O(p^n)` | `O(p·deg)`（三角消去 + 準則） |
| 維數 `dim A` | Gröbner + Hilbert 函數 | `O(D)`（編譯期常數） |
| 冪等元 | 理想分解 | `O(V³)` 線性代數 |
| socle | Gröbner 推導 | `O(n·D³)` 線性代數 |
| radical | 反覆分解 | `O(D³)` 跡/零空間 |

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
| Z3（SMT-LIB2 語義） | `proof/ga_proofs.py` → `proof/RESULTS.md` | **335 / 335 目標 `unsat`，3.3 秒** |
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
    Soc·rad A = 0、Soc·A ⊆ Soc、SOCLE_DIM ≥ 1（三張表各一組）
T8* 余切空間/Ext¹：逐點 Jacobian 餘核 = EXT1_DIM、Tor¹ = Ext¹ = COTANGENT_DIM、
    Tor¹ = Σ_p edim、餘正规序列的 coker = COTANGENT_DIM、簡約 ⇔ 三者同時為 0
T10* Frobenius：由凍結張量重算 Fix(a↦a^p) = FROB_FIXED = NPOINTS
T11* 群代數與 Betti 數：|G| = p^r = D、edim = r、soc = A·N 一維、rad = I(G) 維數 |G|−1、
    Cohen-Maclane 係數逐項相符、b_0 = 1、正次 Betti 數 > 0、
    Maschke（|G| ≢ 0 ⇒ betti 為空）、KIND 三分類、étale ⇔ rad = 0 ⇔ Tor¹ = 0
```

> **憑證強度說明**：上表 `T7*`/`T8*`/`T10*`/`T11*` 的 `rad A`、`Soc(A)`、Frobenius 固定空間、
> Betti 數皆由**凍結表重新計算**（求值核、乘法矩陣核、`a ↦ a^p` 的特徵 1 空間、
> Cohen-Maclane 公式），再與凍結常數比對；理想本身則直接解析 `algebra/moon.mod`
> 的 `--terms` 規則取得，確保憑證量化的是引擎實際執行的那個理想。

完整表格見 `proof/RESULTS.md`。

### 6.4 信任邊界（誠實聲明）

1. Z3 證明的是**凍結表**所定義的有限代數；「凍結表來自 Gröbner 引擎」這一步由
   `algebra-ct` 的 63 個斷言測試與程式產生器的確定性輸入承擔，不是 SMT 證明的對象。
2. `gap/gap.mbtp` 目前只經過 `moon check`（型別/語法）與 `moon check --target native`；
   本沙箱無 Why3，故未實際執行 `moon prove`。文件中的 MoonBit 命題是 Z3 已證命題的
   MoonBit 側改寫，可望在具備 proof toolchain 的環境直接放行。
3. 所有 Z3 目標均以「否定命題 `unsat`」為通過標準，失敗會以非零碼結束
   （`python3 proof/run_proofs.py; echo $?`）。

---

## 7. 執行方式

```bash
export PATH="$HOME/.moon/bin:$HOME/.moonup/bin:$PATH"

# 1) 編譯期引擎（63 個斷言測試）
cd /home/user/algebra/algebra-ct && moon test --target native

# 2) 生成器（CLI）
cd /home/user/algebra/algebra-ct && moon build --target native cmd/gen
#   語法： 多項式以 ';' 分隔；項以 '|' 分隔；指數以 '.' 分隔；係數以 ':' 分隔
#   範例： --p 7  --n 2 --terms "2.0:1;1.1:1;0.2:1"             --name fatpoint
#          --p 97 --n 1 --terms "3.0:1|2.0:-6|1.0:11|0.0:-6"   --name cub
#          --p 2  --n 2 --terms "2.0:1|0.0:-1;0.2:1|0.0:-1"     --name wild
#   注意 F_2 上 x^2-1 必須寫成單一多項式 "2.0:1|0.0:-1"；若拆成 x^2 與 -1
#   兩個生成元，在 F_2 中它們生成的是單位理想 (1)。

# 3) 執行期（9 個斷言測試；dev_build 會自動重生成凍結表）
cd /home/user/algebra/algebra && moon test --target native

# 4) 隱蔽形式化證明（Z3）
cd /home/user/algebra/proof && python3 run_proofs.py     # -> RESULTS.md

# 5) MoonBit 側證明（需 Why3 ≥ 1.7.2 + z3）
cd /home/user/algebra/algebra && moon prove ga/gap
```

---

## 附錄 A：凍結表（倉庫中的實際常數）

三張表由 `algebra-ct` 的 `cmd/gen` 在**編譯期**產生並提交；
`algebra/moon.mod` 的 `gen-*` 規則是唯一輸入，`dev_build` 保證「表 ≡ 規格」。

| 常數 | `cub` = `F₉₇[x]/((x−1)(x−2)(x−3))` | `fat` = `F₇[x,y]/(x²,xy,y²)` | `wild` = `F₂[x,y]/(x²−1,y²−1)` |
|---|---|---|---|
| 說明 | `K[C₃]`，`A = K³`（étale） | 胖點（非簡約） | `K[C₂×C₂]`（`p`-群代數） |
| `P`, `D`, `NVAR` | 97, 3, 1 | 7, 3, 2 | 2, 4, 2 |
| `EDIM`, `LOCAL` | 0, false | 2, true | 2, true |
| `RAD_DIM` | 0 | 2 | 3 |
| `SOCLE_DIM` | 3 | 2 | **1** |
| `COTANGENT_DIM` | 0 | 2 | 2 |
| `EXT1_DIM` | 0 | 2 | 2 |
| `FROB_FIXED` | 3 | 1 | 1 |
| `GROUP_ORDER`, `GROUP_RANK` | 0, 0 | 0, 0 | **4, 2** |
| `KIND` | 0（étale） | 2（局部非群） | **1（`p`-群）** |
| `NBETTI`, `betti` | 0, `[]` | 0, `[]` | 7, `[1,2,3,4,5,6,7]` |

> `COTANGENT_DIM = dim_K(Ω¹ ⊗_A K) = Σ_p edim(A_p) = dim_K Ext¹_A(K,K)`，
> **不是** `dim_K Ω¹_{A/K}`（後者依序為 0、3、8）。見定理 2.31 的說明。
>
> `SOCLE_DIM` 在 `wild` 為 **1**（`soc = A·(1+x)(1+y)`），不是 `r = 2`。見定理 2.34。

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
* `algebra/ga`（9）：凍結張量即環；原始冪等元（和為 1、正交、冪等、求值為 δ）；胖點局部 +
  `edim = 2` + `socle` 二維 + `m² = 0`；根的求值互異；T7/T8 的 étale 與胖點上同調；
  T9/T10 的 `K[C₂×C₂]` Betti 數 `b_i = i+1` 與 `N² = 0`；
  **反例測試**「餘切空間 ≠ `dim_k Ω¹`」；`nullspace`/`solve` 的支點列回歸。
* `proof`（124 條定理 / 335 目標）：見 `proof/RESULTS.md`。
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
