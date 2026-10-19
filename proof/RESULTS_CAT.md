# 範疇化層 Z3 證明報告 / categorification proof report

| # | 定理 / theorem | SMT 目標 | 已證明 | 結果 |
|---|---------------|---------|--------|------|
| 1 | T16 fat: 局部分量 dim_k A_p = D - (D - NPOINTS·EDIM), 且 m_p 的基 ker(ev_pt) 維數 = RAD_DIM `T16.fat.local_dim` | 1 | 1 | PASS |
| 2 | T17 fat: Loewy 分次 dim 之和 = dim_k A_p (m^0 = A_p, m^L = 0) `T17.fat.loewy_total` | 1 | 1 | PASS |
| 3 | T17 fat: Σ_{i>=1} gr^i A_p = dim_k m_p = RAD_DIM, 且 gr^0 = 1 `T17.fat.loewy_radical` | 1 | 1 | PASS |
| 4 | T17 fat: 各因子最後非零分次之和 = soc A = SOCLE_DIM (m^L = 0 ⇒ m^{L-1}·m = 0, 且 soc 是直和) `T17.fat.loewy_socle` | 1 | 1 | PASS |
| 5 | T16 fat: Koszul 微分 d^i d^{i+1} = 0 (矩陣逐項為零) `T16.fat.koszul_complex` | 1 | 1 | PASS |
| 6 | T16 fat: H^0 = A_p/m_p = K, 即參數上同調的第 0 次分次為 1 `T16.fat.koszul_h0` | 1 | 1 | PASS |
| 7 | T16 fat: im d^1 = A_p·m_p = m_p, 故 rank d^1 = dim_k m_p = RAD_DIM, H^0 = dim C^0 - rank d^1 = 1 (由張量消元實得) `T16.fat.koszul_rank1` | 1 | 1 | PASS |
| 8 | T16 fat: 參數上同調 = 1 + 3t + 2t^2 (逐項與由凍結張量消元所得相符) `T16.fat.koszul_series` | 1 | 1 | PASS |
| 9 | T17 fat: Loewy 分次 = 1 + 2t (m^2 = 0, 基 = {1, x, y}) `T17.fat.loewy_series` | 1 | 1 | PASS |
| 10 | T16 wild: 局部分量 dim_k A_p = D - (D - NPOINTS·EDIM), 且 m_p 的基 ker(ev_pt) 維數 = RAD_DIM `T16.wild.local_dim` | 1 | 1 | PASS |
| 11 | T17 wild: Loewy 分次 dim 之和 = dim_k A_p (m^0 = A_p, m^L = 0) `T17.wild.loewy_total` | 1 | 1 | PASS |
| 12 | T17 wild: Σ_{i>=1} gr^i A_p = dim_k m_p = RAD_DIM, 且 gr^0 = 1 `T17.wild.loewy_radical` | 1 | 1 | PASS |
| 13 | T17 wild: 各因子最後非零分次之和 = soc A = SOCLE_DIM (m^L = 0 ⇒ m^{L-1}·m = 0, 且 soc 是直和) `T17.wild.loewy_socle` | 1 | 1 | PASS |
| 14 | T16 wild: Koszul 微分 d^i d^{i+1} = 0 (矩陣逐項為零) `T16.wild.koszul_complex` | 1 | 1 | PASS |
| 15 | T16 wild: H^0 = A_p/m_p = K, 即參數上同調的第 0 次分次為 1 `T16.wild.koszul_h0` | 1 | 1 | PASS |
| 16 | T16 wild: im d^1 = A_p·m_p = m_p, 故 rank d^1 = dim_k m_p = RAD_DIM, H^0 = dim C^0 - rank d^1 = 1 (由張量消元實得) `T16.wild.koszul_rank1` | 1 | 1 | PASS |
| 17 | T16 wild: 參數上同調 = 1 + 3t + 3t^2 + t^3 = (1 + t)^3 `T16.wild.koszul_series` | 1 | 1 | PASS |
| 18 | T17 wild: Loewy 分次 = 1 + 2t + t^2 (m = 3, m^2 = 1, m^3 = 0) `T17.wild.loewy_series` | 1 | 1 | PASS |
| 19 | T17 wild: m^2 = span{1 + x + y + xy}, dim = 1 = socle `T17.wild.m2_dim` | 1 | 1 | PASS |
| 20 | T16 cub: 局部分量 dim_k A_p = D - (D - NPOINTS·EDIM), 且 m_p 的基 ker(ev_pt) 維數 = RAD_DIM `T16.cub.local_dim` | 1 | 1 | PASS |
| 21 | T17 cub: Loewy 分次 dim 之和 = dim_k A_p (m^0 = A_p, m^L = 0) `T17.cub.loewy_total` | 1 | 1 | PASS |
| 22 | T17 cub: Σ_{i>=1} gr^i A_p = dim_k m_p = RAD_DIM, 且 gr^0 = 1 `T17.cub.loewy_radical` | 1 | 1 | PASS |
| 23 | T17 cub: 各因子最後非零分次之和 = soc A = SOCLE_DIM (m^L = 0 ⇒ m^{L-1}·m = 0, 且 soc 是直和) `T17.cub.loewy_socle` | 1 | 1 | PASS |
| 24 | T16 cub: Koszul 微分 d^i d^{i+1} = 0 (矩陣逐項為零) `T16.cub.koszul_complex` | 1 | 1 | PASS |
| 25 | T16 cub: H^0 = A_p/m_p = K, 即參數上同調的第 0 次分次為 1 `T16.cub.koszul_h0` | 1 | 1 | PASS |
| 26 | T16 cub: im d^1 = A_p·m_p = m_p, 故 rank d^1 = dim_k m_p = RAD_DIM, H^0 = dim C^0 - rank d^1 = 1 (由張量消元實得) `T16.cub.koszul_rank1` | 1 | 1 | PASS |
| 27 | T16 cub: etale (RAD_DIM = 0) ⇒ 每個局部分量的參數上同調皆為 1 `T16.cub.etale` | 1 | 1 | PASS |
| 28 | T16 mix: 局部分量 dim_k A_p = D - (D - NPOINTS·EDIM), 且 m_p 的基 ker(ev_pt) 維數 = RAD_DIM `T16.mix.local_dim` | 1 | 1 | PASS |
| 29 | T17 mix: Loewy 分次 dim 之和 = dim_k A_p (m^0 = A_p, m^L = 0) `T17.mix.loewy_total` | 1 | 1 | PASS |
| 30 | T17 mix: Σ_{i>=1} gr^i A_p = dim_k m_p = RAD_DIM, 且 gr^0 = 1 `T17.mix.loewy_radical` | 1 | 1 | PASS |
| 31 | T17 mix: 各因子最後非零分次之和 = soc A = SOCLE_DIM (m^L = 0 ⇒ m^{L-1}·m = 0, 且 soc 是直和) `T17.mix.loewy_socle` | 1 | 1 | PASS |
| 32 | T16 mix: Koszul 微分 d^i d^{i+1} = 0 (矩陣逐項為零) `T16.mix.koszul_complex` | 1 | 1 | PASS |
| 33 | T16 mix: H^0 = A_p/m_p = K, 即參數上同調的第 0 次分次為 1 `T16.mix.koszul_h0` | 1 | 1 | PASS |
| 34 | T16 mix: im d^1 = A_p·m_p = m_p, 故 rank d^1 = dim_k m_p = RAD_DIM, H^0 = dim C^0 - rank d^1 = 1 (由張量消元實得) `T16.mix.koszul_rank1` | 1 | 1 | PASS |
| 35 | T18 wild: |G| = p^n, r = GROUP_RANK = n = 2 (C_2 x C_2 由兩個生成元生成) `T18.wild.group_data` | 1 | 1 | PASS |
| 36 | T18 wild: dim_k H^i(G,K) = i + 1 = Tate 自由秩 rank_i, i = 0 `T18.wild.betti_0` | 1 | 1 | PASS |
| 37 | T18 wild: dim_k H^i(G,K) = i + 1 = Tate 自由秩 rank_i, i = 1 `T18.wild.betti_1` | 1 | 1 | PASS |
| 38 | T18 wild: dim_k H^i(G,K) = i + 1 = Tate 自由秩 rank_i, i = 2 `T18.wild.betti_2` | 1 | 1 | PASS |
| 39 | T18 wild: dim_k H^i(G,K) = i + 1 = Tate 自由秩 rank_i, i = 3 `T18.wild.betti_3` | 1 | 1 | PASS |
| 40 | T18 wild: dim_k H^i(G,K) = i + 1 = Tate 自由秩 rank_i, i = 4 `T18.wild.betti_4` | 1 | 1 | PASS |
| 41 | T18 wild: dim_k H^i(G,K) = i + 1 = Tate 自由秩 rank_i, i = 5 `T18.wild.betti_5` | 1 | 1 | PASS |
| 42 | T18 wild: dim_k H^i(G,K) = i + 1 = Tate 自由秩 rank_i, i = 6 `T18.wild.betti_6` | 1 | 1 | PASS |
| 43 | T18 wild: 環 Lambda^*(V) (x) K[W] 的第 i 次分次 = 凍結 betti[i] (逐項) `T18.wild.betti_frozen` | 1 | 1 | PASS |
| 44 | T18 wild: 截斷到對稱次數 6 的環共有 112 個基元素 = Σ_{a+2b<=14} C(2,a)C(2+b-1,b) `T18.wild.ring_total` | 1 | 1 | PASS |
| 45 | T18 wild: H^0 = K, 即第 0 次分次維數為 1 (乘法單位存在且唯一) `T18.wild.ring_unit` | 1 | 1 | PASS |
| 46 | T18: 外積符號為 Koszul 符號 (e_1 e_0 = -e_0 e_1), 故分次反交換 `T18.wild.grcomm_sign` | 1 | 1 | PASS |
| 47 | T18: 對 [3] 中所有不相交子集對, 符號皆為 ±1 且 s(S,T)s(T,S) = (-1)^{|S||T|} (分次反交換) `T18.wild.grcomm_all` | 1 | 1 | PASS |
| 48 | T12 fat (理想齊次且 A 局部): 齊次理想使標準單項式基底分次, 故 Loewy 濾過 = 單項式次數濾過, hilbert = loewy 逐項相同 = [1, 2] `T12.fat.series_equal` | 1 | 1 | PASS |
| 49 | T13 fat 點 0: Ann(m_p) 的維數 = Loewy 末項 (soc = ann(m_p) = m^{L-1}, 由張量消元重算) `T13.fat.point0.socle_ann` | 1 | 1 | PASS |
| 50 | T15 fat 點 0: 參數上同調的 Euler 特徵 Σ_i (-1)^i dim H^i = (1-1)^{d_p} (複形的 χ 等於其上同調的 χ), 故 = 1 ⇔ m_p = 0 `T15.fat.point0.euler` | 1 | 1 | PASS |
| 51 | T13 fat: 逐點三分類 —— pt_kind = 0 ⇔ m_p = 0 (K), pt_kind ≤ 1 ⇔ soc A_p = m_p 或 m_p = 0 (Gorenstein 或 K), 否則 2; 且 soc = Ann(m_p) 之維數 = Loewy 末項 `T13.fat.trichotomy` | 1 | 1 | PASS |
| 52 | T15 fat: Σ_p χ_p = 剩餘點數 (χ_p = 1 ⇔ A_p = K), 故 Σ_p Σ_i (-1)^i dim_k H^i = #{p : A_p = K} `T15.fat.euler_total` | 1 | 1 | PASS |
| 53 | T14 fat: 直接由凍結基底數出各次數的標準單項式數, 得 Hilbert 函數 = {0: 1, 1: 2} (Σ = D = 3) `T14.fat.from_basis` | 1 | 1 | PASS |
| 54 | T14 fat: Σ_j hilbert[j] = D 且 hilbert[0] = 1 `T14.fat.recovery` | 1 | 1 | PASS |
| 55 | T12 wild (理想不齊次而 A 局部): 齊次性是充分條件而非必要條件 —— 本表不齊次卻仍有 hilbert = loewy = [1, 2, 1] (x^2 = 1 使 m^2 = K, 末層恰為 1) `T12.wild.series_equal_anyway` | 1 | 1 | PASS |
| 56 | T13 wild 點 0: Ann(m_p) 的維數 = Loewy 末項 (soc = ann(m_p) = m^{L-1}, 由張量消元重算) `T13.wild.point0.socle_ann` | 1 | 1 | PASS |
| 57 | T15 wild 點 0: 參數上同調的 Euler 特徵 Σ_i (-1)^i dim H^i = (1-1)^{d_p} (複形的 χ 等於其上同調的 χ), 故 = 1 ⇔ m_p = 0 `T15.wild.point0.euler` | 1 | 1 | PASS |
| 58 | T13 wild: 逐點三分類 —— pt_kind = 0 ⇔ m_p = 0 (K), pt_kind ≤ 1 ⇔ soc A_p = m_p 或 m_p = 0 (Gorenstein 或 K), 否則 2; 且 soc = Ann(m_p) 之維數 = Loewy 末項 `T13.wild.trichotomy` | 1 | 1 | PASS |
| 59 | T15 wild: Σ_p χ_p = 剩餘點數 (χ_p = 1 ⇔ A_p = K), 故 Σ_p Σ_i (-1)^i dim_k H^i = #{p : A_p = K} `T15.wild.euler_total` | 1 | 1 | PASS |
| 60 | T14 wild: 直接由凍結基底數出各次數的標準單項式數, 得 Hilbert 函數 = {0: 1, 1: 2, 2: 1} (Σ = D = 4) `T14.wild.from_basis` | 1 | 1 | PASS |
| 61 | T14 wild: Σ_j hilbert[j] = D 且 hilbert[0] = 1 `T14.wild.recovery` | 1 | 1 | PASS |
| 62 | T12 cub (étale 且理想不齊次): hilbert 與 loewy 同形是巧合 (前者記錄 1, x, x^2 的次數, 後者是三個 K 的直和); T12 只宣告局部情形 `T12.cub.series_etale` | 1 | 1 | PASS |
| 63 | T13 cub 點 0: Ann(m_p) 的維數 = Loewy 末項 (soc = ann(m_p) = m^{L-1}, 由張量消元重算) `T13.cub.point0.socle_ann` | 1 | 1 | PASS |
| 64 | T15 cub 點 0: 參數上同調的 Euler 特徵 Σ_i (-1)^i dim H^i = (1-1)^{d_p} (複形的 χ 等於其上同調的 χ), 故 = 1 ⇔ m_p = 0 `T15.cub.point0.euler` | 1 | 1 | PASS |
| 65 | T13 cub 點 1: Ann(m_p) 的維數 = Loewy 末項 (soc = ann(m_p) = m^{L-1}, 由張量消元重算) `T13.cub.point1.socle_ann` | 1 | 1 | PASS |
| 66 | T15 cub 點 1: 參數上同調的 Euler 特徵 Σ_i (-1)^i dim H^i = (1-1)^{d_p} (複形的 χ 等於其上同調的 χ), 故 = 1 ⇔ m_p = 0 `T15.cub.point1.euler` | 1 | 1 | PASS |
| 67 | T13 cub 點 2: Ann(m_p) 的維數 = Loewy 末項 (soc = ann(m_p) = m^{L-1}, 由張量消元重算) `T13.cub.point2.socle_ann` | 1 | 1 | PASS |
| 68 | T15 cub 點 2: 參數上同調的 Euler 特徵 Σ_i (-1)^i dim H^i = (1-1)^{d_p} (複形的 χ 等於其上同調的 χ), 故 = 1 ⇔ m_p = 0 `T15.cub.point2.euler` | 1 | 1 | PASS |
| 69 | T13 cub: 逐點三分類 —— pt_kind = 0 ⇔ m_p = 0 (K), pt_kind ≤ 1 ⇔ soc A_p = m_p 或 m_p = 0 (Gorenstein 或 K), 否則 2; 且 soc = Ann(m_p) 之維數 = Loewy 末項 `T13.cub.trichotomy` | 1 | 1 | PASS |
| 70 | T15 cub: Σ_p χ_p = 剩餘點數 (χ_p = 1 ⇔ A_p = K), 故 Σ_p Σ_i (-1)^i dim_k H^i = #{p : A_p = K} `T15.cub.euler_total` | 1 | 1 | PASS |
| 71 | T14 cub: 直接由凍結基底數出各次數的標準單項式數, 得 Hilbert 函數 = {0: 1, 1: 1, 2: 1} (Σ = D = 3) `T14.cub.from_basis` | 1 | 1 | PASS |
| 72 | T14 cub: Σ_j hilbert[j] = D 且 hilbert[0] = 1 `T14.cub.recovery` | 1 | 1 | PASS |
| 73 | T12 mix (理想不齊次而 A 局部): 兩級數不必相同 —— 本表是充分性不可反推的反例, 同為 D = 6 但形狀不同 ([1, 2, 2, 1] vs [1, 1, 1, 1, 1, 1]) `T12.mix.series_differ` | 1 | 1 | PASS |
| 74 | T13 mix 點 0: Ann(m_p) 的維數 = Loewy 末項 (soc = ann(m_p) = m^{L-1}, 由張量消元重算) `T13.mix.point0.socle_ann` | 1 | 1 | PASS |
| 75 | T15 mix 點 0: 參數上同調的 Euler 特徵 Σ_i (-1)^i dim H^i = (1-1)^{d_p} (複形的 χ 等於其上同調的 χ), 故 = 1 ⇔ m_p = 0 `T15.mix.point0.euler` | 1 | 1 | PASS |
| 76 | T13 mix: 逐點三分類 —— pt_kind = 0 ⇔ m_p = 0 (K), pt_kind ≤ 1 ⇔ soc A_p = m_p 或 m_p = 0 (Gorenstein 或 K), 否則 2; 且 soc = Ann(m_p) 之維數 = Loewy 末項 `T13.mix.trichotomy` | 1 | 1 | PASS |
| 77 | T15 mix: Σ_p χ_p = 剩餘點數 (χ_p = 1 ⇔ A_p = K), 故 Σ_p Σ_i (-1)^i dim_k H^i = #{p : A_p = K} `T15.mix.euler_total` | 1 | 1 | PASS |
| 78 | T14 mix: 直接由凍結基底數出各次數的標準單項式數, 得 Hilbert 函數 = {0: 1, 1: 2, 2: 2, 3: 1} (Σ = D = 6) `T14.mix.from_basis` | 1 | 1 | PASS |
| 79 | T14 mix: Σ_j hilbert[j] = D 且 hilbert[0] = 1 `T14.mix.recovery` | 1 | 1 | PASS |
| 80 | T19 fat: Σ_j hilbert[j] = D (Hilbert 函數的恢復恆等式) `T19.fat.hilbert_total` | 1 | 1 | PASS |
| 81 | T19 fat: hilbert[0] = 1 (1 恆為標準單項式) `T19.fat.hilbert_unit` | 1 | 1 | PASS |
| 82 | T19 fat: Σ loewy = D (Loewy 濾過窮盡 A) `T19.fat.loewy_total` | 1 | 1 | PASS |
| 83 | T19 fat: Σ loewy_lens = NLOEWY = len(loewy), 且 len(loewy_lens) = NPOINTS_CAT = NPOINTS `T19.fat.loewy_lengths` | 1 | 1 | PASS |
| 84 | T19 fat: 每個 Loewy 區塊的首項為 1 (gr^0 = K), Σ_{i>=1} = RAD_DIM, 最後一項之和 = SOCLE_DIM `T19.fat.loewy_blocks` | 1 | 1 | PASS |
| 85 | T19 fat: Σ kozul_lens = NKOSZUL = len(kozul), 且 len(kozul_lens) = NPOINTS_CAT `T19.fat.kozul_lengths` | 1 | 1 | PASS |
| 86 | T19 fat: 每個參數上同調區塊的首項為 1 (H^0 = A_p/m_p = K) `T19.fat.kozul_h0` | 1 | 1 | PASS |
| 87 | T19 fat: 參數上同調區塊為 1 ⇔ m_p = 0 ⇔ A_p 正則 (以 Loewy 區塊判定) `T19.fat.kozul_regular` | 1 | 1 | PASS |
| 88 | T19 fat: 局部且標準單項式基底次數分次時, Loewy 區塊 = Hilbert 函數 (兩者都由凍結張量算出, 互相印證) `T19.fat.loewy_equals_hilbert_local` | 1 | 1 | PASS |
| 89 | T19 wild: Σ_j hilbert[j] = D (Hilbert 函數的恢復恆等式) `T19.wild.hilbert_total` | 1 | 1 | PASS |
| 90 | T19 wild: hilbert[0] = 1 (1 恆為標準單項式) `T19.wild.hilbert_unit` | 1 | 1 | PASS |
| 91 | T19 wild: Σ loewy = D (Loewy 濾過窮盡 A) `T19.wild.loewy_total` | 1 | 1 | PASS |
| 92 | T19 wild: Σ loewy_lens = NLOEWY = len(loewy), 且 len(loewy_lens) = NPOINTS_CAT = NPOINTS `T19.wild.loewy_lengths` | 1 | 1 | PASS |
| 93 | T19 wild: 每個 Loewy 區塊的首項為 1 (gr^0 = K), Σ_{i>=1} = RAD_DIM, 最後一項之和 = SOCLE_DIM `T19.wild.loewy_blocks` | 1 | 1 | PASS |
| 94 | T19 wild: Σ kozul_lens = NKOSZUL = len(kozul), 且 len(kozul_lens) = NPOINTS_CAT `T19.wild.kozul_lengths` | 1 | 1 | PASS |
| 95 | T19 wild: 每個參數上同調區塊的首項為 1 (H^0 = A_p/m_p = K) `T19.wild.kozul_h0` | 1 | 1 | PASS |
| 96 | T19 wild: 參數上同調區塊為 1 ⇔ m_p = 0 ⇔ A_p 正則 (以 Loewy 區塊判定) `T19.wild.kozul_regular` | 1 | 1 | PASS |
| 97 | T19 wild: 局部且標準單項式基底次數分次時, Loewy 區塊 = Hilbert 函數 (兩者都由凍結張量算出, 互相印證) `T19.wild.loewy_equals_hilbert_local` | 1 | 1 | PASS |
| 98 | T19 cub: Σ_j hilbert[j] = D (Hilbert 函數的恢復恆等式) `T19.cub.hilbert_total` | 1 | 1 | PASS |
| 99 | T19 cub: hilbert[0] = 1 (1 恆為標準單項式) `T19.cub.hilbert_unit` | 1 | 1 | PASS |
| 100 | T19 cub: Σ loewy = D (Loewy 濾過窮盡 A) `T19.cub.loewy_total` | 1 | 1 | PASS |
| 101 | T19 cub: Σ loewy_lens = NLOEWY = len(loewy), 且 len(loewy_lens) = NPOINTS_CAT = NPOINTS `T19.cub.loewy_lengths` | 1 | 1 | PASS |
| 102 | T19 cub: 每個 Loewy 區塊的首項為 1 (gr^0 = K), Σ_{i>=1} = RAD_DIM, 最後一項之和 = SOCLE_DIM `T19.cub.loewy_blocks` | 1 | 1 | PASS |
| 103 | T19 cub: Σ kozul_lens = NKOSZUL = len(kozul), 且 len(kozul_lens) = NPOINTS_CAT `T19.cub.kozul_lengths` | 1 | 1 | PASS |
| 104 | T19 cub: 每個參數上同調區塊的首項為 1 (H^0 = A_p/m_p = K) `T19.cub.kozul_h0` | 1 | 1 | PASS |
| 105 | T19 cub: 參數上同調區塊為 1 ⇔ m_p = 0 ⇔ A_p 正則 (以 Loewy 區塊判定) `T19.cub.kozul_regular` | 1 | 1 | PASS |
| 106 | T19 cub: étale 時 Loewy 區塊逐點皆為 [1] (每個因子是 K), 而 Hilbert 函數記錄標準單項式 1, x, x^2 的次數; 兩者在本表同為 [1, 1, 1] 但理由不同 `T19.cub.loewy_equals_hilbert_etale` | 1 | 1 | PASS |

**合計 goals = 106，已由 Z3 證明 = 106，失敗 = 0**
