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
| 28 | T18 wild: |G| = p^n, r = GROUP_RANK = n = 2 (C_2 x C_2 由兩個生成元生成) `T18.wild.group_data` | 1 | 1 | PASS |
| 29 | T18 wild: dim_k H^i(G,K) = i + 1 = Tate 自由秩 rank_i, i = 0 `T18.wild.betti_0` | 1 | 1 | PASS |
| 30 | T18 wild: dim_k H^i(G,K) = i + 1 = Tate 自由秩 rank_i, i = 1 `T18.wild.betti_1` | 1 | 1 | PASS |
| 31 | T18 wild: dim_k H^i(G,K) = i + 1 = Tate 自由秩 rank_i, i = 2 `T18.wild.betti_2` | 1 | 1 | PASS |
| 32 | T18 wild: dim_k H^i(G,K) = i + 1 = Tate 自由秩 rank_i, i = 3 `T18.wild.betti_3` | 1 | 1 | PASS |
| 33 | T18 wild: dim_k H^i(G,K) = i + 1 = Tate 自由秩 rank_i, i = 4 `T18.wild.betti_4` | 1 | 1 | PASS |
| 34 | T18 wild: dim_k H^i(G,K) = i + 1 = Tate 自由秩 rank_i, i = 5 `T18.wild.betti_5` | 1 | 1 | PASS |
| 35 | T18 wild: dim_k H^i(G,K) = i + 1 = Tate 自由秩 rank_i, i = 6 `T18.wild.betti_6` | 1 | 1 | PASS |
| 36 | T18 wild: 環 Lambda^*(V) (x) K[W] 的第 i 次分次 = 凍結 betti[i] (逐項) `T18.wild.betti_frozen` | 1 | 1 | PASS |
| 37 | T18 wild: 截斷到對稱次數 6 的環共有 112 個基元素 = Σ_{a+2b<=14} C(2,a)C(2+b-1,b) `T18.wild.ring_total` | 1 | 1 | PASS |
| 38 | T18 wild: H^0 = K, 即第 0 次分次維數為 1 (乘法單位存在且唯一) `T18.wild.ring_unit` | 1 | 1 | PASS |
| 39 | T18: 外積符號為 Koszul 符號 (e_1 e_0 = -e_0 e_1), 故分次反交換 `T18.wild.grcomm_sign` | 1 | 1 | PASS |
| 40 | T18: 對 [3] 中所有不相交子集對, 符號皆為 ±1 且 s(S,T)s(T,S) = (-1)^{|S||T|} (分次反交換) `T18.wild.grcomm_all` | 1 | 1 | PASS |

**合計 goals = 40，已由 Z3 證明 = 40，失敗 = 0**
