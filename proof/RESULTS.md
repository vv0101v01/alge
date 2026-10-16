# Z3 證明報告 / Z3 proof report

| # | 定理 / theorem | SMT 目標 | 已證明 | 結果 |
|---|---------------|---------|--------|------|
| 1 | 座標環 cub: e_i * 1 = e_i (張量單位律) `T1.cub.unit_l` | 9 | 9 | PASS |
| 2 | 座標環 cub: 1 * e_i = e_i (張量單位律) `T1.cub.unit_r` | 9 | 9 | PASS |
| 3 | 函數環 cub: 結合律 (T*)*T = T*(T*) `T1.cub.assoc` | 81 | 81 | PASS |
| 4 | 交換律 cub: e_i e_j = e_j e_i `T1.cub.comm` | 9 | 9 | PASS |
| 5 | 座標環 fat: e_i * 1 = e_i (張量單位律) `T1.fat.unit_l` | 9 | 9 | PASS |
| 6 | 座標環 fat: 1 * e_i = e_i (張量單位律) `T1.fat.unit_r` | 9 | 9 | PASS |
| 7 | 函數環 fat: 結合律 (T*)*T = T*(T*) `T1.fat.assoc` | 81 | 81 | PASS |
| 8 | 交換律 fat: e_i e_j = e_j e_i `T1.fat.comm` | 9 | 9 | PASS |
| 9 | 仿射代數簇 cub: 求值 ev_p 是環同態 (雙線性基底檢驗) `T2.cub.eval_hom` | 1 | 1 | PASS |
| 10 | cub: V(I) 的 K-點兩兩相異 `T2.cub.points_distinct` | 1 | 1 | PASS |
| 11 | 仿射代數簇 fat: 求值 ev_p 是環同態 (雙線性基底檢驗) `T2.fat.eval_hom` | 1 | 1 | PASS |
| 12 | fat: V(I) 的 K-點兩兩相異 `T2.fat.points_distinct` | 1 | 1 | PASS |
| 13 | 冪等元: e_i e_j = delta_ij e_i (原始冪等元) `T3.idem_orthogonal` | 1 | 1 | PASS |
| 14 | 冪等元: sum_i e_i = 1 (中國剩餘定理) `T3.idem_sum` | 1 | 1 | PASS |
| 15 | 冪等元: x = r_i e_i, 故 x - r_i in Ann(e_i) `T3.idem_x` | 1 | 1 | PASS |
| 16 | 冪等元: e_i e_j = e_i 當 i=j (冪等) `T3.idem_projection` | 1 | 1 | PASS |
| 17 | 剩餘理想 I_p = ker(ev_p) = A*(x - r): 核的參數式描述 `T3.ker_eval_0` | 1 | 1 | PASS |
| 18 | 剩餘理想 I_p = A*(x - r): 核的每個基底向量都由 x - r 生成 `T3.ker_eval_0.gen` | 2 | 2 | PASS |
| 19 | 剩餘理想 I_p = ker(ev_p) = A*(x - r): 核的參數式描述 `T3.ker_eval_1` | 1 | 1 | PASS |
| 20 | 剩餘理想 I_p = A*(x - r): 核的每個基底向量都由 x - r 生成 `T3.ker_eval_1.gen` | 2 | 2 | PASS |
| 21 | 剩餘理想 I_p = ker(ev_p) = A*(x - r): 核的參數式描述 `T3.ker_eval_2` | 1 | 1 | PASS |
| 22 | 剩餘理想 I_p = A*(x - r): 核的每個基底向量都由 x - r 生成 `T3.ker_eval_2.gen` | 2 | 2 | PASS |
| 23 | 半單理想: 三個剩餘理想的交 = 0 (A 是半單環) `T3.ker_inter_zero` | 1 | 1 | PASS |
| 24 | 投射模/半單理想: A = e_1 A (+) e_2 A (+) e_3 A, pi_i(a) = e_i*a `T3.decomposition` | 1 | 1 | PASS |
| 25 | 直和性: e_0 A ∩ e_1 A = 0 (兩條直線獨立) `T3.direct_01` | 1 | 1 | PASS |
| 26 | 直和性: e_0 A ∩ e_2 A = 0 (兩條直線獨立) `T3.direct_02` | 1 | 1 | PASS |
| 27 | 直和性: e_1 A ∩ e_0 A = 0 (兩條直線獨立) `T3.direct_10` | 1 | 1 | PASS |
| 28 | 直和性: e_1 A ∩ e_2 A = 0 (兩條直線獨立) `T3.direct_12` | 1 | 1 | PASS |
| 29 | 直和性: e_2 A ∩ e_0 A = 0 (兩條直線獨立) `T3.direct_20` | 1 | 1 | PASS |
| 30 | 直和性: e_2 A ∩ e_1 A = 0 (兩條直線獨立) `T3.direct_21` | 1 | 1 | PASS |
| 31 | 域 F_p 中 a^2 = a 蘊涵 a = 0 或 a = 1 (故 A 的冪等元皆由 e_i 組成) `T3.field_idem` | 1 | 1 | PASS |
| 32 | 座標環簡約: F_97 中沒有非零冪零元, 故 A = K^3 是簡約環 (概形 reduced) `T7.field_no_nilpotents` | 1 | 1 | PASS |
| 33 | 剩餘理想: e_1 A ~ F_97 且 (x - r_1) e_1 = 0, 故 Ann(e_1) = I_p 極大(素) `T7.residue_0` | 1 | 1 | PASS |
| 34 | 剩餘理想: e_2 A ~ F_97 且 (x - r_2) e_2 = 0, 故 Ann(e_2) = I_p 極大(素) `T7.residue_1` | 1 | 1 | PASS |
| 35 | 剩餘理想: e_3 A ~ F_97 且 (x - r_3) e_3 = 0, 故 Ann(e_3) = I_p 極大(素) `T7.residue_2` | 1 | 1 | PASS |
| 36 | 互素/不相交: I_1 + I_2 = A (單位 r_2 - r_1), V(I) 為三點不交聯集 `T7.comaximal_01` | 1 | 1 | PASS |
| 37 | 互素/不相交: I_1 + I_3 = A (單位 r_3 - r_1), V(I) 為三點不交聯集 `T7.comaximal_02` | 1 | 1 | PASS |
| 38 | 互素/不相交: I_2 + I_3 = A (單位 r_3 - r_2), V(I) 為三點不交聯集 `T7.comaximal_12` | 1 | 1 | PASS |
| 39 | 正則局部環/底環 Soc(A)=Ann(m): 底環元素的參數式描述 (雙向) `T4.socle_param` | 1 | 1 | PASS |
| 40 | Soc(A) 的 K-維數 = EDIM = 2 (局部代數判別準則 dim Soc = dim_k m/m^2) `T4.socle_dim` | 1 | 1 | PASS |
| 41 | 非正規: dim_k A = 3 > edim = 2, 故 A 不是正規局部環 (但 socle 判別式給出 dim=2) `T4.not_regular` | 1 | 1 | PASS |
| 42 | m^2 = 0 (由 x^2=xy=y^2=0): 生成元兩兩相乘為零 `T4.m2_zero` | 1 | 1 | PASS |
| 43 | m = (x,y), 且 x,y 線性獨立 (故 dim_k m = 2 = edim) `T4.m_indep` | 1 | 1 | PASS |
| 44 | 局部性: a_0 != 0 時 (a_0^{-1} - a_0^{-2}m)*a = 1 (294 個元素的左右逆) `T4.unit_inverse` | 1 | 1 | PASS |
| 45 | 剩餘域 A/m ~ F7: 正規投射 q(a)=a_0 的核恰為 m (概形的閉點) `T4.residue_field` | 1 | 1 | PASS |
| 46 | F7 是域: 每個非零元都有逆元 (故 A/m 為域, m 是極大理想) `T4.field_axioms` | 1 | 1 | PASS |
| 47 | 根理想: m 內任意兩元素相乘為零 (7^4 = 2401 組全稱情形) `T5.m2_bilinear` | 1 | 1 | PASS |
| 48 | 可逆元素永不冪零 (a_0 != 0 的 294 個元素, 前 12 次冪皆非零) `T5.unit_not_nilpotent` | 1 | 1 | PASS |
| 49 | 非半素: x != 0 且 x^2 = 0, 故 (0) != sqrt(0) = m (理想 (0) 不是根理想) `T5.zero_not_radical` | 1 | 1 | PASS |
| 50 | 凝聚層/精確序列 0 -> m -> A -> A/m -> 0 在 A 處精確 (ker q = m) `T6.exact_at_A` | 1 | 1 | PASS |
| 51 | 函數環/分次: gr_m(A) 的第 1 層 = m/m^2 由 x,y 獨立張成 (2 維, 無關係) `T6.gr_layer` | 1 | 1 | PASS |
| 52 | 連續模/精確序列: 0 -> xA -> A -> A/xA -> 0 精確 (ker q = xA) `T6.exact_xA` | 1 | 1 | PASS |
| 53 | 連續模/精確序列: 0 -> yA -> A -> A/yA -> 0 精確 (ker q = yA) `T6.exact_yA` | 1 | 1 | PASS |
| 54 | 凝聚性: dim_k A = 3 有限, 故 A 同時是 Artin 與 Noetherian, Spec A 上的層凝聚 `T6.artinian_noetherian` | 1 | 1 | PASS |

**合計 goals = 265，已由 Z3 證明 = 265，失敗 = 0**
