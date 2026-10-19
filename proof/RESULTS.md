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
| 55 | 根理想: rad A = 所有點求值核的交集, dim_k rad A = RAD_DIM `T7.cub.rad_dim` | 1 | 1 | PASS |
| 56 | rad A 的每個元素在每個 K-有理點取值 0 (逐基底全稱驗證) `T7.cub.rad_vanishes` | 1 | 1 | PASS |
| 57 | rad A 是理想: (rad A)·A ⊆ rad A (全稱, 以參數式描述子消元) `T7.cub.rad_ideal` | 1 | 1 | PASS |
| 58 | I ⊆ rad A: 標準基底外的單項式 (I 的生成元) 在所有點取值 0 `T7.cub.ideal_in_rad` | 1 | 1 | PASS |
| 59 | 簡約判準: A 簡約 ⇔ rad A = 0 ⇔ Tor^A_1(K,K) = 0 ⇔ Ext^1 = 0 `T7.cub.reduced` | 1 | 1 | PASS |
| 60 | 底環: Soc(A) = Ann(rad A), dim_k Soc(A) = SOCLE_DIM `T7.cub.socle_dim` | 1 | 1 | PASS |
| 61 | 底環定義: Soc(A)·rad A = 0 (逐對基底全稱驗證) `T7.cub.socle_kills_rad` | 1 | 1 | PASS |
| 62 | Soc(A) 是理想: Soc(A)·A ⊆ Soc(A) (全稱, 以參數式描述子消元) `T7.cub.socle_ideal` | 1 | 1 | PASS |
| 63 | 底環非零: 1 ∈ Soc(A) (因 rad A·1 ⊆ rad A), 故 SOCLE_DIM ≥ 1 `T7.cub.socle_nonempty` | 1 | 1 | PASS |
| 64 | Ext^1_A(K,K): 逐點 Jacobian 餘核維數總和 = EXT1_DIM `T8.cub.ext1_jacobian` | 1 | 1 | PASS |
| 65 | Auslander-Bridger-Solberg: dim Ext^1_A(K,K) = dim Tor^A_1(K,K) = COTANGENT_DIM = EXT1_DIM `T8.cub.tor1_ext1` | 1 | 1 | PASS |
| 66 | Tor^A_1(K,K) = ⊕_p m_p/m_p^2: dim = Σ_p edim(A_p); 局部情形下即 COTANGENT_DIM = NPOINTS·EDIM, etale 時兩者皆 0 `T8.cub.tor1_edim` | 1 | 1 | PASS |
| 67 | 餘正规序列 I/I^2 --d--> K^n --c--> Ω^1_{A/K} ⊗_A K --0--> 0: coker d 的維數 = Σ_p edim = COTANGENT_DIM `T8.cub.conormal` | 1 | 1 | PASS |
| 68 | A 簡約 ⇔ COTANGENT_DIM = 0 ⇔ EXT1_DIM = 0 ⇔ RAD_DIM = 0 (三條獨立路徑必須同時成立) `T8.cub.reduced_iff_zero` | 1 | 1 | PASS |
| 69 | Frobenius 固定空間: dim_k Fix(a↦a^p) = FROB_FIXED (由凍結張量重算) `T10.cub.frob_fixed` | 1 | 1 | PASS |
| 70 | Frobenius ⇔ 有理點: dim Fix(Frob) = NPOINTS = #K-有理點 `T10.cub.frob_points` | 1 | 1 | PASS |
| 71 | Maschke: GROUP_ORDER = 0 時無非平凡 p-群上同調, NBETTI = 0 且 betti 為空陣列 `T11.cub.maschke` | 1 | 1 | PASS |
| 72 | 三分類 KIND: 0 = étale (域之積), 1 = p-群代數, 2 = 局部但非群代數; 與 (RAD_DIM, COTANGENT_DIM, GROUP_ORDER) 一致 `T11.cub.kind` | 1 | 1 | PASS |
| 73 | étale ⇔ rad A = 0 ⇔ Tor_1 = 0 ⇔ KIND = 0 `T11.cub.kind_etale` | 1 | 1 | PASS |
| 74 | 局部且 rad A = 0 蘊涵 D = 1 (局部代數簡約 ⇔ 是域 ⇔ 一點) `T11.cub.local_etale` | 1 | 1 | PASS |
| 75 | 根理想: rad A = 所有點求值核的交集, dim_k rad A = RAD_DIM `T7.fat.rad_dim` | 1 | 1 | PASS |
| 76 | rad A 的每個元素在每個 K-有理點取值 0 (逐基底全稱驗證) `T7.fat.rad_vanishes` | 1 | 1 | PASS |
| 77 | rad A 是理想: (rad A)·A ⊆ rad A (全稱, 以參數式描述子消元) `T7.fat.rad_ideal` | 1 | 1 | PASS |
| 78 | I ⊆ rad A: 標準基底外的單項式 (I 的生成元) 在所有點取值 0 `T7.fat.ideal_in_rad` | 1 | 1 | PASS |
| 79 | 簡約判準: A 簡約 ⇔ rad A = 0 ⇔ Tor^A_1(K,K) = 0 ⇔ Ext^1 = 0 `T7.fat.reduced` | 1 | 1 | PASS |
| 80 | 底環: Soc(A) = Ann(rad A), dim_k Soc(A) = SOCLE_DIM `T7.fat.socle_dim` | 1 | 1 | PASS |
| 81 | 底環定義: Soc(A)·rad A = 0 (逐對基底全稱驗證) `T7.fat.socle_kills_rad` | 1 | 1 | PASS |
| 82 | Soc(A) 是理想: Soc(A)·A ⊆ Soc(A) (全稱, 以參數式描述子消元) `T7.fat.socle_ideal` | 1 | 1 | PASS |
| 83 | 底環非零: 1 ∈ Soc(A) (因 rad A·1 ⊆ rad A), 故 SOCLE_DIM ≥ 1 `T7.fat.socle_nonempty` | 1 | 1 | PASS |
| 84 | Ext^1_A(K,K): 逐點 Jacobian 餘核維數總和 = EXT1_DIM `T8.fat.ext1_jacobian` | 1 | 1 | PASS |
| 85 | Auslander-Bridger-Solberg: dim Ext^1_A(K,K) = dim Tor^A_1(K,K) = COTANGENT_DIM = EXT1_DIM `T8.fat.tor1_ext1` | 1 | 1 | PASS |
| 86 | Tor^A_1(K,K) = ⊕_p m_p/m_p^2: dim = Σ_p edim(A_p); 局部情形下即 COTANGENT_DIM = NPOINTS·EDIM, etale 時兩者皆 0 `T8.fat.tor1_edim` | 1 | 1 | PASS |
| 87 | 餘正规序列 I/I^2 --d--> K^n --c--> Ω^1_{A/K} ⊗_A K --0--> 0: coker d 的維數 = Σ_p edim = COTANGENT_DIM `T8.fat.conormal` | 1 | 1 | PASS |
| 88 | A 簡約 ⇔ COTANGENT_DIM = 0 ⇔ EXT1_DIM = 0 ⇔ RAD_DIM = 0 (三條獨立路徑必須同時成立) `T8.fat.reduced_iff_zero` | 1 | 1 | PASS |
| 89 | Frobenius 固定空間: dim_k Fix(a↦a^p) = FROB_FIXED (由凍結張量重算) `T10.fat.frob_fixed` | 1 | 1 | PASS |
| 90 | Frobenius ⇔ 有理點: dim Fix(Frob) = NPOINTS = #K-有理點 `T10.fat.frob_points` | 1 | 1 | PASS |
| 91 | Maschke: GROUP_ORDER = 0 時無非平凡 p-群上同調, NBETTI = 0 且 betti 為空陣列 `T11.fat.maschke` | 1 | 1 | PASS |
| 92 | 三分類 KIND: 0 = étale (域之積), 1 = p-群代數, 2 = 局部但非群代數; 與 (RAD_DIM, COTANGENT_DIM, GROUP_ORDER) 一致 `T11.fat.kind` | 1 | 1 | PASS |
| 93 | étale ⇔ rad A = 0 ⇔ Tor_1 = 0 ⇔ KIND = 0 `T11.fat.kind_etale` | 1 | 1 | PASS |
| 94 | 局部且 rad A = 0 蘊涵 D = 1 (局部代數簡約 ⇔ 是域 ⇔ 一點) `T11.fat.local_etale` | 1 | 1 | PASS |
| 95 | 根理想: rad A = 所有點求值核的交集, dim_k rad A = RAD_DIM `T7.wild.rad_dim` | 1 | 1 | PASS |
| 96 | rad A 的每個元素在每個 K-有理點取值 0 (逐基底全稱驗證) `T7.wild.rad_vanishes` | 1 | 1 | PASS |
| 97 | rad A 是理想: (rad A)·A ⊆ rad A (全稱, 以參數式描述子消元) `T7.wild.rad_ideal` | 1 | 1 | PASS |
| 98 | I ⊆ rad A: 標準基底外的單項式 (I 的生成元) 在所有點取值 0 `T7.wild.ideal_in_rad` | 1 | 1 | PASS |
| 99 | 簡約判準: A 簡約 ⇔ rad A = 0 ⇔ Tor^A_1(K,K) = 0 ⇔ Ext^1 = 0 `T7.wild.reduced` | 1 | 1 | PASS |
| 100 | 底環: Soc(A) = Ann(rad A), dim_k Soc(A) = SOCLE_DIM `T7.wild.socle_dim` | 1 | 1 | PASS |
| 101 | 底環定義: Soc(A)·rad A = 0 (逐對基底全稱驗證) `T7.wild.socle_kills_rad` | 1 | 1 | PASS |
| 102 | Soc(A) 是理想: Soc(A)·A ⊆ Soc(A) (全稱, 以參數式描述子消元) `T7.wild.socle_ideal` | 1 | 1 | PASS |
| 103 | 底環非零: 1 ∈ Soc(A) (因 rad A·1 ⊆ rad A), 故 SOCLE_DIM ≥ 1 `T7.wild.socle_nonempty` | 1 | 1 | PASS |
| 104 | Ext^1_A(K,K): 逐點 Jacobian 餘核維數總和 = EXT1_DIM `T8.wild.ext1_jacobian` | 1 | 1 | PASS |
| 105 | Auslander-Bridger-Solberg: dim Ext^1_A(K,K) = dim Tor^A_1(K,K) = COTANGENT_DIM = EXT1_DIM `T8.wild.tor1_ext1` | 1 | 1 | PASS |
| 106 | Tor^A_1(K,K) = ⊕_p m_p/m_p^2: dim = Σ_p edim(A_p); 局部情形下即 COTANGENT_DIM = NPOINTS·EDIM, etale 時兩者皆 0 `T8.wild.tor1_edim` | 1 | 1 | PASS |
| 107 | 餘正规序列 I/I^2 --d--> K^n --c--> Ω^1_{A/K} ⊗_A K --0--> 0: coker d 的維數 = Σ_p edim = COTANGENT_DIM `T8.wild.conormal` | 1 | 1 | PASS |
| 108 | A 簡約 ⇔ COTANGENT_DIM = 0 ⇔ EXT1_DIM = 0 ⇔ RAD_DIM = 0 (三條獨立路徑必須同時成立) `T8.wild.reduced_iff_zero` | 1 | 1 | PASS |
| 109 | Frobenius 固定空間: dim_k Fix(a↦a^p) = FROB_FIXED (由凍結張量重算) `T10.wild.frob_fixed` | 1 | 1 | PASS |
| 110 | Frobenius ⇔ 有理點: dim Fix(Frob) = NPOINTS = #K-有理點 `T10.wild.frob_points` | 1 | 1 | PASS |
| 111 | 群代數: A = K[G] 且 |G| = p^r = D = GROUP_ORDER `T11.wild.group_order` | 1 | 1 | PASS |
| 112 | Cauchy: dim_K K[G] = |G|, 故 D = p^r (r = GROUP_RANK) `T11.wild.group_dim` | 1 | 1 | PASS |
| 113 | edim(K[G]) = r = GROUP_RANK (Jacobson 基底 x_1-1,...,x_r-1) `T11.wild.edim` | 1 | 1 | PASS |
| 114 | soc(K[G]) = K[G]·N (N = Σ_{g∈G} g): 底環一維, SOCLE_DIM = 1 `T11.wild.socle_one` | 1 | 1 | PASS |
| 115 | rad K[G] = 增廣理想 I(G), 維數 |G| - 1 = RAD_DIM `T11.wild.rad_augmentation` | 1 | 1 | PASS |
| 116 | Cohen-Maclane: b_i = Σ_{2j≤i} C(w+j-1,j)C(r,i-2j), w = |G| - r, 與凍結 betti 逐項相等 (NBETTI 項) `T11.wild.betti` | 1 | 1 | PASS |
| 117 | NBETTI = |betti|: 凍結陣列長度與公式長度一致 `T11.wild.betti_len` | 1 | 1 | PASS |
| 118 | Betti 數差分: b_i - b_{i-1} 與公式逐項相符 `T11.wild.betti_recurrence` | 1 | 1 | PASS |
| 119 | H^0(G,K) = K: b_0 = 1, 與公式在 i=0 的值相符 `T11.wild.betti_h0` | 1 | 1 | PASS |
| 120 | p-群代數: 正次上同調非零 (Maschke 在 char p 失效), b_i ≥ 1 `T11.wild.betti_positive` | 1 | 1 | PASS |
| 121 | N = Σ_{g∈G} g ≠ 0 且 N^2 = |G|·N = 0 (char p 下 p | |G|), 故 N ∈ Soc(K[G]) 並生成它 `T11.wild.socle_norm` | 1 | 1 | PASS |
| 122 | 三分類 KIND: 0 = étale (域之積), 1 = p-群代數, 2 = 局部但非群代數; 與 (RAD_DIM, COTANGENT_DIM, GROUP_ORDER) 一致 `T11.wild.kind` | 1 | 1 | PASS |
| 123 | étale ⇔ rad A = 0 ⇔ Tor_1 = 0 ⇔ KIND = 0 `T11.wild.kind_etale` | 1 | 1 | PASS |
| 124 | 局部且 rad A = 0 蘊涵 D = 1 (局部代數簡約 ⇔ 是域 ⇔ 一點) `T11.wild.local_etale` | 1 | 1 | PASS |

**合計 goals = 335，已由 Z3 證明 = 335，失敗 = 0**
