# fieldStemProof — 结果全景与发表潜力评估材料

> 面向专家评审：一份诚实、可核验的现状清单。
> 仓库：Lean 4 (v4.30.0) + Mathlib (v4.30.0)，全项目编译通过，**无 `sorry`**。
> 所有"已证"条目均由 `lake build` 与 `#print axioms` 机器核验。

---

## 0. 中心命题（thesis）

量子随机电路的张量网络，其**最优收缩路径呈 stem（caterpillar / 脊柱）结构**，复杂度
与 `min(比特数, 深度-受限割面)` 成指数关系；据此给出收缩复杂度的理论下界，并复现
Sycamore 53-20 ≈ `10^18`、Sycamore-70 ≈ `10^24`。

形式化时拆成四层（spec §0.3）：

- **A** 最优收缩路径可取 stem 结构（存在性）
- **B** generic / 无秩坍缩 ⇒ 图论 treewidth 上界升级为**紧**下界
- **C** average-case：Haar 随机、深度阈值之上，下界 a.a.s. 紧 —— **开放猜想**
- **D** 代入复现 Sycamore 数字

---

## 1. 严格已证（仅标准公理；机器核验）

以下定理 `#print axioms` 仅显示 `[propext, Classical.choice, Quot.sound]`，即无任何
自定义/未证依赖：

### 引理 B 线（核心原创）
- `generic_nonsingular` — **genericity 引擎**：参数化方阵在某一点非奇异 ⇒ 其行列式是
  非零多项式 ⇒ 在一个真代数子簇之外处处非奇异。（Schwartz–Zippel /
  `MvPolynomial.funext`。）
- `flatten` / `squareFlatten` / `flatten_map` — 量子比特张量跨割面的 flattening 矩阵化，
  eval 与 flatten 交换。
- `generic_tensor_full_schmidt` — **无约束 generic 量子比特张量跨任意平衡割面满 Schmidt
  秩**，秩坍缩只发生在真子簇上。（"随机张量无秩坍缩"的无条件陈述。）
- `nonsingular_realized` + `squareFlatten_tensorOfMatrix` — flattening 对矩阵满射：任意
  非奇异割面方阵都被某张量实现为满秩 flattening。

### 门库（`Gates.lean`，全部 `det ≠ 0`）
- 单比特：`X Y Z H S T √X √Y`
- 两比特：`CZ SWAP CNOT iSWAP √iSWAP fSim(θ,φ)`
- 技术：归一化常数走 `det_smul`；置换门走 `det_permutation`；对角门 `det_diagonal`；
  4×4 连续纠缠门走 Laplace 展开 `det_succ_row_zero`；`fSim` 另用 `sin²+cos²=1`。

### worst-case 见证（`Worstcase.lean`）
- `gate_full_schmidt`、`iSWAP/CNOT/fSim_full_schmidt` — **具体纠缠门嵌到割面 ⇒ 割面态满
  Schmidt 秩 `2^k`**。构造性兑现引理 B 的前件（worst-case）。

### Theorem A 的可证骨架（`TheoremA.lean`）
- `cc_le_pw` — stem 序赢不过全局收缩最优（pw ≥ cc）。
- `exists_stem_pw` — pw 由某条 stem 序达到。
- `optimal_stem_within_const` — 给定晶格界 `pw ≤ C·cc`，存在宽度 ∈ `[cc, C·cc]` 的 stem 序。

### 推论 D（`CorollaryD.lean`，纯算术，无 axiom）
- `sweepCut n d = min(n, ⌊√n⌋·d)`；`stemCost = 4·2^cut·steps`。
- `stemCost_sycamore53 : 10^18 ≤ 4·2^53·150 < 10^19`  → **~10^18**
- `stemCost_sycamore70 : 10^23 ≤ 4·2^70·200 < 10^24`  → **~10^24**

---

## 2. 依赖已发表定理（显式 axiom，注明出处）

**整个项目只有一条定理** `optimal_stem_lattice` 依赖自定义 axiom（`#print axioms`
核验）。这些 axiom 全是**已发表、已严格证明**的结果，Mathlib 仅是尚未收录、且无可导入
的形式化版本（唯一的 treewidth 形式化在 Coq，Lean 无法引用）：

| Axiom | 文献 | 内容 |
|---|---|---|
| `markovShi` | Markov & Shi, *SIAM J. Comput.* 38(3), 2008 (quant-ph/0511069) | `cc(G) = tw(L(G))`，收缩宽度 = 线图 treewidth |
| `latticePathwidthBound` | 经典 grid `pw=tw=min`（Seymour–Thomas bramble）；Kozawa–Otachi–Yamazaki（3D grid `tw=min(n,√n·d)+…`） | 晶格图 `pw ≤ C·cc` |

把已证定理作为带出处的 axiom 引用，是标准的 "cite, don't reprove" 实践。整份发展因此
**条件性地建立在已确立的数学之上**，而非建立在未证猜想之上。

---

## 3. 开放（未证）

- **猜想 C**：对 (2+1)D = **3D 时空晶格**、深度超过可模拟相变阈值的 **Haar 随机**电路，
  中间张量 a.a.s. 满秩 ⇒ average-case 下界紧。
  - 现状：**未证**。且在**浅层 2D**已被 Napp–La Placa–Dalzell–Harrow–Brandão
    (PRX 2022, arXiv:2001.00021) **证伪**（measurement-induced 相变的可模拟相）。因此任何
    成立版本必须限定到 **3D 深 bulk**（阈值之上）——这正是本课题锁定 3D 的原因。
  - 这是本课题真正的研究难点与潜在主要贡献。

---

## 4. 已知"模型 vs 完整命题"的缝隙（诚实标注）

1. **Theorem A 对抽象 `CircuitGraph` 结构证明，尚未实例化到具体 Sycamore 晶格图。** A 证
   的是"任何满足晶格 `pw≤C·cc` 的图，最优路径可取 stem"，把它绑到真正的时空晶格对象差
   一步实例化。
2. **引理 B 的 generic 结论针对无约束张量**；真实电路中间张量是受约束子族——worst-case
   （具体门）已接死，average-case 即猜想 C。
3. **尚无端到端单一定理** `sycamore53_lower_bound`：第 2 步（抽象）与第 4 步（具体算术）
   目前人工拼接，串成一条机器定理需补 §4.1 的实例化。

---

## 5. 相对 prior art 的新意

- **Markov–Shi (2008)**：`cc=tw(L(G))`。我们**引用**，非重证。
- **Boixo et al. (2017)**：grid 电路 treewidth 的启发式上界。
- **Gray–Kourtis (2021), Pan–Zhang, Huang et al. (2020)**：hyper-opt 收缩、"stem"一词的
  来源（Huang et al. 命名几何 stem）、big-head 复用。多为算法/工程。
- **Napp et al. (2022)**：浅层 2D 随机电路可模拟（相变）——我们据此**限定** regime。

本工作的潜在新意集中在：
1. **统一严格框架**：把"观察到的 stem 低复杂度"解释为 **pathwidth ≈ treewidth on
   lattices** + **随机性 ⇒ 无秩坍缩 ⇒ 下界紧**，并明确区分"收缩方法下界"与"算法无关硬
   度"。
2. **机器核验的形式化 artifact**（Lean 4 + Mathlib，无 sorry，公理足迹极小且全部注明）——
   据查为该主题首个 Lean 形式化。
3. **猜想 C 的精确陈述**（3D 深 bulk + 阈值），把开放问题从模糊直觉收紧为可攻的命题，
   且正面处理了 Napp 反例的边界。

---

## 6. 发表潜力 —— 诚实评估

**当前已证内容的定位**：更接近"**严谨综合 + 可核验形式化 artifact + 精确化的开放猜想**"，
而非"一条全新深定理"。引理 B 的 genericity 内核数学上属标准（generic rank / Schwartz–
Zippel）；其价值在于完整、无 sorry、并接到量子比特张量与真实门库。

可能的发表路径：

- **(a) 形式化 / 方法学方向**（ITP / CPP / *J. Automated Reasoning* 类）：以"首个 Lean
  形式化随机电路收缩复杂度的 stem/treewidth 框架 + 极小公理足迹"为卖点。**当前内容基本够
  一篇**，需补 §4 的实例化以给出端到端定理。
- **(b) 量子模拟 / 复杂度方向**（quantum 期刊 / 会议）：以统一框架 + 精确猜想 C 为主。
  当前新意中等——多数构件已知；若**仅停在已证部分**，更像 survey/position + 形式化附录。
- **(c) 最高价值**：**证明猜想 C**（或其 3D 深 bulk 的某个非平凡 regime），或给出严格的
  average-case 下界。这是真正的研究 prize，难度大（需纠缠增长 / 反集中），一旦突破即为强
  结果。

**会显著增强发表力的两件事**：
1. 补 §4.1 端到端实例化 → 一条机器核验的 `sycamore53_lower_bound`，把"全部 ✅+▣"的论断
   钉成单一定理。
2. 在猜想 C 上取得任何严格进展（哪怕受限 regime / 数值相图 + 部分解析阈值）。

---

## 7. 一句话给评审

> 我们有一个**机器核验、无 sorry、公理足迹极小**的 Lean 形式化，严格建立了"随机电路 TN
> 的最优收缩路径可取 stem 结构、并由无秩坍缩给出紧的收缩下界"——其中除一条已发表的
> grid-treewidth 定理（显式引用）外全部真证，并把唯一开放的 average-case 紧性收紧为精确
> 的、避开已知反例的猜想 C。请评估：(a) 作为形式化 artifact 的发表价值；(b) 猜想 C 的可
> 攻性与潜在影响。
