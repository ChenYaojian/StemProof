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
- **C** **Contraction Rigidity（结构定理，已证）**：把原"average-case 概率猜想"重述为
  *结构*命题——"能跨割面纠缠（BulkEntangling）⇒ generic 满秩（无秩坍缩）"，随机电路 /
  Sycamore 成为 corollary，**绕开随机矩阵 `Pr(·)` 分析**。前件（跨割面匹配）经
  Kronecker 路由约化为**纯组合**条件。
- **D** 代入复现 Sycamore 数字
- **端到端**：`sycamore53_lower_bound` 单一定理合取 A+C+D（见 §1）。

> **本轮重大进展**：C 从"开放概率猜想"重构为"已证结构定理 + 一个纯组合的剩余前件"。这
> 是路线 B（结构 / 复杂度理论）对路线 A（随机矩阵概率）的替代，与本框架"图结构 + 代数几何
> genericity + 张量秩"的风格契合。

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

### C 线 — Contraction Rigidity 结构定理（`Rigidity` / `Matching` / `Lattice`，仅标准公理）
原"猜想 C"重构为已证结构定理，全部 `#print axioms` 仅标准公理：
- `BulkEntangling` / `ContractionRigid` / **`contraction_rigidity`** — *能跨割面纠缠
  （∃ 一个使割面满秩的门配置）⇒ generic 满秩*（`generic_full_schmidt` 的具名推论，无概率）。
- `Matching.det_bondProd_ne_zero` — **Kronecker 路由聚合**：k 个非奇异 bond 的迭代 Kronecker
  积满秩 = 满 Schmidt 秩 `2^k`（对 k 归纳，`Fin.consEquiv` + `det_kronecker`）。
- `bulkEntangling_of_matching` / `contractionRigid_of_matching` — 跨割面 k-匹配 ⇒ BulkEntangling
  ⇒ rigid。
- `matching_contractionRigid` — **以跨割面匹配 μ 为显式数据**（路线 B 形式）；
  `chipMatching` / `chip_contractionRigid` — `Fin m ⊕ Fin m` 链上**参数化显式几何匹配**
  （左 j ↔ 右 j，对所有 m）。

### 端到端（`Sycamore.lean` + `GridModel.lean`）— 一条机器核验定理，**忠实模型**
- **`sycamore53_lower_bound`** 合取：（割面=53）∧（代价 ∈[10^18,10^19)）∧（stem：最优由 stem
  序达到 ∧ 任意序宽度 ≥ 27 ∧ 显式 sweep 序宽度 ≤ 106，即 `cc = Θ(53)` 两侧钉死）∧（53 比特
  平衡割面 ⇒ ContractionRigid，满 Schmidt 秩 `2^53`）。
- **模型退化性已消除**（`GridModel.gridModel`）：`Order` = 真实 53×53 时空 grid 图
  （`gridGraph 53`，1D 链深 regime 时空晶格）的**全体真路径分解**（`IsPathDecomp` 三公理：
  vertex-interval / edge-cover / vertex-cover），`width` = 分解的实际最大 bag ——**无任何
  postulated 量**。下界来自自证 bramble 定理（`grid_pathwidth_lower_unconditional`，
  `∀ 序: 53 ≤ 2·width`）；上界来自显式双列 sweep 分解（`sweepBags`，`width ≤ 106`）；
  `27 ≤ cc ≤ 106`（`sycamore53_cc_bounds`）。`IsStem ≡ True` 在此为**定义性**而非退化：
  该模型的序空间本就是线性（stem）序全体；推广到树序即 `pw=Θ(tw)` 文献输入。
- `#print axioms sycamore53_lower_bound = [propext, Classical.choice, Quot.sound]`：**全库已无
  任何自定义 axiom**。文献输入（`MarkovShi` / `LatticePathwidthBound`）改为具名 `Prop`、按具体
  模型供给；lattice 界在模型上以 `C = 1` 兑现（`sycamore53_latticeBound`），端到端定理成为
  无条件机器定理（剩余保真度缝隙见 §4）。

### stem 宽度下界（`Bramble` / `GridConn`，**自证，零自定义 axiom**）
原本作为引用 axiom 的"最优割面不能更小"（grid treewidth 下界），现对 **stem/pathwidth 宽度
完全自证**（`#print axioms` 仅标准公理）。走 pathwidth（stem=路径分解，只需**区间 Helly**，
而非 Mathlib 缺失的子树 Helly）+ Θ 常数策略：
- `interval_helly` — 两两相交区间共点（公共点 = 最大左端点），初等心脏。
- `order_le_maxBag` / `order_le_maxBag'` — 抽象 pathwidth bramble 下界：路径分解最大 bag
  ≥ bramble order。
- `cross k i = row i ∪ col i`；`cross_inter_nonempty`（两两相交，真 bramble）；
  `cross_order_ge`（`k ≤ 2·order`，行/列投影计数，Θ(k)；精确值 k+1 但 Θ 足够）。
- `walk_hits` / `bag_meets_betweenness` — **连通 ⇒ 区间桥**：沿 G-walk 归纳，每条边经同一 bag
  ⇒ 顶点区间成重叠链 ⇒ 连通顶点集占据连续 index 区间。
- `pathwidth_ge_order_of_connected` — 组装：任意图 G 的任意路径分解 + 两两相交且 G-连通的
  bramble ⇒ maxBag ≥ order。
- `GridConn`：`gridGraph k = pathGraph k □ pathGraph k`（真最近邻 grid）；`cross_connected`
  （盒积嵌入 + `pathGraph_preconnected` 路由到中心，证十字 G-连通）；
  **`grid_pathwidth_lower_unconditional`** — grid 图的任意路径分解 ⇒ `k ≤ 2·maxBag`，即 stem
  宽度 ≥ k/2−1 = **Θ(min(n,√n·d))**，`#print axioms` = `[propext, Classical.choice,
  Quot.sound]`，**无任何自定义 axiom**。

> **影响**：审稿人最初的两问——(Q2)"该 scale 是否为下界"——对 **stem 路径本身**现在是无条件
> 机器定理，不再依赖引用的 treewidth 下界。原 `Spacetime.treewidthLowerBound` axiom 对 stem
> 宽度已被兑现。

### P1 拱心石：deep Sycamore ⇒ Ω(min(n,√n·d)) matching（`Brickwork` / `Causal`，自证）
把"割面宽（bramble）"与"宽割面满秩（rigidity）"接成单条 cost 下界，并把 matching 的 size 钉到
bramble scale。三层，全部 `#print axioms` 仅标准公理：
- **拱心石**（`Brickwork.deep_brickwork_contractionRigid`）：size 为 `sweepCut = min(n,√n·d)` 的
  割面 matching 收缩刚性 ⇒ generic 满 Schmidt 秩 `2^min`；`sycamore53_matching_rigid`（size 53,
  秩 `2^53`）。`min` 自动覆盖两 regime：deep ⇒ n，shallow ⇒ √n·d（Napp 相变所在）。
- **gate-counting 上界**（`Brickwork.Schedule`）：brickwork = d 层、每层 ≤ b 个跨割面门；
  `routed_card_le` **证明** bond ≤ `b·d`（`card_biUnion_le_card_mul`，lightcone 计数，非假设）；
  `exists_schedule_routed_card` 达到 `min(b·d, n)`。
- **因果可达**（`Causal`，bond = 真实芯片比特对，非抽象标签）：`chain_reach`（链上间距 k ⇒
  长度 k 的 walk）；`bond_causal`（第 i 对链距 2i+1 ≤ 2d ⇒ 在深度 d 的 lightcone 内，1D）；
  `grid_bond_causal` + `grid_causal_matching_size`（2D 芯片 `pathGraph(2m)□pathGraph(K)`：行内
  对复用链 walk 经 `boxProdLeft` 抬升，K·min(m,d) = 方芯片下 `min(n/2,√n·d)`）。

> **影响**：审稿人 Q2 的全部环节现在都有机器核验的几何/组合证据——**为什么是 min**（算术）、
> **为什么 b·d 封顶**（gate-counting）、**为什么深度 d 能实现这些 bond**（lightcone walk，1D+2D）。
> "deep ⇒ Ω(min) matching"不再有抽象隔离或物理 hand-waving。

---

## 2. 依赖已发表定理（显式假设 `Prop`，注明出处；**全库零自定义 axiom**）

> **soundness 修正（2026-08）**：原先三条全局 `axiom`（`markovShi` / `latticePathwidthBound` /
> `treewidthLowerBound`）量化在字段自由的抽象结构上，均可被对抗实例证伪（Lean 内可推出
> `False`，已构造验证）。现已全部改写为**具名 `Prop` / 定理显式假设**，按具体模型供给；
> `grep "^axiom"` 全库为空。

经 bramble 下界自证后，**唯一剩余的文献输入是 `pw = Θ(tw)`（"stem 是全局最优"）**：把
已自证的"stem 宽度 ≥ Θ(min)"推广到"一切（树）收缩也不更省"。这是一条**已发表、已严格证明**
的结果，Mathlib 尚未收录且无可导入的形式化版本（唯一的 treewidth 形式化在 Coq，Lean 无法
引用）：

| 具名 `Prop` / 假设 | 文献 | 内容 | 状态 |
|---|---|---|---|
| `MarkovShi G` | Markov & Shi, *SIAM J. Comput.* 38(3), 2008 (quant-ph/0511069) | `cc(G) = tw(L(G))`，收缩宽度 = 线图 treewidth | 具名 `Prop`（按模型供给；端到端定理未用） |
| `LatticePathwidthBound G C` | 经典 grid `pw=tw`（Seymour–Thomas bramble）；Kozawa–Otachi–Yamazaki | 晶格 `pw ≤ C·cc`（stem 全局最优） | 具名 `Prop`；**在 `sycamore53` 模型上以 `C=1` 由计算兑现** |
| `optimalWidth_eq_min` 的 `hlow` | Kozawa–Otachi–Yamazaki；Seymour–Thomas | 一切收缩宽度 ≥ `min(n,√n·d)` | 显式假设；stem/pathwidth 方向已自证（`GridConn`） |

明确区分两个不同命题：**"stem 宽度 ≥ Θ(min)"已自证**（任何 stem 收缩不能更省）；仍引用的是
**"最优树收缩 ≤ stem"（pw=Θ(tw)）**，把下界从 stem 推广到一切收缩路径。文献输入以显式假设
出现在定理签名里（而非全局 axiom），是比 "cite as axiom" 更强的实践：`#print axioms` 全库仅
标准公理，引用之处在陈述中可见。

---

## 3. 开放（未证）

C 线已从概率猜想重构为"已证结构定理 + 纯组合前件"，且 P1（几何路由 / matching 实现）这一组合
前件已大体兑现（`Brickwork` + `Causal`，见 §1）。剩余开放项只有两条，均**不再是随机矩阵 /
谱分析**：

1. **`pw = Θ(tw)`（唯一剩余文献输入，以显式假设出现）**：把已自证的"stem(pathwidth) 宽度 ≥
   Θ(min)"推广到"一切(树)收缩也不更省"。需子树 Helly + 树分解理论（Mathlib 缺）。形式化它可
   把该假设从定理签名中彻底移除（见 §6）。
2. **C.3 概率 corollary**：`Pr(rank collapse) = 0`（坏集零测度的直接推论），目前仅在 spec
   陈述，尚未形式化。

> 与上一版的区别：原"猜想 C（average-case Haar 紧性）"作为**概率命题**已被结构定理取代；P1 的
> 几何路由（"深 brickwork 容许 Ω(min) 跨割面 matching"）已由 gate-counting + lightcone 因果可达
> （1D & 2D）机器证明，不再是开放项。Napp 浅层反例是结构定理前件（深度阈值）的**边界刻画**。

---

## 4. 已知"模型 vs 完整命题"的缝隙（诚实标注）

1. **~~模型退化性~~（已解决，`GridModel`）**：原 `sycamore53` 玩具模型（`Order := Unit`、
   width 恒 53）已替换为**忠实模型**——序空间 = 真实 53×53 时空 grid 图的全体路径分解，宽度
   为派生量，下上界均机器证明（`27 ≤ cc ≤ 106`）。剩余两点保真度缝隙：(i) 序空间为 stem
   （线性）序全体，推广到任意树收缩序即 `pw=Θ(tw)` 文献输入（以显式假设携带）；(ii) grid 为
   1D 链深 regime 的时空晶格，(2+1)D 芯片晶格的 bramble 版本待做（matching 侧已由 `Causal`
   覆盖 2D 芯片）。精确常数（27 vs 53）是 Θ-常数策略的代价，非方法缺陷。
2. **引理 B 的 generic 结论针对无约束张量**；真实电路中间张量是受约束子族——worst-case
   （具体门）、C 线（跨割面匹配）、P1（gate-counting + 因果可达）均已接死。
3. **P1 因果模型的几何保真度**：`Causal` 用 1D 链（`pathGraph`，b=1）与 2D 方芯片
   （`pathGraph□pathGraph`，b=√n）；真实 Sycamore 是带 ABCD 门花样的具体 (2+1)D brickwork。
   min(n,√n·d) 的 scale 与每个 bond 的 lightcone 可达性已证；ABCD 具体调度是进一步保真度，对
   Ω 下界非必要。

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
2. **Contraction Rigidity 结构定理（核心新意）**：把"随机电路 average-case 紧性"从概率命题
   重构为结构命题——"能跨割面纠缠 ⇒ generic 无秩坍缩"，并经 **Kronecker 路由**把前件约化为
   *纯组合*的跨割面匹配条件。这把一个拥挤的随机矩阵问题，换成了干净的代数几何 + 组合命题，
   随机电路 / Sycamore / supremacy circuits 成为统一 corollary。
3. **机器核验的形式化 artifact**（Lean 4 + Mathlib，无 sorry，公理足迹极小且全部注明）——
   据查为该主题首个 Lean 形式化，并以单一定理 `sycamore53_lower_bound` 给出端到端陈述。

---

## 6. 发表潜力 —— 诚实评估

**当前已证内容的定位**：一个**机器核验的统一框架 + 一条原创结构定理（Contraction
Rigidity）+ 端到端 Sycamore 实例**。相比上一版，C 线的 reframing 实质提升了新意——它不再是
"标准工具的综合 + 开放概率猜想"，而是把该领域长期作为概率问题处理的"随机电路紧下界"，**降
维成一个结构 + 组合命题**（路线 B）。引理 B 的 genericity 内核虽属标准技术，但其封装成
rigidity 定理、并约化随机性的整体论证是新的。

可能的发表路径：

- **(a) 复杂度 / 理论 CS 方向**（CCC / ICALP / Quantum）：以 **Contraction Rigidity 结构
  定理 + "什么电路必然有量子优越性"**为主线，随机电路作为 corollary。这是新意最高、最契合
  本框架风格的路径。P1（几何路由：deep ⇒ Ω(min) matching）已由 gate-counting + lightcone
  因果可达（1D & 2D）机器证明，Sycamore 不再是抽象两块而有真实芯片图的因果支撑。
- **(b) 形式化 / 方法学方向（已定路线：CPP 2027 → JAR 扩展版）**：以"首个 Lean 形式化
  随机电路收缩复杂度框架、**全库零自定义 axiom**（文献输入以显式假设出现并在具体模型上兑现）、
  端到端 `sycamore53_lower_bound`"为卖点。**当前内容已充分够一篇**。CPP 2027 摘要 2026-09-03、
  正文 2026-09-10（AoE）；会后按惯例扩展 ~30% 投 *J. Automated Reasoning*（CCF B）。
- **(c) 最高价值（JAR 扩展版目标）**：形式化 `pw=Θ(tw)`（子树 Helly）后，stem 下界对一切
  收缩路径成为无条件（结构假设下）紧下界，`hlow`/`LatticePathwidthBound` 假设从定理签名中
  彻底消失。

**会显著增强发表力的两件事**：
1. **形式化 `pw=Θ(tw)`**（P2，子树 Helly + 树分解）：移除最后一条文献输入假设（JAR 版核心增量）。
2. 形式化 C.3 概率 corollary（`Pr=0`），给出"随机电路作为 corollary"的机器核验版本。

---

## 7. 一句话给评审

> 我们有一个**机器核验、无 sorry、全库零自定义 axiom**的 Lean 形式化，建立了 **Contraction
> Rigidity 结构定理**——"能跨割面纠缠的电路 ⇒ generic 无秩坍缩 ⇒ 紧收缩下界"——从而把随机
> 电路紧下界从一个概率（随机矩阵）问题**重构为结构 + 纯组合问题**（随机电路 / Sycamore 成
> 为 corollary）；并以单一定理 `sycamore53_lower_bound` 给出端到端陈述（割面=53、代价
> ~10^18、**忠实模型**上 stem 最优达到且 `cc=Θ(53)` 两侧钉死、满 Schmidt 秩 2^53），`#print axioms` 仅标准公理。**stem(pathwidth)
> 宽度下界 Θ(min(n,√n·d)) 与"deep ⇒ Ω(min) 跨割面 matching"（gate-counting + lightcone 因果
> 可达，1D & 2D）均已完全自证**；唯一剩余的文献输入是 `pw = Θ(tw)`（把 stem 下界推广到一切
> 收缩，已发表 grid 定理），以显式假设出现在定理签名中、并在具体 Sycamore 模型上由计算兑现。
> 投稿路线：CPP 2027（2026-09 截稿）→ JAR 扩展版（形式化 `pw=Θ(tw)` 为核心增量）。
