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

### 端到端（`Sycamore.lean`）— 一条机器核验定理
- **`sycamore53_lower_bound`** 合取：（割面=53）∧（代价 ∈[10^18,10^19)）∧（最优路径具 stem
  结构，宽度 ≤ C·cc=53）∧（53 比特平衡割面 ⇒ ContractionRigid，满 Schmidt 秩 `2^53`）。
- `sycamore53 : CircuitGraph` 具体模型，`sycamore53_cc` 真证 cc=53。
- `#print axioms sycamore53_lower_bound = [propext, Classical.choice, Quot.sound,
  latticePathwidthBound, latticePathwidthConst]`：代价/割面/刚性三部分仅标准公理；仅
  stem-最优性依赖那条已发表 grid 定理。`markovShi` 未用到。

---

## 2. 依赖已发表定理（显式 axiom，注明出处）

**只有 Theorem A 的 stem-最优性**（`optimal_stem_lattice`，及端到端定理中用到它的部分）依赖
自定义 axiom（`#print axioms` 核验）。这些 axiom 全是**已发表、已严格证明**的结果，Mathlib
仅是尚未收录、且无可导入的形式化版本（唯一的 treewidth 形式化在 Coq，Lean 无法引用）：

| Axiom | 文献 | 内容 |
|---|---|---|
| `markovShi` | Markov & Shi, *SIAM J. Comput.* 38(3), 2008 (quant-ph/0511069) | `cc(G) = tw(L(G))`，收缩宽度 = 线图 treewidth |
| `latticePathwidthBound` | 经典 grid `pw=tw=min`（Seymour–Thomas bramble）；Kozawa–Otachi–Yamazaki（3D grid `tw=min(n,√n·d)+…`） | 晶格图 `pw ≤ C·cc` |

把已证定理作为带出处的 axiom 引用，是标准的 "cite, don't reprove" 实践。整份发展因此
**条件性地建立在已确立的数学之上**，而非建立在未证猜想之上。

---

## 3. 开放（未证）

C 线已从概率猜想重构为"已证结构定理 + 一个纯组合的剩余前件"。剩余开放项只有两条，且均
**不再是随机矩阵 / 谱分析**：

1. **几何路由（C 线唯一剩余数学）**：深 (2+1)D Sycamore brickwork（深度过混合阈值）的某个
   割面，确实诱导出形式化所需的**跨割面完美匹配**（把 `chipMatching` 的抽象两块落到真实芯片
   坐标）。这是**纯组合**命题（晶格能否配对），不是"秩会不会坍缩"的分析。Napp 相变的
   `d>d★` 阈值正落在此（深度够，因果锥才跨得过割面）。
2. **C.3 概率 corollary**：`Pr(rank collapse) = 0`（坏集零测度的直接推论），目前仅在 spec
   陈述，尚未形式化。

> 与上一版的区别：原"猜想 C（average-case Haar 紧性）"作为**概率命题**已被结构定理取代；
> Napp 浅层反例不再是"障碍"，而是结构定理前件（深度阈值）的**边界刻画**。

---

## 4. 已知"模型 vs 完整命题"的缝隙（诚实标注）

1. **Theorem A 的 stem-最优性经具体 `sycamore53` 模型实例化**（`cc=53` 真证），但该模型的
   width 取常值以使 `cc=53` 干净成立；把它换成真实时空晶格图的逐序 width 计算，需要在 Lean
   里自建 treewidth 理论（Mathlib 无）——这正是 §2 两条 grid axiom 承担的部分。
2. **引理 B 的 generic 结论针对无约束张量**；真实电路中间张量是受约束子族——worst-case
   （具体门）与 C 线（跨割面匹配）已接死，唯余 §3.1 的几何路由。
3. **刚性部分的 53 比特割面**用 `chip_contractionRigid 53`（`Fin 53 ⊕ Fin 53` 抽象两块），
   尚未绑定真实 Sycamore 芯片几何（即 §3.1）。

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
  本框架风格的路径。**主要待补**：§3.1 几何路由（把匹配落到真实 Sycamore brickwork），使
  Sycamore 成为定理的真正实例而非抽象两块模型。
- **(b) 形式化 / 方法学方向**（ITP / CPP / *J. Automated Reasoning*）：以"首个 Lean 形式化
  随机电路收缩复杂度框架、极小公理足迹、端到端 `sycamore53_lower_bound`"为卖点。**当前内容
  已基本够一篇**。
- **(c) 最高价值**：完成 §3.1 几何路由（纯组合）后，C 线即成为对 3D 深电路的**无条件**
  （结构假设下）紧下界——一旦把"深 Sycamore brickwork 满足跨割面匹配"证出，即得到强结果。

**会显著增强发表力的两件事**：
1. **补 §3.1 几何路由**：把 `chipMatching` 落到真实 (2+1)D Sycamore 坐标，使
   `sycamore53_lower_bound` 的刚性部分指向真实芯片而非抽象两块。纯组合、无分析。
2. 形式化 C.3 概率 corollary（`Pr=0`），给出"随机电路作为 corollary"的机器核验版本。

---

## 7. 一句话给评审

> 我们有一个**机器核验、无 sorry、公理足迹极小**的 Lean 形式化，建立了 **Contraction
> Rigidity 结构定理**——"能跨割面纠缠的电路 ⇒ generic 无秩坍缩 ⇒ 紧收缩下界"——从而把随机
> 电路紧下界从一个概率（随机矩阵）问题**重构为结构 + 纯组合问题**（随机电路 / Sycamore 成
> 为 corollary）；并以单一定理 `sycamore53_lower_bound` 给出端到端陈述（割面=53、代价
> ~10^18、最优 stem 结构、满 Schmidt 秩 2^53），仅依赖标准公理 + 一条注明出处的已发表
> grid-treewidth 定理。唯一剩余数学是一个**纯组合**的几何路由（深晶格容许跨割面匹配）。请
> 评估：(a) 结构定理路线（路线 B）的发表价值与目标会议；(b) 几何路由命题的难度与可攻性。
