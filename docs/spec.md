# 随机量子电路张量网络的 stem 结构与最优收缩复杂度

> 设计文档 / 定理草稿（spec A）
> 日期：2026-06-06
> 状态：待评审

---

## 0. 命题与精炼

### 0.1 原始命题（用户）

> 量子电路转化成的张量网络，收缩时计算复杂度较低的收缩路径一般都呈现 **stem 结构**。它的收缩过程很像 state vector 与量子门相乘，最终复杂度几乎与 `min(量子比特数, 深度)` 成指数关系。目标：把量子随机电路的张量网络严格定义出来，确定其性质，并证明其**最优收缩路径具备 stem 结构**，从而基于 stem 结构给出近似的理论复杂度下界。

例证（需被框架复现）：

- Sycamore 53-20：`≈ 4 · 2^53 · steps(100~200) ≈ 10^18`
- Sycamore 70：`≈ 4 · 2^70 · steps ≈ 10^24`

### 0.2 术语对齐（文献核实结论）

"stem" 一词由 Huang et al.（arXiv:2005.06787, §4 + Fig.1）**首创并命名**，且就是**几何形状义**：收缩树中一条由高代价节点构成的近线性主路径（stem），其上挂载若干低代价小簇（branches），"a single big tensor absorbs small tensors **sequentially**"。这与用户"像 state vector × 门"的直觉逐字吻合。后续 SW-TNC（arXiv:2504.09186）扩展出 **multi-stem**，并观察到 Sycamore 单 stem 主导、Zuchongzhi 多为 multi-stem。

> 注意区分：Pan–Zhang 的 **big-head / `Ghead`–`Gtail`** 与 Kalachev 的 **subtree/common-subexpression reuse** 是**计算复用义**，文献中**不叫 stem**。本 spec 全程使用几何义。

### 0.3 精炼后的命题（本 spec 实际证明对象）

把"所有最优路径都是 stem"（在一般图上为假）收紧为**存在性 + 紧性下界**，并分层处理可证性：

> **设 C 为格点几何上的随机量子电路，G 为其张量网络的（线）图。则**
> **(A) 存在性**：存在一条 stem（caterpillar）收缩路径，其收缩宽度 = `tw(G)`，即达到全局最优；
> **(B) 紧性（generic）**：对除零测度外的门参数，沿该路径中间张量满秩，故 `Θ(2^{tw}) · steps` 是收缩法的紧下界；
> **(C) 紧性（average-case, 前沿）**：对足够深（超过可模拟相变阈值）的 Haar 随机电路，上述紧性几乎必然（a.a.s.）成立——**作为猜想列出**；
> **(D) 推论**：`tw(G)` = 最小横截分隔面 = `min(n, d)` 类量，复现 Sycamore 数字。

---

## 1. 定义层

### 1.1 随机量子电路 ensemble

**定义 1.1（架构 + 随机赋值）.** 一个量子电路架构 `A = (n, d, L, {G_t})` 由比特数 `n`、深度 `d`、几何 `L`（比特的连接图，1D 链 / 2D 芯片网格）、各层门的**支撑位置**（哪些比特对在第 `t` 层作用两比特门）构成。随机电路 ensemble `𝒞(A, μ)` 通过给每个门独立采样酉矩阵得到：单比特门、两比特门的酉部分按测度 `μ`（典型取每个两比特门的 Haar 测度，或 fSim/√iSWAP 类固定纠缠门 + 随机单比特门，对齐 Sycamore）。

**约定**：所有门为两比特或单比特，故底层 TN 度 ≤ 4（用于后续 line-graph treewidth 的常数化）。

**定义 1.1′（时空晶格几何，本课题的主靶子）.** 关键区分 TN(C) 底层图的**时空维数**：

- 比特排在 1D 链、加时间轴 → TN 图是 **2D 网格** `n × d`。
- 比特排在 2D 芯片（Sycamore/Zuchongzhi）、加时间轴 → TN 图是 **(2+1)D = 3D 时空晶格**，bulk 为真三维。

**本课题锁定 3D 时空晶格 + 深度 `d` 充分大（bulk 厚）的 regime。** 这一限定有两重作用：(i) Napp et al. 的相变反例（§2 [M4]）是**浅层 2D**（时间方向薄、退化成准 1D 测量动力学），其可模拟相**够不到 3D 深 bulk**；(ii) 3D 晶格的最小割是真正的二维分隔面，treewidth 随 `min(n, √n·d)` 增长，与 Sycamore 数字对齐（§3 推论 D）。后文凡言"格点"，主结果均指此 3D 时空晶格；2D（1D 比特链）作为可完全证清的对照基例保留。

### 1.2 电路的张量网络与图

**定义 1.2（TN(C)）.** 给定 `C ∈ 𝒞(A, μ)` 及一个标量目标（单振幅 `⟨x|C|0^n⟩`、一批振幅、或期望值 `⟨0|C^† O C|0⟩`），其张量网络 `TN(C)`：每个门为一个张量，键（共享指标）按电路连线连接，开放指标按目标固定/求和。

- **网络图 `G`**：顶点 = 张量，边 = 键（含悬挂的开放指标）。
- **线图 `L(G)`**：把 `G` 的边作为顶点，原共享一个张量的边相邻。

> Markov–Shi 的收缩宽度等式作用在 `L(G)` 上；对度 ≤ 4 的电路图，`tw(L(G)) = Θ(tw(G))`（Markov–Shi Lemma 4.4）。为叙述简洁，下文 `tw`、`pw` 默认指 `L(G)`，必要处显式区分。

### 1.3 收缩树、收缩宽度

**定义 1.3（收缩树 / 收缩宽度）.** 一棵**收缩树** `T` 是把 `TN(C)` 化为单个张量的一串成对合并（`G` 的边的层次二分）。沿 `T` 出现的最大中间张量的指标数记为 `width(T)`；**收缩宽度** `cc(G) = min_T width(T)`。收缩的时间复杂度 `= Θ(Σ_v 2^{indices(v)}) = Θ(2^{width(T)} · |steps|)`（由最宽步主导）。

### 1.4 stem / caterpillar 收缩树与 pathwidth

**定义 1.4（stem / caterpillar 收缩树）.** 一棵收缩树 `T` 称为 **stem 型（caterpillar）**，若删去所有叶子后剩下一条路径（脊柱 spine）。等价地：存在一个对张量的线性序 `τ_1, …, τ_m`，收缩按"维护一个累积张量 `S`，依次把 `τ_i` 吸收进 `S`"进行——即 state-vector 风格的 sweep。其上每个吸收点的 `width` 由当时"已吸收 / 未吸收"边界的**割**决定。

**定义 1.5（pathwidth）.** `pw(H)` 为图 `H` 的路径分解最小宽度。**事实**：stem 型收缩序的最优收缩宽度 `= pw(L(G))`（线性序 ↔ 路径分解；这是 Def 1.3 在"序为线性"约束下的特例）。

### 1.5 横截分隔面（cut）

**定义 1.6（最小横截分隔面）.** 对格点几何，沿某方向（时间轴 / 空间轴）把电路切成两半所需切断的键数的最小值，记 `s(A)`。直觉：sweep 的边界张量大小 = 当前割面大小。

---

## 2. 已知结论（引用，不重证）

**[M1] Markov–Shi（arXiv:quant-ph/0511069, Prop 4.2 / Thm 4.6）.**
`cc(G) = tw(L(G))`（**等式，无常数**）。一棵宽度 `d` 的 `L(G)` 树分解可转成收缩宽度 ≤ `d` 的收缩序；反之任何收缩序在某步必形成 ≥ `tw(L(G))` 指标的张量。模拟时间上界 `T^{O(1)} · exp(O(tw))`。
> 注意：这是**收缩法**的最优性刻画 + 上界，**不是**"所有经典算法都需 `2^tw`"的硬度下界（Clifford 反例、decision-diagram 反例存在）。

**[M2] 网格 pw = Θ(tw)（经典图论）.** `n×n` 网格 `tw = n`，`pw = Θ(n)`；一般图 `pw = O(tw·log n)`，差距由"完全二叉树 minor"障碍刻画（Groenland et al. arXiv:2008.00779）。**网格不含大完全二叉树 minor，故 `pw/tw = O(1)`。** 这正是 stem（=pathwidth 实现）在格点上**不吃亏**的机制，而在树状/expander 电路图上会吃亏。

**[M3] 电路网格 treewidth 值（Boixo et al. arXiv:1712.05384）.** 深度 `d`、`ℓ×(n/ℓ)` 芯片（`ℓ` 为较短边）：`tw = Θ(min(d·ℓ, n))`（上界，QuickBB 启发式）。

**[M4] 相变反例（Napp–La Placa–Dalzell–Harrow–Brandão, arXiv:2001.00021, PRX 2022）.** 存在 worst-case 难、`tw = Ω(n)` 的**随机浅层 2D** 电路族，几乎所有实例可线性时间近似模拟（measurement-induced 相变的可模拟相）——即随机性**不**自动保证下界紧。约束了 §4 猜想 C 的适用 regime。

---

## 3. 主定理（分层）

### 定理 A（存在最优 stem 路径）— 可证·拼装

> 设 `C` 为格点几何 `L` 上的电路，`G = L(TN(C))`。则存在一棵 stem 型收缩树 `T★`，满足 `width(T★) = pw(G) = Θ(tw(G)) = cc(G)`。即：**在格点上，存在一条达到全局最优收缩宽度（仅差常数）的 stem 路径。**

**证明骨架.** (1) 由 [M2]，格点图 `pw(G) = Θ(tw(G))`。(2) 取实现 `pw(G)` 的路径分解，按其袋序构造线性吸收序 → stem 型 `T★`，`width(T★) = pw(G)`（Def 1.5 事实）。(3) 由 [M1]，`cc(G) = tw(G)`，故 `width(T★) = Θ(cc(G))`。∎

**待补严格度**：(2) 的"路径分解 → 收缩序"映射在悬挂开放指标存在时的常数；(M2) 的常数对 1D（`n×d` 网格）是 1，对 2D（3D 时空格）需引用/重算分隔面定理的常数。

### 引理 B（generic 紧性，无秩坍缩）— 可证·原创核心

> 沿 `T★` 收缩，设第 `i` 步累积张量 `S_i` 的开放指标集对应割 `cut_i`（`|cut_i| ≤ pw(G)`）。则存在一个关于全体门矩阵元的非零多项式 `P`，使得只要门参数 `θ ∉ {P = 0}`（一个零 Lebesgue 测度的代数簇），每个 `S_i` 的相应 flattening 满秩 `= 2^{|cut_i|}`。从而沿 `T★` 实际收缩宽度 = `pw(G)`，`Θ(2^{pw(G)}) · steps = Θ(2^{tw(G)}) · steps` 是该路径代价，且为收缩法紧下界。

**证明骨架（Schwartz–Zippel / generic rank）.** `S_i` 的 flattening `M_i(θ)` 是门矩阵元的多项式矩阵。取某一具体门赋值（如恒等 + 一个最大纠缠门构造）使 `M_i` 满秩 ⇒ 其某个 `2^{|cut_i|}` 阶子式 `≠ 0` ⇒ 该子式作为 `θ` 的多项式非零 ⇒ 其零集是零测度代数簇。对所有 `i` 取并仍零测度。∎

**待补严格度**：(a) "存在一个赋值使 `M_i` 满秩"需要构造——这一步把"格点割面 `≥` 对应纠缠"显式化，是引理真正的技术负担；(b) 需说明 `|cut_i|` 沿 stem 的分布（SW-TNC 观察到呈"纺锤/spindle"，两端小中间大），紧性只需 `max_i |cut_i| = pw`。

### 猜想 C（average-case, 阈值之上）— 前沿·诚实标注

> 存在深度阈值 `d★(L)`（与几何相关），使得对 `d > d★` 的 Haar 随机电路 `C ~ 𝒞(A, μ_Haar)`，引理 B 的满秩 a.a.s. 成立；即 `2^{tw} · steps` 是 average-case 紧的收缩下界。

**为何只能是猜想**：[M4] 证明了 `d < d★` 时随机浅层电路发生秩坍缩、可高效模拟，故无阈值限制的版本**为假**。`d★` 对应 measurement-induced entanglement 相变点。证明需把"随机门 ⇒ 中间张量谱不坍缩"与相变阈值定量挂钩——**目前文献无此证明，是本课题最大原创空间，也是最难部分**。

### 推论 D（复现 Sycamore 数字）— 可算

> `tw(G) = s(A)`（最小横截分隔面）。沿时间轴 sweep：边界 = `n` 比特 ⇒ `2^n`；沿空间轴 sweep：边界 `~ √n · d`。`tw = min(n, √n·d)` 量级（[M3] 的 `min(d·ℓ, n)` 形式）。

- Sycamore 53-20：时间向 `2^53` < 空间向 `2^{√53·20}` ⇒ `tw=53` ⇒ `4·2^53·steps ≈ 10^18` ✓
- Sycamore 70：`2^70·steps ≈ 10^24` ✓

用户原式 `min(n,d)` 的指数，对"够深"的 Sycamore 落在空间边界 `n` 上；框架自动给出该 min 的取值方向。

---

## 4. 证明依赖图与难度评级

```
[M1 Markov–Shi]──┐
                 ├──► 定理A（存在最优stem）        难度: 低（拼装+常数核算）
[M2 grid pw=tw]──┘         │
                          ▼
[构造满秩赋值]──► 引理B（generic紧性）            难度: 中（原创，技术负担在满秩构造）
                          │
[M4 Napp相变]──► 猜想C（average-case阈值）        难度: 高（open，本课题核心贡献）
                          │
[M3 Boixo值]──► 推论D（Sycamore数字）             难度: 低（代入）
```

**模块边界（便于分工 / 独立验证）**：

| 模块 | 输入 | 输出 | 可独立验证方式 |
|---|---|---|---|
| 定义层 §1 | 用户命题 | 形式化定义 | 自洽性、与文献术语一致性 |
| 定理 A | M1, M2 | 存在性 | 对 1D `n×d` 网格手算 pw=tw=min(n,d) |
| 引理 B | A, Schwartz–Zippel | generic 下界紧 | 小规模电路数值验秩 |
| 猜想 C | B, M4 | 阈值 + a.a.s. | （前沿，先做相图数值证据） |
| 推论 D | M3, A | Sycamore 数字 | 直接代入对账 10^18/10^24 |

---

## 5. 已知风险与反例边界（必须在正文正面处理）

1. **stem 非唯一最优**：一般图上平衡树胜过 stem；定理只能声明"存在最优 stem"，不能声明"最优 ⇒ stem"。multi-stem（SW-TNC）说明复杂几何下单 stem 也不够——正文需限定几何为"足够规则的格点"。
2. **treewidth 只是上界**：decision diagram（arXiv:2510.06775）显式打破 treewidth 壁垒；故下界论证必须经由引理 B 的满秩，不能直接用 `tw`。
3. **相变（M4）**：浅层随机电路可模拟 ⇒ 猜想 C 必须带 `d > d★`。**几何维数是关键缓冲**：M4 是 2D 浅层（准 1D 测量动力学）的结果，本课题靶子是 3D 时空晶格深 bulk（定义 1.1′），相变可模拟相够不到；但 `d★` 的存在性与几何依赖仍须显式论证，不能默认 3D 就自动越过。
4. **"收缩法"下界 ≠ 一切算法下界**：全文下界限定在 TN-收缩算法类（含 slicing，因 slicing 只换时间↔空间、不降总功），不声称无条件经典硬度。

---

## 6. 交付物与后续

- 本 spec（A）：定义 + 分层定理陈述 + 证明骨架。
- 后续候选（择一深入）：
  - **B 优先**：把引理 B 写成完整证明（含满秩赋值的显式构造），这是"可证 + 原创"的最高性价比点。
  - **A 收尾**：把 2D/Sycamore 的 `pw=tw` 常数算死，补全推论 D 的严格代数。
  - **C 探路**：先用数值相图给猜想 C 的 `d★` 证据，再尝试解析阈值。

---

## 附：源文献

- Markov & Shi, *Simulating quantum computation by contracting tensor networks*, [quant-ph/0511069](https://arxiv.org/abs/quant-ph/0511069)
- Huang et al., *Classical Simulation of Quantum Supremacy Circuits*, [arXiv:2005.06787](https://arxiv.org/abs/2005.06787)（"stem" 出处）
- SW-TNC, [arXiv:2504.09186](https://arxiv.org/abs/2504.09186)（multi-stem）
- Boixo et al., *Simulation of low-depth quantum circuits as complex undirected graphical models*, [arXiv:1712.05384](https://arxiv.org/abs/1712.05384)
- Groenland et al., *Tight bounds for pathwidth vs treewidth*, [arXiv:2008.00779](https://arxiv.org/abs/2008.00779)
- Napp, La Placa, Dalzell, Harrow, Brandão, *Efficient classical simulation of random shallow 2D quantum circuits*, [arXiv:2001.00021](https://arxiv.org/abs/2001.00021)
- *Breaking the Treewidth Barrier ... with Decision Diagrams*, [arXiv:2510.06775](https://arxiv.org/abs/2510.06775)
- Pan & Zhang, [arXiv:2103.03074](https://arxiv.org/abs/2103.03074); Pan, Chen & Zhang, [arXiv:2111.03011](https://arxiv.org/abs/2111.03011)（big-head，非 stem）
- Kalachev, Panteleev, Yung, [arXiv:2108.05665](https://arxiv.org/abs/2108.05665)（subtree reuse，非 stem）
