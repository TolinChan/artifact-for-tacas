## 合成模块使用指南（StateMachine/CEGIS）

本指南介绍如何使用本仓库的智能合约合成模块，包括两条合成路线（标准版与V2版本）、输入文件组织、运行命令、输出产物，以及当前已知问题与排错建议。

### 环境与依赖

- 必需：
  - Java 11+，SBT 1.9+（项目使用 Scala 2.13）
  - Z3（含 Java 绑定），参考仓库 `README.md` 的 Z3 安装与 `unmanaged` 依赖配置
- 可选：
  - Truffle（仅用于后续在链上测试 Solidity 合约）

### 目录结构与输入

- 基准合约放在 `synthesis-benchmark/<name>/` 下。以 crowdfunding 为例：
  - `synthesis-benchmark/crowdfunding/crowfunding.dl`：Datalog 功能规范（关系/事务/视图/交易条件）
  - `synthesis-benchmark/crowdfunding/example_traces.txt`：正例轨迹（可选）
  - `synthesis-benchmark/crowdfunding/temporal_properties.txt`：时序/安全性质（支持常见模式，见“性质语法支持”）

说明：`benchmarks/crowFunding.dl` 为原始基准版本；已将其语义拆分同步到 `synthesis-benchmark/crowdfunding/` 以适配当前实现的合成流程。

### 性质语法支持（Parser）

`temporal_properties.txt` 支持的常见模式（忽略最外层的 □）：

- 互斥：`¬(♦A() ∧ ♦B())`
- 单向禁止：`♦A() → ¬♦B()`（左右括号 `♦(A())` 也可）
- 事件条件：`♦Event() → raised(r) ∧ target(t) → r < t`（也支持 `<=, >, >=, ==`）

其它不在上述列表的复杂表达式会被跳过（不报错）。

### 两条合成路线

- 路线一：标准 CEGIS（使用提供的轨迹与性质）
  - 入口：
    ```bash
    sbt "run synthesize crowdfunding"
    ```
  - 流程：解析 Datalog → 构建 `StateMachine` → 候选守卫枚举 → CEGIS → BMC → Solidity 翻译与 require 注入
  - 输出：`test-solidity/crowdfunding.sol`

- 路线二：V2 随机轨迹/候选评分版（探索式）
  - 入口（参数依次为 K、maxPerTr、trainTraces、valTraces、maxTraceLen）：
    ```bash
    sbt "run synthesizeV2 crowdfunding 3 2 40 40 6"
    ```
  - 流程：先估计候选规模后，随机选取候选组合；对每个组合随机生成训练/验证轨迹，执行 CEGIS 与 BMC 评分，挑选得分最佳的组合，再输出合约

### 输出与注入规则

- 守卫合取生成后会导出到 Solidity 的 `require(...)`：
  - 多条同名交易（如 `refund_2`, `refund_11`）按 base 名（`refund`）聚合为多条条件的 OR
  - 导出时会过滤恒真/恒假（`true/false`）的条件，避免注入 `require(true)` 或 `require(false)`；若全部为恒真/恒假，则不注入 require，由内部规则函数的 `revert("Rule condition failed")` 兜底
- Z3→Solidity 条件转换支持：`and/or/not`、位宽整数比较（`<, <=, >, >=, =`）、`bvadd/bvsub/bvmul`、数组 `select`、十六进制位向量常量转十进制等

### 常用命令速查

- 单合约合成（路线一）：
  ```bash
  sbt "run synthesize crowdfunding"
  ```
- V2 合成（路线二）：
  ```bash
  sbt "run synthesizeV2 crowdfunding 3 2 40 40 6"
  ```
- 仅测试 BMC（内置小实验）：
  ```bash
  sbt "run testbmc2"
  ```

### 已知问题与现状

- 问题一：部分转移的守卫在合取后化简为恒真或恒假
  - 现象：日志中可能出现 `refund_x: false` 或 `true`
  - 原因：候选生成会成对加入布尔字面量 `b` 与 `not b`，在 CEGIS 选择过程中可能导致 AND 合取矛盾/平凡
  - 处理：为保持与 Python 版本核心一致性，不在求解端增加“互斥约束”；在导出层过滤恒真/恒假，避免注入无意义的 `require`

- 问题二：V2 路线易出现“Negative trace has NO FALSE candidates – cannot be blocked”
  - 现象：大量负例轨迹提示候选在该反例处全部评估为 `true`，无法用于阻断，导致难以收敛
  - 可能原因：候选池对当前语义过弱，或轨迹生成参数使得训练信号稀疏
  - 建议：
    - 适度放宽候选枚举（允许更多索引/谓词）或提高 `maxPerTr`
    - 调整 V2 参数：缩短 `maxTraceLen`、增大 `train/valid` 提升学习信号密度；改变 `seed`
    - 针对关键交易（如 `refund/withdraw`）添加与 `closed/raised/target` 相关的“种子谓词”以增强可阻断性（需要定制候选生成）

- 问题三：性质解析能力有限
  - 仅支持本文“性质语法支持”列出的模式；更复杂的 LTL/CTL 未解析（会被忽略）

- 问题四：导出 require 时的取舍
  - 当聚合后仅剩恒真/恒假时，为避免生成 `require(true/false)`，当前策略是不注入入口 require；逻辑约束通过内部更新函数的判定与 `revert(...)` 保证

### 验证与示例

- Crowdfunding（当前仓库默认样例）
  - 输入：`synthesis-benchmark/crowdfunding/crowfunding.dl` 与 `temporal_properties.txt`
  - 路线一运行示例：
    ```bash
    sbt "run synthesize crowdfunding"
    ```
  - 产物：`test-solidity/crowdfunding.sol`
  - 典型日志：CEGIS 两轮内收敛，BMC 通过；函数入口 `require(...)` 仅在存在非平凡守卫时注入

### 排错建议（Checklist）

- Z3 环境：确认 Java 绑定与动态库路径按 `README.md` 配置
- 语法：`temporal_properties.txt` 是否满足受支持的模式；事件名需与交易基名对应（如 `refund`、`withdraw`）
- Datalog 语义：`recv_*` 与内部交易关系映射是否匹配（如 `recv_withdraw` → `withdraw(...)`）
- 候选不足：若频繁出现“NO FALSE candidates”，优先调整 V2 参数或增强候选生成逻辑

### 设计一致性说明

- Scala `StateMachine` 与 Python 版本在“核心逻辑”（候选生成、simulate/transfer、CEGIS、BMC）保持一致；本次改动仅在导出层：
  - 强化 Z3→Solidity 的字符串转换以避免误判为 `true`
  - 导出时过滤恒真/恒假，避免注入无意义的 `require`

---

如需对其它基准（如 `erc20`、`voting`）进行同样的拆分与测试，可参考 crowdfunding 的目录组织与命令。若希望我为某个基准建立对应的 `synthesis-benchmark/<name>/` 输入三件套，请告知名称即可。


