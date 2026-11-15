# 库结构与范围说明

本目录是论文《恰当拟合边界：一个机器检验的刻画及其可满足性》的 Lean 4 实现。

## 快速开始

```powershell
cd lib
lake exe cache get          # 首次：拉取 Mathlib 预编译产物（否则要编数小时）
lake build ProperFit        # 论文入口：覆盖论文正文引用的全部定理
```

工具链见 `lean-toolchain`（`leanprover/lean4:v4.33.0-rc1`）。
Mathlib 版本由 `lakefile.toml` 中的 `rev` 锁定。

## 两个 lakefile

| 文件 | 依赖方式 | 用途 |
|---|---|---|
| **`lakefile.toml`** | 从 GitHub 拉取 Mathlib（`rev` 固定） | **默认 / 交付用**。任何有网络与 elan 的机器都能构建 |
| `lakefile.local.toml` | 本地路径 `D:/mathlib/packages/...` | 本机离线联调用（不触网） |

本机离线构建时：

```powershell
Copy-Item lakefile.local.toml lakefile.toml -Force
```

> `lake-manifest.local.json` 是本地 path 配置对应的 lock 文件，随之保留。

## 两个入口

| 入口 | 覆盖范围 | 用途 |
|---|---|---|
| `ProperFit.lean` | 23 个直接导入、闭包 **44 个模块**、**695 条定理** | **论文入口**。论文引用的一切都在这里 |
| `ProperFit/All.lean` | **142 个模块**、**2388 条定理** | 全量库入口 |

> **论文读者只需 `lake build ProperFit`。**

## 目录结构

```
lib/
  lakefile.toml          依赖声明（Mathlib + 8 个基础包）
  lean-toolchain         leanprover/lean4:v4.33.0-rc1
  ProperFit.lean         ← 论文入口
  ProperFit/             实现模块
    FitBoundary.lean               第 3–5、8.1 节
    OptimalFit.lean                第 3.3、10 节（参数无关判据）
    FitBoundaryLowerBound.lean     第 7 节
    Decomposition.lean             第 5.3 节
    CoreBasics.lean                第 6 节
    ScoreK.lean                    第 8.2 节
    ErrorBound.lean                第 8.3 节
    ErrorCriterion*.lean           第 8.2、8.4 节
    GridGeometry.lean              第 9.1 节
    FormalContext.lean             第 9.2 节
    Dimensions.lean                第 12.1 节
    SigmaFeasible.lean             第 10.1 节
    SigmaDataDependence.lean       第 10.2 节
    InfoCompleteness.lean          第 5.6 节
    SupportBound.lean              第 11 节
    MainLoopSupportBridge.lean     第 11 节
    All.lean                       全量入口
```

## 关于 `ProperFit/` 中的其余模块

`ProperFit/` 共 142 个模块，其中约 98 个**不属于论文内容**——它们来自另一条独立的理论
工作（因果推断、世界模型、规则系统、形式概念分析主线等）。这些模块：

- **不在** `ProperFit.lean` 的闭包内（即不影响论文）；
- 只在 `ProperFit/All.lean` 中被导入；
- 其注释使用另一套术语，与本文的术语不同。

**论文的全部内容由 `ProperFit.lean` 的 43 模块闭包承担。**

## 验收

```powershell
lake build ProperFit         # 论文入口
lake build ProperFit.All     # 全量库
```

- 代码位置**零 `sorry` / `admit` / 自定义 `axiom`**；
- 抽样定理经 `#print axioms` 核验，公理依赖均为 `[propext, Classical.choice, Quot.sound]`。

> **已知环境限制**：`lake build ProperFit.All` 在资源紧张时可能偶发
> `failed to read … .olean`（每个模块单独构建均正常）。绕法：先单独构建报错模块预热，
> 或使用 `_tools/build_sequential.ps1` 顺序构建。

## 论文与定理的对照

论文附录 B 给出「论文条目 → 定理名 → 模块」的对照表。**只引用定理名，不引用行号**——
行号会随任何一次重组失效，定理名不会。

核验工具：`_tools/verify_paper_claims.py`（检查论文引用的每个定理名是否真实存在）。
