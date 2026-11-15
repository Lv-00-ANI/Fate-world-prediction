# 发现：G4 的假 PASS 通道（已被 G4-b 堵住）

> **日期**：2026-11-03
> **发现**：专项 T42（环境复测）
> **性质**：**门禁漏洞**——一个从未被真正检查的文件，可以长期伪装成"全部零公理"

---

## 一、漏洞机制

`_audit_axioms.py`（G4）的工作方式：

1. **按文件系统遍历** `FateV2/Core/*.lean`（不是按 import 图）
2. 用 `_declscan` 提取所有定理名
3. 生成 `_audit_core.lean`：`import FateV2.GroupD` + 一堆 `#print axioms <name>`
4. 解析输出，找 `depends on axioms`

**问题在第 1 步与第 3 步的错配**：

- 扫描器看的是**磁盘上有什么**
- `#print axioms` 看的是 **`GroupD` 的 import 闭包里有什么**

**⟹ 若某文件在磁盘上存在但不在 import 链里**（新建未接入、编译失败无 `.olean`），
它所有的定理名都会 `unknownIdentifier`。

**而原代码把 `unknownIdentifier` 明确过滤掉**：

```python
hard = [l for l in out.splitlines()
        if re.search(r'(^|:\s*)error(\(|:)', l)
        and 'unknownIdentifier' not in l        # ← 这里
        and 'Unknown constant' not in l
        ...]
```

**⟹ `unknownIdentifier` 不算错误 ⟹ 整批消失被静默跳过 ⟹ `[PASS]`**

---

## 二、活证据

`T42` 实测时，`Core/ClosureStableFinal.lean` 有 24 条声明：

- 扫描器扫到 24 条 ✅
- `GroupD` 解析不到 24 条（文件不在 import 链，编译失败）
- **G4 报 `[PASS] 全部定理不依赖任何公理`** ❌

即：**那 24 条从未被检查过，但门禁说它们零公理。**

---

## 三、修复：G4-b

新增一道判定（在 `_audit_axioms.py` 里，与 G4 同脚本）：

> **逐文件检查**：若某个文件的**所有完整名**都落在 `unknownIdentifier` 里
> ⟹ 该文件**从未被真正检查** ⟹ **FAIL**

**关键设计细节**（第一版写错过）：
- 扫描器对带 namespace 的定理会给出**两个候选**（`FateV2.Core.Term.fold_lit` 与 `Term.fold_lit`）
- **只能按完整名判定**。用 `endswith` 之类的模糊匹配会把 `Rec.lean` 误报为"整批失败"
- `Rec.lean` 的短名 `Term.fold_lit` 在 GroupD 上下文里解析不到是**正常的**，
  但完整名 `FateV2.Core.Term.fold_lit` 解析得到 ⟹ 它确实被检查了

---

## 四、教训

> **门禁「扫描磁盘」而「检查 import 图」时，二者之间的差集就是盲区。**

这与本项目此前发现的另一类问题同源：

| 门禁 | 扫描对象 | 检查对象 | 盲区 |
|---|---|---|---|
| G5（账实相符） | 账本 CSV | 磁盘上的定理 | 磁盘上有但没登记的 |
| **G4（零公理）** | **磁盘上的定理** | **import 图里的定理** | **磁盘上有但 import 图里没有的** ← 本次 |

**通则：任何"从 A 取事实、在 B 上验证"的门禁，都必须显式检查 `A \ B`。**

---

## 五、当前状态

修复后，`G4-b` 在正常树上 PASS，在 `ClosureStableFinal.lean` 未完成时 FAIL——
**这正是它应有的行为**。
