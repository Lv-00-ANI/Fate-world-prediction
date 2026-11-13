/-!
  ## 迁移探针 000 · 构建链路自检

  不 import 任何迁移代码，只证明「这个仓库能构建」。
  后续每个迁移批次都会先跑一次这个探针，确保失败是**迁移代码**的问题，
  而不是**仓库配置**的问题。
-/
namespace FateWorld.Migrate000

/-- 构建链路自检：Lean 内核可用、工具链版本正确。 -/
theorem build_smoke : (1 : Nat) + 1 = 2 := rfl

end FateWorld.Migrate000