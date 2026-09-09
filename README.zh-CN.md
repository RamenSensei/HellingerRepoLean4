# HellingerRepoLean4

本仓库提供 Boolean 噪声、Hellinger 界、bent 函数、二次相位和谱不等式的 Lean 4 证明，共 87 个证明模块。一般情形的 Hellinger 猜想与 Courtade–Kumar 猜想仍未解决；已证明的范围、假设和等号条件以 Lean 定理类型为准。

## 构建与验证

安装 Git、elan 和 Python 3.10 或以上版本后运行：

```sh
git clone https://github.com/RamenSensei/HellingerRepoLean4.git
cd HellingerRepoLean4
lake exe cache get
lake build
python3 checks/verify.py
```

Lean 固定为 `v4.33.1`，mathlib 固定为 `0df444a360eaa60ab8c11dca51a86af692955474`，传递依赖由 `lake-manifest.json` 锁定。首次下载需要网络和足够的磁盘空间。

验证包含文件白名单、模块导入完整性、依赖版本、逐模块编译、公理审计和独立内核重放，并用负对照确认错误证明及违规机制会被拒绝。公理白名单为 `propext`、`Classical.choice` 和 `Quot.sound`。运行结果写入被 Git 忽略的 `checks/results/`。

## 代码入口

- [Lean 库入口](Hellinger.lean)：导入全部证明模块。
- [完整函数接口](Hellinger/FunctionContracts.lean)：平移、bent、二次相位和奇函数结论。
- [谱接口](Hellinger/SpectralContracts.lean)、[概率接口](Hellinger/ProbabilityContracts.lean)和[商空间接口](Hellinger/QuotientContracts.lean)。
- [验证工具](checks)：验证驱动、公理审计、内核重放和接口检查。

仓库仅包含 Lean 源码以及构建、验证、说明和许可所需文件。论文、PDF、LaTeX、研究笔记、发布包和生成日志不纳入 Git；`checks/source_only.py` 在本地验证和 CI 中执行明确的文件白名单检查。

内核验证针对 Lean 中的形式化陈述，不证明其与外部文字文档之间的对应关系。提交修改前请运行完整验证，并说明定理类型变动的数学原因。

原始代码和说明采用 [MIT 许可证](LICENSE)，依赖保留各自许可证。
