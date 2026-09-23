# Summary of changes for run 24d6cf7e-2d46-4d4b-9ebd-9e7e2e7e8180
I worked through the priority list in order: the build blocker first, then the outstanding proof debt, then the methodology question, and finally a foundational layer of the extremal-function programme.

**T0 — the build (top priority, now solved).** `lake build` failed immediately with `dependency 'Zeta23' not in manifest`, and the dependency tree was additionally inconsistent with the project's own pins, so nothing at all was being compiled. I restored the path entry for the vendored `Zeta23` library in `lake-manifest.json`, re-resolved Mathlib against the revision pinned in `lakefile.toml` (`db584cd…`, Lean `v4.33.0`) and fetched the matching prebuilt artefacts. `lake build` now completes with **9221 targets and no errors**, including all of `vendor/zeta23`. `docs/build-environment.md` records the two failure modes, their symptoms (including the misleading "Mathlib itself won't compile" errors that a toolchain/pin mismatch produces) and the exact recovery commands, so this does not have to be rediscovered. There is no `sorry` anywhere under `RiemannHypothesis/`; the three in `Challenge.lean` are the challenge statement file by design and are discharged in `Solution.lean`.

**T2 — the free bound, proved.** New module `RiemannHypothesis/HilbertFreeBound.lean`. For `δ`-separated real frequencies and arbitrary complex coefficients, `‖∑_{r≠s} x_r conj(x_s)/(λ_r−λ_s)‖ ≤ 2 H_n δ⁻¹ ∑‖x_r‖²` (`hilbert_free_bound`), and with the harmonic number estimated, `≤ 2(1+log n) δ⁻¹ ∑‖x_r‖²` (`hilbert_free_bound_log`). The argument is the elementary one: a `δ`-separated set in an interval of length `d−c` has at most `(d−c)/δ+1` points, so the `j`-th nearest frequency on either side of a given one is at distance at least `jδ`, whence the row bound `∑_{s≠r} 1/|λ_r−λ_s| ≤ 2H_{#S}/δ` (`sum_inv_dist_le`); the bilinear form follows by `|x_r x_s| ≤ (|x_r|²+|x_s|²)/2` and symmetry. Sorry-free; `#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound`. `HilbertInequality.lean` now cross-references it, so the residual content of the unproved `GeneralizedHilbertInequality` is exactly the removal of the logarithm.

**T6 — the methodology report (`docs/zeta23-methodology.md`).** Reading the vendored sources, the `2/3` is a Gram-matrix second-moment argument with an inertia certificate, not a mollifier argument. The report traces the whole chain: the Gram matrix `A = Σ_ρ m_ρ v_ρ v_ρᵀ` built from a sampled taper; the zero side, where the reflection symmetry `ρ ↦ 1−ρ̄` makes each off-line conjugate pair a hyperbolic block that can raise the positive index by at most one while costing two zeros (`posIndex_blockQ_le`), which is the load-bearing step and the reason no Riemann hypothesis is assumed; the rank–trace inequality at `c = 2` giving `s₁+s₂ ≥ 4 tr Â − 2N − ‖Â‖_F²`; and the prime side, where the explicit formula yields `tr G̃ ≈ L·N` and `(tr G̃)²/tr G̃² ≈ F(λ₁)N` with `F(x) = x/(1+x²/3)`. Substituting gives the shape `2 − 1/c`, which is exactly `Hfun λ = 2 − 1/λ − λ/3 = 2 − 1/F(λ)`; `F(1) = 3/4` and hence `2/3` at `λ → 1⁻`, and `c₁* = 0.75329…` (the optimal taper) gives `2 − 1/c₁* = 0.67250…`. The report also explains `EF.EF_lit` and the layered discharge of the four literature inputs, gives a table of every constant (`1/2`, `3/4`, `5/6`, `(3−1/c₁*)/2`) and its source, and records the audit I ran: no `sorry`, no `axiom`, no `native_decide` in the vendored library, statements unfolded with `#print` to Mathlib's `riemannZeta`/`analyticOrderAt` (numerator counts distinct on-line zeros, denominator counts with multiplicity — the harder normalisation), and `#print axioms` reporting only the three standard axioms. It also states plainly that the constant exceeds the published unconditional records and which single step a sceptical reader should examine. A final section answers T7 as far as it can be answered without new theorems: the repository cannot currently rederive `2/3`, and the obstructions are named precisely — first among them the Montgomery–Vaughan inequality, where the now-proved free bound loses a factor `log T` in the intended regime (`δ ≍ 1/log T`, `n ≍ T log T`).

**T1 — foundational layer.** New module `RiemannHypothesis/ExponentialType.lean` supplies the predicate the rest of the Beurling–Selberg programme is phrased in, `HasExponentialTypeAtMost f τ`, together with its closure API, all proved: monotonicity in `τ`, sums, differences, finite sums, products (types add), scalar multiples, rescaling `z ↦ f(cz)` (type `|c|τ`), and the base cases — constants and polynomials have type `0`, `exp(az)` has type `‖a‖`, and `sin(cz)`, `cos(cz)` have type `|c|` (so `sin(πz)` has type `π`, the bandwidth-one normalisation). The remaining Beurling–Selberg items (Paley–Wiener, Beurling's `B`, the Selberg and Vaaler functions) are not done; neither are T3, T4, T5 or the research items T8–T11, and nothing about them has been claimed or marked as complete.

# Summary of changes for run 3d038154-6036-4899-8a96-ff0246c8c555
I picked the Riemann-hypothesis formalization up where it stood, restored its build, and added one new fully machine-checked module together with all of the repository's own bookkeeping.

**1. The project did not build as delivered.** Its dependency manifest was inconsistent with the pins in `lakefile.toml` and `lean-toolchain` (which I left untouched): `lake build` failed immediately with `dependency 'Zeta23' not in manifest`, and the resolved Mathlib revision did not match the pinned one either. I re-resolved the dependencies against the project's own pins and committed the regenerated `lake-manifest.json`. `lake build` now completes successfully (9218 targets, no errors).

**2. New module `RiemannHypothesis/VanDerCorputSequence.lean` — an explicit sequence of low discrepancy.** Every discrepancy bound in the repository so far was for sequences whose discrepancy is only known to decay slowly (the Erdős–Turán route in `RiemannHypothesis/Discrepancy.lean` gives `N^(−1/9)` for badly approximable `α`), and nothing exhibited a sequence attaining the logarithmic rate that the repository's Koksma inequalities are designed to be used with. This module supplies one. `vdc` is the base-two radical inverse, defined by `vdc n = (n % 2 + vdc (n / 2))/2`; its first values `0, 1/2, 1/4, 3/4, 1/8, 5/8, 3/8, 7/8` are proved, so the definition is the classical one. The proof is combinatorial: the first `j` binary digits of `vdc n` are the lowest `j` digits of `n` reversed (`vdc_split`), so `vdc n` lies in the dyadic cell of length `2^(−j)` indexed by that reversal, and on **any** `2^j` consecutive indices the cell index is a bijection onto `{0, …, 2^j − 1}` (`image_revBits_block`) — exactly one point in each cell. Hence the counting error over such a block is at most `1`, and cutting an arbitrary block of `N` consecutive indices along the binary digits of `N` gives `|#{n ∈ [a, a+N) : vdc n < x} − N x| ≤ log₂ N + 1` for every offset and every `x ∈ [0,1]`. Consequences proved: `discrepancy_vdc_le` (`D_N(vdc) ≤ 2 (log₂ N + 1)/N` for `N ≥ 1`), its counting and star forms (the latter with the constant `1`), `tendsto_discrepancy_vdc` (`D_N(vdc) → 0`), and the quadrature bounds `|(1/N)∑_{n<N} f(vdc n) − ∫₀¹ f| ≤ L·2(log₂ N + 1)/N` for `L`-Lipschitz `f`, the corresponding bound for integrands of bounded variation, and the limit statement.

**3. A lower bound, so the rate is pinned from both sides.** `one_div_two_mul_le_discrepancy` proves, for *every* sequence and every `N ≥ 1`, that `D_N ≥ 1/(2N)`: among the `2N` cells of length `1/(2N)` the first `N` points must miss one (pigeonhole), and that cell witnesses the deviation. Together with the upper bound this gives `1/(2N) ≤ D_N(vdc) ≤ 2 (log₂ N + 1)/N`, so the rate proved is optimal up to the logarithm.

**Honest statement of what is not done.** The constant `2` is not optimal (it comes from writing `[a,b)` as a difference of two initial segments; the star form carries `1`). The sharp optimality statement — Schmidt's theorem, that `N·D_N` is unbounded for every sequence — is not formalized, only the trivial `1/(2N)`. Only base two is treated: no general radical inverse, no Halton or Hammersley point sets, no multidimensional discrepancy. The Riemann hypothesis itself remains an open problem; everything added this round is unconditional analysis around it and says nothing about its truth.

**Bookkeeping and verification** (following the repository's existing conventions): a new task-board row `M1-VDC-SEQUENCE` (`DONE_WEAK`, with the boundary above written out), an evidence file with an adversarial-revalidation section, seven statements pinned verbatim in `scripts/revalidation.lean`, new import and `#print axioms` checks in `scripts/audit.sh`, a README module-table row, the module added to the root import, and `docs/current-goal-state.md` regenerated. Results: `lake build` succeeds; `bash scripts/audit.sh` prints `OK` (2539 theorems axiom-audited, none outside the standard three; 170 task rows validate; all pinned statements elaborate); the new module contains no `sorry` (the only ones in the repository remain the three in `Challenge.lean`, which is the statement-of-record file and is allowed them by the repository's own rules), and the new theorems depend on exactly `propext`, `Classical.choice`, `Quot.sound`. All work is committed and pushed.

# Summary of changes for run 7cf3dcec-b038-4fd5-a8e1-e96aae57cab0
继续完成了这一轮工作：先修好交付状态下无法编译的依赖，再在任务板上关闭了两个明确记录的缺口，全部机器验证通过。

**1. 恢复构建。** 交付时 `lake-manifest.json` 与仓库自己的 pin（`lakefile.toml`、`lean-toolchain`，二者均未改动）不一致，`lake build` 直接以 `dependency 'Zeta23' not in manifest` 失败。我按仓库自身的 pin 重新解析依赖并提交了新的 manifest；现在 `lake build` 成功（9213 个目标，零错误）。

**2. 新模块 `RiemannHypothesis/KoksmaVariation.lean` —— 用总变差表述的 Koksma 不等式。** 此前仓库只有单调被积函数、或写成两个单调函数之差的版本，常数依赖于所选分解；任务板把「没有总变差泛函」记为未决边界。本模块用 Mathlib 的 `eVariationOn` 定义 `unitVariation f = V(f)`，并证明：对 `[0,1]` 上任意有界变差（不假设连续）的 `f`、任意序列 `x`、任意 `N ≥ 1`，
`|(1/N)∑_{n<N} f({xₙ}) − ∫₀¹ f| ≤ (2V(f) − |f 1 − f 0|)·D_N(x)`，特别地 `≤ 2V(f)·D_N(x)`；
证明是把两个 Jordan 分解 `f = V_f − (V_f − f)` 与 `f = (V_f + f) − V_f` 分别代入已有的差分形式。附带：单调时 `V(f) = f 1 − f 0`（新常数恰好退化为旧常数）、Lipschitz 常数由 `3L` 改进为 `2L`、以及「判别序列的差异度趋于 0 ⇒ 正确积分每个有界变差函数」的极限形式（含 `α n²`、`α` 无理的具体实例）。

**3. 新模块 `RiemannHypothesis/KoksmaSharp.lean` —— Lipschitz 情形的最优常数。** 完全绕开单调分解：把分部求和步骤推广到任意权重序列（`abs_sum_weight_cellDev_le`，以权重沿格点的变差代替单调升幅），再证明两个离散化误差（平均值 vs 格点阶梯平均、积分 vs 黎曼和）各不超过 `L/K`，于是误差 `≤ L·D_N(x) + 2L/K` 对每个 `K ≥ 1` 成立，从而
`|(1/N)∑_{n<N} f({xₙ}) − ∫₀¹ f| ≤ L·D_N(x)`（`koksma_lipschitz_sharp`），这是经典的最优常数，取代了先前的 `3L` 与 `2L`。同时给出其极限形式。

**如实说明尚未做到的部分。** 一般有界变差情形的最优常数仍是 `V(f)` 而非 `2V(f)`：那需要对 `d f` 的 Riemann–Stieltjes 分部积分，Mathlib 与本仓库都没有这套机制；任务板对应行如实标为未决。黎曼猜想本身仍是公开未解决问题，本轮新增内容都是围绕它的无条件分析结果，与其真假无关。

**记账与验证**（沿用仓库既有规范）：新增任务板行 `M1-KOKSMA-VARIATION`（DONE_WEAK，边界写明常数非最优）与 `M1-KOKSMA-LIPSCHITZ-SHARP`（DONE_STRONG，边界为空），并相应更新了 `M1-KOKSMA` 的未决边界；两个 evidence 文件（含对抗性复核小节）；`scripts/revalidation.lean` 中逐条完整钉住语句；`scripts/audit.sh` 增加导入与 `#print axioms` 检查；README 模块表新增两行；重新生成 `docs/current-goal-state.md`。验证结果：`lake build` 成功；`bash scripts/audit.sh` 输出 `OK`（2442 条定理公理审计通过、0 条越界；165 条任务校验通过）；新模块无 `sorry`（全仓库仅剩 `Challenge.lean` 中按约定保留的三个），新定理公理恰为 `propext`、`Classical.choice`、`Quot.sound`。所有改动已提交并推送。

# Summary of changes for run fa0c2a1f-da61-4fe1-a61d-040dc236b397
I picked the Riemann-hypothesis formalization up where it stood and made two kinds of progress: I restored the build, and I added a new, fully machine-checked module.

**1. The project did not build as delivered.** Its dependency manifest did not match the Mathlib revision pinned in `lakefile.toml`, so `lake build` failed immediately (`dependency 'Zeta23' not in manifest`, plus a Mathlib revision mismatch). I re-resolved the dependencies against the project's own pins — `lean-toolchain` and `lakefile.toml` untouched — and committed the regenerated `lake-manifest.json`. `lake build` now completes successfully (9211 targets, no errors) and `scripts/audit.sh` reports `OK`.

**2. New module `RiemannHypothesis/Koksma.lean` — Koksma's inequality.** The repository already had the discrepancy `D_N(x)` and Weyl's criterion in discrepancy form, but nothing connecting the discrepancy to what it is for: the error of numerical integration along the sequence. This module proves, quantitatively and with no limit taken:

* `koksma_monotone` — for a nondecreasing `f` on `[0,1]`, every sequence `x` and every `N ≥ 1`,
  `|(1/N) ∑_{n<N} f({xₙ}) − ∫₀¹ f| ≤ (f 1 − f 0) · D_N(x)`. No continuity is assumed: the integrand may have jumps.
* `koksma_sub_monotone` — the bounded-variation form, for an integrand written as a difference `f = g − h` of two nondecreasing functions, with the sum of the two rises.
* `koksma_lipschitz` — the Lipschitz form, with constant `3 L` (not the sharp `L`).
* `tendsto_average_of_tendsto_discrepancy` and `tendsto_average_quadratic` — the limiting consequences, the second for `α n²` with `α` irrational.

The proof cuts `[0,1)` into `K` cells: monotonicity brackets the average between the two step averages built from the cell endpoints and brackets the integral between the corresponding Riemann sums, which differ by `(f 1 − f 0)/K`; the remaining cell-deviation sums are handled by summation by parts, which turns them into consecutive differences of `f` weighted by the deviations of the tail intervals `[j/K, 1)`, each bounded by `D_N`. The boundary terms vanish because the full interval and the empty interval have deviation `0`.

**Verification and bookkeeping.** The module is `sorry`-free; the axioms of all four headline theorems are exactly `propext`, `Classical.choice`, `Quot.sound`. The module is imported by the root `RiemannHypothesis.lean`, its theorems are added to the axiom checks in `scripts/audit.sh` and pinned statement-by-statement in `scripts/revalidation.lean`, and a task-board row `M1-KOKSMA` with an evidence file under `docs/goal/evidence/` records what is proved and what remains open (no total-variation functional; the Lipschitz constant is not sharp). `README.md` and `docs/current-goal-state.md` are updated. The only `sorry`s left in the repository are the three in `Challenge.lean`, which the repository's own convention requires to be unproved there and proved in `Solution.lean`.

As before, and stated plainly: the Riemann hypothesis itself is open and is not proved here; everything added is unconditional analysis around it. All work is committed and pushed.

# Summary of changes for run 51974088-7ebe-4277-b7d7-5569abdd3146
I picked up the Riemann-hypothesis formalization project and made three kinds of progress: I restored the build, and I closed two recorded gaps plus added a capstone equivalence, all machine-checked.

**1. The project would not build as delivered.** Its dependency manifest did not match the vendored `Zeta23` path dependency and the pinned Mathlib revision, so `lake build` failed immediately with `dependency 'Zeta23' not in manifest`. I re-resolved the dependencies against the project's own pins (`lean-toolchain` and `lakefile.toml` untouched) and committed the regenerated manifest. `lake build` now succeeds (9203 targets, zero errors) and `scripts/audit.sh` reports `OK`.

**2. `RiemannHypothesis/WeylDiscrepancyGeneral.lean` — the Erdős–Turán bound for every subinterval.** The existing discrepancy inequality only covered intervals `[a,b) ⊆ [0,1]` satisfying `1/K < a`, `b + 1/K < 1` and `a + 2/K ≤ b`, which the task board recorded as an open boundary; short intervals and intervals touching `0` or `1` — exactly the ones a discrepancy supremum is attained on — were excluded. I proved the inequality for **every** `0 ≤ a ≤ b ≤ 1`, with the constant `20/K` in place of `4/K`, using a rotation (translation multiplies each exponential sum by a unimodular factor), an enlargement of short intervals, and the complement identity `#[0,a) + #[a,b) + #[b,1) = N`. The rates for `α n` and for `α n²` with `2α` badly approximable are carried over to all intervals.

**3. `RiemannHypothesis/Discrepancy.lean` — the discrepancy itself, and a power saving.** Defines `D_N(x)` as the supremum of the interval deviations (nonempty, bounded by 1), with the interface lemmas, a non-vacuity check (the constant sequence `0` has `D_N ≥ 1/2`), the Erdős–Turán bound in discrepancy form, and the power saving `D_N(α n) ≤ 2(20 + 2/c)·N^(−1/9)` for badly approximable `α` and `N ≥ 8⁹` — obtained with `K = ⌊N^(1/9)⌋` — hence `D_N(α n) → 0`.

**4. `RiemannHypothesis/DiscrepancyCriterion.lean` — Weyl's criterion in discrepancy form.** A sequence is equidistributed modulo one exactly when `D_N → 0`. The forward direction is not a repackaging of the pointwise limits (a supremum of infinitely many null sequences need not be null): it chooses `K` with `20/K < ε/2` first and only then passes to the limit in the remaining finitely many exponential sums. Corollaries: `D_N(α n²) → 0` for every irrational `α`, and the constant sequence `0` shows the criterion separates sequences.

All new code is free of `sorry` (the only `sorry`s in the repository remain the three deliberate ones in `Challenge.lean`, which `Solution.lean` discharges), and every new theorem's axioms are exactly `propext`, `Classical.choice`, `Quot.sound`. I followed the repository's own conventions throughout: new task-board rows (`M1-WEYL-DISCREPANCY-GENERAL`, `M1-DISCREPANCY`, `M1-DISCREPANCY-CRITERION`, all `DONE_STRONG` with empty open boundaries), evidence files with adversarial-revalidation sections, fully expanded statement pins in `scripts/revalidation.lean`, `#print axioms` entries in `scripts/audit.sh`, README module rows, a regenerated `docs/goal/conditional-theorems.txt` (one new DEFINITIONAL line), and a regenerated `docs/current-goal-state.md`. The board now validates 159 tasks and the full audit reports `OK`.

The Riemann hypothesis itself remains open and unproved here, as the repository states; the rows recording that (including `M4-RH`) are unchanged. Everything is committed and pushed.

# Summary of changes for run 47ed40fe-827d-46e5-a22a-7358eddec39d
## 简短回答：**没有全部完成**——而且我发现交付状态下项目根本编译不起来，已经修好。

### 现在的真实状态（都是我这次亲自跑出来的，不是转述）

**任务板（`docs/goal/task-board.yaml`）共 154 行：`DONE_STRONG` 95 条，`DONE_WEAK` 49 条，`TODO_NEEDS_DESIGN` 10 条。**
- `DONE_WEAK` 是「做了一部分、`open_boundary` 里明确写着还缺什么」的行（例如临界线上的均方渐近、大筛法的最优常数、Weyl 指数的对数因子、Montgomery–Vaughan 形式等）。
- `TODO_NEEDS_DESIGN` 里包括 `M4-RH`（黎曼猜想本身）、Selberg 中心极限定理、对关联、Vinogradov、零点间隙、3×10¹² 高度的数值验证等。**黎曼猜想仍是未解决问题，仓库里没有、也不声称有它的证明**；仓库中不存在任何 `ZetaForm` 类型的项。

### 这次做了什么

1. **修好「拿到手就编译不了」的问题（重要）。** `lake-manifest.json` 与仓库自己的 `lakefile.toml` 不一致：manifest 里记的是另一个 Mathlib 版本，并且完全没有 vendor 的 `Zeta23` 路径依赖，Lake 直接报 `dependency 'Zeta23' not in manifest`。我按仓库自己的 pin（`lean-toolchain` v4.33.0、`lakefile.toml` 指定的 Mathlib 版本，二者均未改动）重新解析依赖并提交了新的 manifest。现在 **`lake build` 成功（9201 个目标，零错误）**，`bash scripts/audit.sh` 报 `OK`。
2. **清掉了 vendor 之外的全部编译告警。** 约 130 处 Mathlib 弃用重命名（`Set.mem_setOf_eq → Set.mem_ofPred_eq`、`integral_finset_sum → integral_finsetSum`、`Set.mem_diff → Set.mem_sdiff`、`push_neg → push Not` 等）、两条空操作策略、一个未被使用的假设（顺带把 `sum_sieveWeight_dvd_le` 的语句变得更一般）。现在除 `Challenge.lean` 里按仓库约定故意保留的三个 `sorry` 外，非 vendor 代码零告警、零 `sorry`。
3. **新增一条真正的数学结果并关闭了一个明确记录的缺口：** 新模块 `RiemannHypothesis/WeylPortmanteau.lean`，把 Weyl 判别法补成**计数形式**。此前仓库只有「等分布 ⟹ 每个子区间的计数比例趋于区间长度」；反方向缺失，而这正是判别法通常被使用的形式。现在证明了
   - `weylSumsVanish_of_countsEquidistribute`：只要对每个 `0 ≤ a < b ≤ 1` 有 `#{n<N : {xₙ}∈[a,b)}/N → b−a`，则每个非零频率的指数和都是 `o(N)`；
   - 由此 `equidistributedMod1_iff_countsEquidistribute`、`weylSumsVanish_iff_countsEquidistribute`：三种表述互相等价，判别法不再需要连续检验函数或测度；
   - `countsEquidistribute_quadratic`：对每个无理数 α，`α n²` 的小数部分满足该计数形式。
   证明思路：把 `[0,1)` 分成 `K > |m|` 个等长格子，用相位的 2π-Lipschitz 性把每项换成所在格子左端点的值（总误差 ≤ `N·2π|m|/K`），剩下的是各格计数的加权和，其极限是 `e(m·)` 在 `K` 次单位根上的平均，因 `K ∤ m` 而为 0。
   **无 `sorry`，公理恰为 `propext, Classical.choice, Quot.sound`。** 同时按仓库既有规范补齐了：任务板新行 `M1-WEYL-PORTMANTEAU`（含对抗性复核小节的 evidence 文件）、`scripts/revalidation.lean` 中三条完全展开的语句钉子、`scripts/audit.sh` 的公理检查、条件/无条件边界分类（新的 `CountsEquidistribute` 归入 DEFINITIONAL 并重新生成 `docs/goal/conditional-theorems.txt`）、README 模块表、以及重新渲染的 `docs/current-goal-state.md`。

### 验证
`lake build` 成功；`bash scripts/audit.sh` 输出 `OK`（2057 条定理全部公理审计通过、0 条越界；154 条任务通过校验）；非 vendor 代码中除 `Challenge.lean` 的三个约定 `sorry` 外没有任何 `sorry`。所有改动已提交并推送。

### 还剩什么
上面那 49 条 `DONE_WEAK` 与 10 条 `TODO_NEEDS_DESIGN`，各行的 `open_boundary` 里逐条写明了缺口；其中黎曼猜想本身是公开的未解决问题，仍未证明。


# Summary of changes for run 52bd440b-1337-4cd2-a619-bb3cb85e3d3b
按您给的顺序 4 → 2 → 1 → 3 → 5 全部做完了。完整报告写在 `docs/audit-review-2026-09-06.md`，下面是结论。

**4. 编译（先做，几分钟就暴露了问题）——交付状态下编译不起来，已修好。**
`lake build` 根本没能启动：`lake-manifest.json` 与仓库自己的 pin 不一致（Mathlib 记的是另一个 revision/URL，且完全没提 vendor 的 `Zeta23` path 依赖，Lake 直接报 `dependency 'Zeta23' not in manifest`）。按仓库自己的 pin 重新解析依赖后（`lean-toolchain` v4.33.0、`lakefile.toml` 的 Mathlib v4.33.0 都没动，只改了 manifest）：**`lake build` 成功，9200 个目标，零错误**。三轮合并的十一个新模块全部编译通过，**没有 API 漂移**；只有 Mathlib 的 deprecation 警告（我改到的文件里已顺手改掉）。担心的「来源 pin v4.28.0」没有发生：vendor/zeta23 pin 的就是同一个 v4.33.0 Mathlib。唯一的 `sorry` 警告是 `Challenge.lean` 里设计好的三个。

**2. 公理审计覆盖率 719/2030（35%）——已整类关掉，不是补清单。**
新增 `scripts/axiom_audit.lean`：遍历环境，对本仓库每一个 theorem 收集其证明真正依赖的公理，报出任何超出 `propext, Classical.choice, Quot.sound` 的。当前结果：**2255 条定理全查，0 条越界**；新定理天生被覆盖，不需要往任何清单里加行。已接进 `scripts/audit.sh`（步骤 3b）。做了阳性对照：往叶子模块塞一条 `by sorry` 的定理并重编译，工具报 `NONSTANDARD … : [sorryAx]`，随后撤掉。旧的手写清单保留（它是「被比对的结论」名单），其覆盖率现在被报告出来，并且**清单里若出现库中已不存在的名字就直接判失败**——写工具时就抓到 4 个这样的失效名并修正。

**1. vendor/zeta23 的 2/3 定理：是真结果，不是定义的把戏。**
(a) 公理我自己重跑：`thmA₀ / thmA₀_cumulative / thmB₀ / thmC₀ / thmA₀_N0` 以及本仓库的 `two_thirds_on_critical_line` 都恰是标准三公理；`thmA₀ = thmA₁ zetaEF`，而 `zetaEF` 是定理不是假设，所以 Theorem A 无任何前提。
(b) 语句直接对着 Mathlib 读：`zerosIn` 就是 `riemannZeta ρ = 0 ∧ 0 < re ρ < 1 ∧ T₁ < im ρ ≤ T₂`，`zeroMult` 就是 `analyticOrderAt riemannZeta`；归一化确实是文献的，且左带重数、右数不同点，方向是更强而不是更弱。
(c) 关键补的是「分母非空」：新模块 `RiemannHypothesis/Zeta23Verification.lean` 把比例式变成绝对计数——`windowCount_sub_mainTerm_le`（|N(T,2T) − (T/2π)(log(T/2π)+2log2−1)| ≤ C log T，即 windowCount 就是文献的 N）、`eventually_windowCount_ge`（N(T,2T) ≥ (T/4π)log T）、`eventually_windowCountOnLine_ge`（大 T 时临界线上至少 (T/8π)·log T 个**不同**零点）、`eventually_windowCountSimpleOnLine_ge`（同样多的**单**零点）。常数是故意保守的（丢掉一半主项换显式阈值）。这不代替对解析论证本身的独立复核，那仍要走 vendor 的 comparator。

**3. 条件定理分类：确实是穷尽的，但检测器原来有四个盲区，已补上。**
补的是：Prop 值的 structure/class/inductive 也算 statement；扫描 vendor `Zeta23` 自己的假设；纳入 Mathlib 的 `RiemannHypothesis`（`ZetaForm` 只是它的 abbrev）；以及「是否已被证明」改为按**整个命题连同参数**匹配，而不是只看头常量（否则 `P a` 会被 `P b` 的证明清掉）。**加强后输出与记录的清单逐字节相同**（36 条、三类、无 UNCLASSIFIED），所以原分类是穷尽的。阳性对照证实三项新能力真实有效（旧版对这些探针一律看不见）。

**5. 冲终极问题。** 黎曼猜想仍然是开问题，仓库里没有、也不声称有它的证明。能诚实做到的是把「还差什么」变成定理，并且发现通行的直觉有一处是错的：新模块 `RiemannHypothesis/EventualCountingCriterion.lean` 证明 `zetaStripForm_of_eventually_windowCountOnLine_eq`——只要对**一切充分大的 T** 有 N₀*(0,T) = N_d(0,T)，猜想即成立，**完全不需要对低高度零点另做有限验证**：线外零点总可取正纵坐标（ζ 在 (0,1) 上无实零点，零点集对共轭封闭），于是它被其纵坐标以上的**每一个**窗口遗漏，亏损是永久的。配套给出等价形式（含重数版本，即 2/3 定理的那个分母；以及把猜想呈现为 `(c−ε)N ≤ N₀*` 这族命题在 c = 1 处的端点，而已证的是 c = 2/3）。这是归约不是进展：其前提与猜想同难，`CorpusCeiling` 的 67% 天花板依旧。

**记账（按仓库自己的协议）**：新增两个模块、两个 board 行（M1-TWO-THIRDS-ABSOLUTE、M3-EVENTUAL-COUNTING-CRITERION，都是 DONE_WEAK 并写明边界；归约行按板子规则不得标 DONE_STRONG）、一个 M0-AUDIT-COVERAGE 治理行、证据文件 `docs/goal/evidence/2026-09-06-m1-two-thirds-absolute.md`（含对抗式复核与两个阳性对照）、`scripts/revalidation.lean` 语句钉桩、`audit.sh` 公理行、README 与 `docs/current-goal-state.md` 已更新，`docs/goal/conditional-theorems.txt` 重新生成（新增三条都是「前提就是黎曼猜想」的预期条目）。`bash scripts/audit.sh` 打印 `OK`（153 行任务全部校验通过）。全部已 commit + push。

# Summary of changes for run 290ea71f-4e50-41b2-ae35-0db0a4a59221
Short answer: **no — not everything on the project's own task board is finished, and the Riemann hypothesis itself is of course still open.** Here is the verified state, plus what I did this session.

**1. The project did not build as delivered — fixed.**
`lake build` failed immediately on a fresh checkout: the dependency lock file (`lake-manifest.json`) disagreed with the project's own pins (`lakefile.toml`, `lean-toolchain`) — it recorded a different Mathlib revision, on a different Lean toolchain than the one the project requires, and omitted the vendored `Zeta23` path dependency. I re-resolved the dependencies against the project's own pins; only `lake-manifest.json` changed. The whole library, the vendored `Zeta23`, `Challenge` and `Solution` now build clean.

**2. Verified, not assumed.** With the build restored I ran the project's full audit (`scripts/audit.sh`) end to end: `lake build` succeeds; there is no `sorry` anywhere outside `Challenge.lean` (whose three `sorry`s are by design — it is the statement-of-record file, and `Solution.lean` proves all three theorems from `RiemannHypothesis.Main`); the compared theorems depend on exactly `propext`, `Classical.choice`, `Quot.sound`; the claims of every closed row are pinned and elaborate in `scripts/revalidation.lean`; the conditional/unconditional boundary matches its manifest; the board validates. The audit prints `OK`.

**3. What remains open.** Of the 150 rows on `docs/goal/task-board.yaml`: 93 are `DONE_STRONG`, **47 are `DONE_WEAK`** (each with an explicit written `open_boundary` — e.g. the sharp Hardy–Littlewood mean-square asymptotic, the fourth moment, the density theorems, the mollifier work, the Weyl-sum family), and **10 are `TODO_NEEDS_DESIGN`**. Nothing in the repository proves the Riemann hypothesis, and no claim here should be read as doing so; what is proved is the equivalence of its three standard formulations, plus a body of classical prerequisites and partial results.

**4. New mathematics added this session** (`RiemannHypothesis/SubconvexityLogFree.lean`, `sorry`-free, axioms exactly `propext, Classical.choice, Quot.sound`): the subconvex bound on the closed critical strip, with the logarithm removed. Writing `e(σ) = max((1−σ)/3, 1/2 − 2σ/3)` for the strip's subconvex exponent,
- `norm_riemannZeta_le_subconvexity_logfree` — for every `ε > 0` a constant `C`, uniform in `σ`, with `‖ζ(s)‖ ≤ C|t|^(e(σ)+ε)` for `0 ≤ σ ≤ 1`, `|t| ≥ 3`;
- `norm_riemannZeta_le_subconvexity_logfree_fixed` — at every fixed `σ ∈ (0,1)`, with no logarithm and no `ε`, `‖ζ(σ+it)‖ ≤ C|t|^((1−σ)/2 − min(σ,1−σ)/12)` for all `|t| ≥ 3`, an exponent strictly below the convexity exponent `(1−σ)/2` (the gap `(1−σ)/2 − e(σ)` is `σ/6` on the left half of the strip and `(1−σ)/6` on the right, so half of it pays for the logarithm and half is kept);
- `isBigO_riemannZeta_subconvexity_logfree` — the same in `O`-notation.

This strengthens the existing logarithm-free convexity bound. It is recorded on the board as a new row `M1-SUBCONVEXITY-LOGFREE`, with an adversarial-revalidation note in `docs/goal/evidence/2026-09-05-m1-subconvexity-logfree.md` and statement pins in `scripts/revalidation.lean`; `docs/current-goal-state.md` was regenerated. All work is committed and pushed.

# Summary of changes for run fb66b7d3-74d8-40d8-a4d4-eac95072328d
I picked the project up where it stood, restored a working build, and pushed the analytic side of it forward with new, `sorry`-free mathematics. `lake build` succeeds and `scripts/audit.sh` prints `OK` (no `sorry` outside `Challenge.lean`, every new result depending on exactly `propext, Classical.choice, Quot.sound`, all new claims pinned in `scripts/revalidation.lean`, task board validating). Everything is committed and pushed.

**On the headline question:** the Riemann hypothesis itself is still open — nothing here proves it, and I would not claim otherwise. What I did was close the top-priority open row of the project's own task board (`M1-GROWTH`) and strengthen the growth theory around it.

**1. Build repair.** The delivered dependency lock file did not match the project's own pins (`lakefile.toml`, `lean-toolchain`): it recorded a different Mathlib revision and omitted the vendored `Zeta23` path dependency, so `lake build` refused to start. I re-resolved the dependencies against the project's own pins; only `lake-manifest.json` changed. The whole library, including the vendored `Zeta23`, now builds clean.

**2. Subconvexity in the left half of the critical strip** (new `RiemannHypothesis/SubconvexityLeft.lean`). Before this, nothing better than the convexity bound was proved for `σ ≤ 1/2`.
- `exists_bound_criticalLine_sixth` — `‖ζ(1/2+it)‖ ≤ A|t|^(1/6)(1+log|t|)` at *every* height `|t| ≥ 3` and both signs of `t` (the project's existing bound needed `t ≥ 10⁹`).
- `norm_riemannZeta_le_subconvexity_left` — `‖ζ(σ+it)‖ ≤ C(1+log|t|)|t|^(1/2−2σ/3)` for `0 ≤ σ ≤ 1/2`, `|t| ≥ 3`, by Phragmén–Lindelöf between the functional-equation bound on `re s = 0` and the Weyl exponent `1/6` on the critical line, using the same interpolating apparatus (`u^(−w)/log u`) as the existing convexity files.

**3. The convexity bound with no logarithm and no ε** (new `RiemannHypothesis/ConvexityLogFree.lean`), the first exit criterion of `M1-GROWTH`, previously recorded as still open:
- `norm_riemannZeta_le_convexity_logfree` — for every fixed `σ ∈ (0,1)` there is `C` with `‖ζ(σ+it)‖ ≤ C|t|^((1−σ)/2)` for all `|t| ≥ 3`, and `isBigO_riemannZeta_convexity_logfree` in `O`-notation. The logarithm is removed because each half of the strip now has a subconvex exponent saving a fixed positive power of `|t|` at fixed `σ`, and a fixed positive power swallows `1+log|t|`. The constant must depend on `σ`, and the docstring says so.
- `norm_riemannZeta_le_log_div_of_one_lt_re` — the second exit criterion, `‖ζ(σ+it)‖ ≤ 2log|t|/(σ−1)` for `1 < σ ≤ 2`, `|t| ≥ 3`.

**4. One subconvex bound for the whole closed strip** (new `RiemannHypothesis/SubconvexityClosedStrip.lean`): the `t ≥ 10⁹` threshold and the restriction to positive `t` are removed from the right-hand bound (`norm_riemannZeta_le_subconvexity_right`), and the two halves are merged into `norm_riemannZeta_le_subconvexity_closed_strip`: `‖ζ(s)‖ ≤ C(1+log|t|)|t|^max((1−σ)/3, 1/2−2σ/3)` for `0 ≤ σ ≤ 1`, `|t| ≥ 3` — the exponent is `1/6` on the critical line and below the convexity exponent for every `σ ∈ (0,1]`.

**5. Bookkeeping the project asks for.** The new modules are imported by `RiemannHypothesis.lean`, their axioms are checked by `scripts/audit.sh`, every new claim is pinned (statement written out, repository declaration as proof term) in `scripts/revalidation.lean`, a new evidence file `docs/goal/evidence/2026-09-04-m1-convexity-logfree.md` records the arguments and the adversarial revalidation of each row, `M1-GROWTH` is now `DONE_STRONG` with an empty open boundary, two new rows (`M1-SUBCONVEXITY-LEFT`, `M1-SUBCONVEXITY-CLOSED-STRIP`) are added, and `docs/current-goal-state.md` is regenerated. The list of conditional theorems is unchanged: everything added is unconditional.

What remains out of reach and is stated as such: the Lindelöf exponent, any improvement of the constants, and any consequence for the zeroes — these bounds are pointwise, and no mean value, density estimate or zero-free region follows from them.

# Summary of changes for run 60cfe46b-2689-45d1-9c7d-99455318f983
I picked up the Riemann-hypothesis project, restored a working build, and closed the task board's headline analytic boundary with new, `sorry`-free mathematics. `lake build` succeeds and `./scripts/audit.sh` prints `OK` (no `sorry` outside `Challenge.lean`, every new result depending on exactly `propext, Classical.choice, Quot.sound`, all new claims pinned in `scripts/revalidation.lean`, task board validating). Everything is committed.

**Build repair.** The delivered dependency lock file did not match the project's own pins: it recorded a different Mathlib revision and omitted the vendored `Zeta23` path dependency, so `lake build` refused to start, and with the recorded revision a dozen modules failed to compile. I re-resolved the dependencies against the project's own pins; `lakefile.toml` and `lean-toolchain` are unchanged, only `lake-manifest.json` differs. The whole library, including the vendored `Zeta23`, now builds clean.

**1. Subconvexity on the critical line, with no hypothesis** (new `RiemannHypothesis/SubconvexityUnconditional.lean`). The board's row M1-AFE-SUBCONVEXITY had the classical exponent 1/6 only *conditionally* on the approximate functional equation, which is merely recorded, not proved. That hypothesis is now gone:
- `norm_riemannZeta_criticalLine_le` — unconditionally, `‖ζ(1/2+it)‖ ≤ 200 t^(1/6)(log t + 1)` for `t ≥ 10⁹`.

The approximate functional equation is not needed if the Dirichlet polynomial is taken longer and *every* dyadic block of it is bounded. The Euler–Maclaurin representation at length `⌈t²⌉` has both error terms `O(1)` (`norm_riemannZeta_sub_zetaSum_le`, using a telescoping tail bound `∑_{n≥N}(n+1)^(-3/2) ≤ 2/√N`), and the blocks are covered by three different van der Corput tests: the third-derivative test up to `t^(2/3)` (its range extended from the previous `√t`), the second-derivative test up to `2t`, and Kusmin–Landau beyond `2t`, where the phase derivative `t/2πx` is below `1/4π` and therefore is itself its distance to the nearest integer (`norm_sum_e2pi_logPhase_block_le_all`).

**2. Subconvexity inside the strip** (new `RiemannHypothesis/SubconvexityStrip.lean`). The block estimates are about the phase alone, so they do not depend on the line; only the Abel-summation weight does:
- `norm_riemannZeta_strip_le` — unconditionally, `‖ζ(σ+it)‖ ≤ 400 t^((1−σ)/3)(log t + 1)` for `1/2 ≤ σ ≤ 1`, `t ≥ 10⁹`. For `σ > 1/2` the exponent `(1−σ)/3` beats the convexity exponent `(1−σ)/2` by a fixed power of `t`, which addresses the M1-GROWTH boundary in a stronger (though not logarithm-free) form.

Both results are recorded on the task board as new rows (`M1-SUBCONVEXITY-UNCONDITIONAL`, `M1-SUBCONVEXITY-STRIP`) with evidence and adversarial-revalidation notes under `docs/goal/evidence/`, are pinned in `scripts/revalidation.lean` and `scripts/audit.sh`, and are described in `README.md`; the boundaries of the rows they improve were updated accordingly. What remains open is stated honestly in those rows: the constants and thresholds are explicit but not optimized, the logarithms are not removed, nothing is claimed for `σ ≤ 1/2` off the critical line, no moment, density estimate or zero-free region follows from a pointwise bound, and the B process (Poisson summation with stationary phase) is still not formalized, so exponents beyond `(1/6, 2/3)` and the Lindelöf hypothesis remain out of reach. The Riemann hypothesis itself is of course still open, and the repository continues to state it rather than prove it.

# Summary of changes for run 4b2132e5-8279-4251-bd4d-94aa9dff97ba
I picked up the Riemann-hypothesis project, restored a green build, and closed two of the task board's named open boundaries with new, `sorry`-free mathematics. Everything is committed; `lake build` succeeds (9195 jobs) and `./scripts/audit.sh` prints `OK` (no `sorry` outside `Challenge.lean`, every new result depending on exactly `propext, Classical.choice, Quot.sound`, all new claims pinned in `scripts/revalidation.lean`).

**Build repair.** The delivered dependency lock file did not match the versions the project itself pins: it recorded a different Mathlib revision and omitted the vendored `Zeta23` path dependency, so `lake build` refused to start. I re-resolved the dependencies against the project's own pins; `lakefile.toml` and `lean-toolchain` are unchanged, only `lake-manifest.json` differs.

**1. Kusmin–Landau over a general range** (new `RiemannHypothesis/KusminLandauGeneral.lean`). The board's row M1-KUSMIN-LANDAU said plainly that "splitting a general range into such subranges is not done here": the existing first-derivative test needed `f'` trapped between two consecutive integers. Now proved, with `e(θ) = exp(2πiθ)`:
- `norm_sum_e2pi_le_of_deriv_block` — one block, under the separation hypothesis `λ ≤ |f'(x) − m|` for every integer `m`;
- `norm_sum_e2pi_le_of_deriv_floor` — the general monotone range, with the exact block count: `‖∑_{j ≤ K} e(f(c+j))‖ ≤ (⌊f'(c+K)⌋ − ⌊f'(c)⌋ + 1)(1 + 2/λ)`;
- `norm_sum_e2pi_le_of_deriv_general` — the same in terms of the total variation `V = |f'(c+K) − f'(c)|`, for `f'` monotone *or* antitone: `≤ (V + 2)(1 + 2/λ)`, the classical shape of the test.
The proof is strong induction on the length of the range: on the maximal initial block where `⌊f'⌋` is constant the old bound applies uniformly in its length, and past it `⌊f'⌋` has grown by at least one; the antitone case follows by conjugation.

**2. Brun–Titchmarsh with the constant `2π + ε`** (new `RiemannHypothesis/BrunTitchmarshSharp.lean`, plus a generalization inside `RiemannHypothesis/BrunTitchmarshProgressions.lean`). The row M2-BRUN-TITCHMARSH named its own remedy — "with the factor π kept and Q optimized it would give 2π + o(1)" — and that is now carried out:
- `card_primes_Ico_le_of_level` — the sieve at an arbitrary level `Q ≥ 2`: at most `(Q² + π y)/log Q + Q + 1` primes in `[x, x + y)`, uniformly in `x`;
- `card_primes_Ico_le_two_pi` — for every `ε > 0` there is a `Y` with at most `(2π + ε) y / log y` primes in `[x, x + y)` for all `y ≥ Y` and all `x` (previously `13 y/log y + √y + 1`, or `9` above `log y ≥ 24`), by sieving at `Q = ⌊√y / log y⌋`; `card_primes_Ico_le_two_pi_aux` makes the threshold explicit (`log y ≥ (1000/ε)² + 10⁶`);
- `card_primes_range_le_two_pi` — the case `x = 0`: `π(N) ≤ (2π + ε) N / log N` for large `N`;
- `card_primes_Ico_mod_le_of_level` and `card_primes_Ico_mod_le_two_pi` — the same for arithmetic progressions: the existing progression bound is generalized to a free level (its old statement retained as the level `⌊√Y⌋`), and with `Y = ⌊y/q⌋ + 1` the count of primes of `[x, x + y)` in a class `a` mod `q` is at most `(2π + ε)(q/φ(q)) Y / log Y`, uniformly in `x`, `q` and `a` (previously the same shape with `8.3`).
What still separates this from the classical `2 + o(1)` is exactly the factor `π` that this project's large sieve carries in place of `1`; that is recorded, not papered over.

**Bookkeeping**, following the repository's own protocol: two new evidence files under `docs/goal/evidence/`, updated `latest_update`, `open_boundary`, exit criteria and gates for the two rows (both remain `DONE_WEAK`, since their constants are still not sharp), regenerated `docs/current-goal-state.md`, new axiom checks in `scripts/audit.sh`, new pinned statements in `scripts/revalidation.lean`, and a README entry for the new Kusmin–Landau module (I also corrected the README's description of the older one, which overstated its hypothesis).

**What is not finished.** "All tasks" cannot be completed: the board's remaining 56 open rows culminate in the Riemann hypothesis itself, which is an open problem, and most of the rest need inputs that exist in neither Mathlib nor this project — the approximate functional equation (van der Corput's B process), Selberg's majorant or the Montgomery–Vaughan Hilbert inequality for the sharp large sieve constant, a sharp fourth moment, Vinogradov's mean value theorem. Those boundaries are stated honestly in the task board and I did not weaken any of them.

# Summary of changes for run 35293947-4625-4ae3-aa9b-a6cc27e96e7c
按您的建议做了 M2-DENSITY 的显式化：把 Carlson 链条里的每个指数都用 θ = σ₀ − 1/2 追踪出来，从「∀σ ∃c」升级成「c 是 σ 的显式函数」。全仓 `lake build` 通过（9190 个目标），`scripts/audit.sh` 打印 `OK`，无 `sorry`，新结果的 `#print axioms` 恰为 `propext, Classical.choice, Quot.sound`。

**新的主结论**（`RiemannHypothesis/CarlsonDensityPowerSaving.lean`）

- `ncard_zerosRightOf_le_rpow_explicit`：对 1/2 < σ < 1，存在 C > 0 使得对一切 T ≥ 1，N(σ, T) ≤ C·T^(1 − (σ−1/2)²/64)。
- `ncard_zerosOffCriticalLine_le_rpow_explicit`：双侧形式，指数 1 − δ²/64。
- 原有的存在性命题 `exists_ncard_zerosRightOf_high_le_rpow`、`exists_ncard_zerosRightOf_le_rpow` 现在多带一个合取项 `(σ − 1/2)²/64 ≤ c`。

**常数是怎么追出来的**（`RiemannHypothesis/CarlsonPowerSaving.lean`，语句都加了显式合取项）

- Montgomery–Vaughan 那一半：γ = α(3/2 − σ₀) 恰等于 1 − θ/2（一行恒等式）。
- Euler–Maclaurin 那一半：β = 2α(1 − σ₀) ≤ 1 − θ（写成 u = 3/2 − σ₀ 后即 u + 1/2 − 1/(2u) ≤ u）。
- 关键改动：mollifier 指数原来取的是 (1 − max(γ,β))/4——只有上界、没有下界，正是「一串 min」的源头；现在直接定义为 θ/8，仍满足 γ′+γ ≤ 1 − 3θ/8 与 2γ′+β ≤ 1 − 3θ/4，于是均方节省 ≥ 3θ/8。
- 圆周平均层：σ₀ = min(3−R, 3/4) 给出 θ = min(5/2−R, 1/4) 的等式。
- 计数层：κ = (σ−1/2)/4、R = 3−σ+2κ 使 θ = (σ−1/2)/2，三项平衡后 c ≥ θ²/16 = (σ−1/2)²/64。

**诚实的边界**（已写进模块 docstring、任务板、证据文件、README）

- 得到的节省是 (σ−1/2) 的**二次式**，不是 exit criteria 里写的线性形 O(T^(1−c(σ−1/2)))。线性节省是 Selberg/Ingham 的强度，需要 sharp mean value theorem 或四阶矩，库里和 mathlib 都没有——所以 M2-DENSITY 这一行我标成 DONE_WEAK，并把「线性形未证、以及缺什么前置定理」明确写进 open_boundary 和改写后的 exit criteria，而不是假装达标。
- 与 Carlson 的 4(σ−1/2)² 相比形状相同、常数差 256 倍；C(σ) 仍不显式；对 σ 不一致、σ = 1/2 处无任何结论；零点不计重数。

**记账**：新增证据文件 `docs/goal/evidence/2026-09-02-m2-density-explicit-exponent.md`；更新 M2-DENSITY 与 M2-DENSITY-POWER-SAVING 两行（`python3 scripts/goal_state.py validate` 通过，145 行；`render` 已重生成 `docs/current-goal-state.md`）；两个显式命题按仓库惯例钉进 `scripts/revalidation.lean`、加进 `scripts/audit.sh` 的公理检查；README 相应段落与表格已更新。旧证据文件末尾追加了一条指向新结论的更新说明（未删改原文）。

**M2-MOLLIFIER 未动**，与您的判断一致：临界线上 γ = (5/2−σ₀)/2 在 σ₀ = 1/2 处恰好退化为 1，不是调参能救的，缺的是前置定理而非设计。

另外，交付时的依赖锁文件与 `lakefile.toml` 的固定版本不一致（缺少 vendored `Zeta23` 的 path 依赖、Mathlib 修订与 toolchain 不匹配），已重新解析依赖使其与项目自身的固定版本一致后再构建。

# Summary of changes for run 66fe9c79-b333-4421-8df9-b9c479cb1441
I picked up the open boundary that the previous round of work had explicitly left in the twin-prime file and closed it, so the project now contains Brun's theorem itself, not just the counting bound behind it.

**New module `RiemannHypothesis/BrunConstant.lean`** (sorry-free; every result checked to depend on exactly the standard axioms `propext`, `Classical.choice`, `Quot.sound`):

- `twinInv` — `1/n` restricted to the `n` with `n` and `n + 2` both prime — and `blockSum`, its dyadic blocks over `[2ᵏ, 2ᵏ⁺¹)`.
- `blockSum_le` — every dyadic block is at most `3753/(k+1)²`. For `k ≥ 46` this comes from the twin-prime counting bound `card_twinPrimes_le` already in the project (`≤ 900 N/(log N)² + √N + 1` for `log N ≥ 32`), applied at the block endpoint `M = 2ᵏ⁺¹`, using `log M = (k+1) log 2 ≥ 32`, the elementary induction `k⁴ ≤ 2ᵏ` for `k ≥ 47` (which controls the `√M` and the additive `1`), and `(log 2)² ≥ 0.48`; for `k < 46` the trivial bound `blockSum k ≤ 1` suffices.
- `sum_inv_twinPrimes_le` — the reciprocals of the twin primes below `N` sum to at most `6600`, uniformly in `N`, by summing the blocks against `∑ 1/d² ≤ 7/4`.
- `summable_twinInv` — **Brun's theorem**: the series of the reciprocals of the twin primes converges; and `tsum_twinInv_le`, its sum is at most `6600`.
- `infinite_setOf_prime_not_prime_add_two` — a corollary: there are infinitely many primes `p` with `p + 2` composite, since the sum of all prime reciprocals diverges while its twin part converges.

Stated scope, recorded in the module docstring, the task-board row and the evidence file: the constant `6600` is an upper bound only and is far from the Brun constant `1.902…` (it inherits the non-sharp constant `900` and uses crude dyadic summation); no digit of that constant is certified; no lower bound is claimed, and nothing follows about the twin-prime conjecture, which stays open — convergence is compatible with there being only finitely many twin primes. Nothing about ζ follows.

**Repository bookkeeping**, following the project's own conventions: the module is imported from `RiemannHypothesis.lean`; the five main statements are pinned in full in `scripts/revalidation.lean` under a new `M2-BRUN-CONSTANT` heading; six `#print axioms` checks were added to `scripts/audit.sh`; a new task-board row `M2-BRUN-CONSTANT` and the evidence file `docs/goal/evidence/2026-09-01-m2-brun-constant.md` were written, the superseded "no convergence statement is drawn" notes in the twin-prime module and its evidence file were corrected, and `docs/current-goal-state.md` regenerated (145 tasks validate).

**Gates**: `lake build` completes with no errors; `scripts/revalidation.lean` elaborates cleanly; the full audit script ran to completion twice with no failures, all 688 axiom checks reporting exactly the three standard axioms. The properties table is reconciled: the twin-prime bound, sifting-sum and sieve statements from the earlier work, and the four new Brun results, are all marked proved.


# Summary of changes for run a09cdc0f-9896-4d2c-a6b9-e8b986205af6
I continued the project by closing the next open boundary the repository itself recorded: the large sieve over squarefree moduli was proved, but no sieve consequence had been drawn from it. That consequence is now proved.

**New module `RiemannHypothesis/BrunTitchmarsh.lean`** (namespace `RiemannHypothesis.BrunTitchmarsh`), sorry-free and warning-free:

- `siftSum Q` — the sifting sum of the large sieve at the weights `w p = p − 1`, i.e. `∑_{q ≤ Q squarefree} ∏_{p ∣ q} 1/(p − 1)`.
- `inv_le_prod_inv_sub_one`, `sum_inv_squarefree_le_siftSum` — `∑_{q ≤ Q squarefree} 1/q ≤ siftSum Q`, since a squarefree `q` is the product of its prime factors and `1/p ≤ 1/(p − 1)`.
- `harmonic_cast`, `log_le_sum_inv`, `sum_inv_le_log_add_one` — `log Q ≤ ∑_{n ≤ Q} 1/n ≤ log Q + 1`.
- `sum_inv_multiples_le`, `sum_biUnion_le_sum_sum`, `sum_inv_not_squarefree_le` — the reciprocals of the non-squarefree `n ≤ Q` sum to at most `(3/4)(log Q + 1)`, by reindexing the multiples of `d²` and a union bound over `d ∈ [2, Q]`.
- `quarter_log_le_sum_inv_squarefree`, `quarter_log_le_siftSum` — `siftSum Q ≥ (log Q)/4 − 3/4`.
- `card_mul_siftSum_le` — the sieve for a set `A ⊆ [0, N)` avoiding one residue class modulo every prime `p ≤ Q`: `|A| · siftSum Q ≤ Q² + π N`.
- `card_primes_Ico_eq`, `shifted_primes_avoid`, `half_log_sub_log_two_le_log_sqrt` — the three ingredients of the application.
- `card_primes_Ico_le` — **a Brun–Titchmarsh inequality**: uniformly in the starting point `x`, the number of primes in `[x, x + y)` is at most `70 y / log y + √y + 1`, whenever `log y ≥ 24`.
- `card_primes_range_le` — its case `x = 0`, a Chebyshev-type upper bound `π(N) ≤ 70 N / log N + √N + 1`.

The constant `70` and the threshold `log y ≥ 24` are honest artefacts of the crude bounds used (the sharp constant is `2`); this is stated in the module docstring, the board row's open boundary and the evidence note, together with what is *not* proved (no arithmetic-progression form, no Bombieri–Vinogradov, nothing about `ζ`).

**Repository bookkeeping.** The module is imported from `RiemannHypothesis.lean`; the six main statements are pinned in `scripts/revalidation.lean` under a new `M2-BRUN-TITCHMARSH` heading (statement written out, repository declaration supplied as the proof term) and their axiom checks added to `scripts/audit.sh`; a new board row `M2-BRUN-TITCHMARSH` was added to `docs/goal/task-board.yaml` with exit criteria, open boundary and required gates, together with the evidence note `docs/goal/evidence/2026-09-01-m2-brun-titchmarsh.md` containing the required adversarial-revalidation section; the open boundary of `M2-LARGE-SIEVE-SQUAREFREE` was amended to point at what is now closed, and `docs/current-goal-state.md` was regenerated.

**Verification.** `lake build RiemannHypothesis.BrunTitchmarsh` succeeds with no errors and no warnings; `bash scripts/audit.sh` runs end to end and prints `OK` (exit 0), which includes the full build, the sorry scan, the axiom checks and the board validation (143 tasks). `#print axioms` for every new statement reports exactly `[propext, Classical.choice, Quot.sound]`. No `sorry` exists anywhere outside `Challenge.lean`, whose three sorries are the repository's intended statement of record. `ARISTOTLE_SUMMARY.md` was left untouched. All work is committed and pushed.


# Summary of changes for run 89f2c688-637d-4f9f-a5dc-99ca55612aa0
This session added two completed, fully documented increments to the project's task board, both machine-checked and with every repository gate green.

**1. Weyl's inequality generalized from monomial to arbitrary polynomial phases** (rows `M1-WEYL-CLASSICAL`, `M1-WEYL-BADLY-GENERAL`)

`RiemannHypothesis/WeylClassical.lean` and `RiemannHypothesis/WeylBadlyGeneral.lean` now state their results for an arbitrary polynomial phase `f` of degree at most `d = r + 2` with leading coefficient `α`, instead of only the monomial phase `α n^d` (which is kept as one-line corollaries):

* `norm_polyPhaseSum_pow_le_three_term` — the classical three-term inequality with explicit constants, for every denominator `q > 0`;
* `exists_norm_polyPhaseSum_pow_le_three_term` — divisor loss and logarithm absorbed into `N^ε`;
* `exists_norm_polyPhaseSum_le_three_term` — `‖∑ e(f n)‖ ≤ C N^(1+ε) (1/q + 1/N + q/N^d)^(1/2^(d−1))`;
* `exists_norm_polyPhaseSum_pow_mul_le_of_badlyApproximable`, `exists_norm_polyPhaseSum_le_of_badlyApproximable` — Weyl's exponent `1 − 1/2^(d−1) + ε` when `d!α` is badly approximable, plus the explicit coefficient `√2/d!`.

The two task-board rows, their evidence files, the revalidation pins and the axiom checks were updated accordingly.

**2. A new row, `M1-WEYL-INTERVAL`: Weyl's inequality over an arbitrary interval** (new module `RiemannHypothesis/WeylInterval.lean`)

* `WeylGeneral.IsPolyPhase.comp_add` — a translate `n ↦ f (n + M)` of a polynomial phase is a polynomial phase of the same degree with the *same* leading coefficient (binomial expansion plus an exchange of sums);
* `sum_e2pi_Ico_shift` — `∑_{M ≤ n < M+N} e(f n) = ∑_{0 ≤ n < N} e(f (n+M))`;
* `norm_polyPhaseSum_Ico_pow_le_three_term`, `exists_norm_polyPhaseSum_Ico_pow_le_three_term`, `exists_norm_polyPhaseSum_Ico_le_three_term` — the three-term Weyl inequality over `[M, M+N)`, with constants and exponents independent of the starting point `M`;
* `exists_norm_polyPhaseSum_Ico_le_of_badlyApproximable` — Weyl's exponent over an arbitrary interval;
* monomial corollaries and the explicit example `α = √2/d!` over an arbitrary interval.

The new module is imported by `RiemannHypothesis.lean`, its declarations are axiom-checked in `scripts/audit.sh`, pinned by `example`s in `scripts/revalidation.lean`, documented in `docs/goal/evidence/2026-08-31-m1-weyl-interval.md` (including the adversarial-revalidation section), and registered as a row in `docs/goal/task-board.yaml`.

**Verification.** Full `lake build` succeeds; `lake env lean scripts/revalidation.lean` is clean; `docs/goal/conditional-theorems.txt` was regenerated (the two new entries appear only in the `DEFINITIONAL` section, i.e. hypotheses on the theorem's own argument, not open assumptions, and this is recorded in the evidence files); `python3 scripts/goal_state.py validate` reports `OK: 141 tasks validate`; a full `bash scripts/audit.sh` run started after all edits reports `OK`. Every new declaration has axioms exactly `[propext, Classical.choice, Quot.sound]`, and there is no `sorry` anywhere outside `Challenge.lean`. All work is committed and pushed.

The Riemann hypothesis itself remains open in the repository; these rows are prerequisites in the analytic-number-theory track and claim nothing about ζ.

# Summary of changes for run c95a03b2-c891-4b30-b3a3-3f1f75de7885
I continued the Weyl-inequality strand of the project and closed the item that several rows of the task board named as their open boundary: the general degree-`d` Weyl inequality and the evaluation of its right-hand side. The Riemann Hypothesis itself remains open in the repository, as expected.

**New machine-checked mathematics** (all in `RiemannHypothesis/WeylGeneral.lean`, which builds with `lake build RiemannHypothesis.WeylGeneral`, contains no `sorry`, and whose results use exactly the axioms `propext`, `Classical.choice`, `Quot.sound`):

- `weylMulti` — the `r`-fold shifted majorant sum `W₀(m) = min(N, 1/(2‖βm‖))`, `W_{r+1}(m) = ∑_{k<H} W_r(mk)`, with the zero shifts included.
- `IsPolyPhase` and `IsPolyPhase.diff` — differencing a polynomial phase lowers its degree by one and multiplies the leading coefficient by `(d+1)k`.
- `norm_polyPhaseSum_pow_le` — **Weyl's inequality in arbitrary degree**, by induction on `d`: for any polynomial phase of degree ≤ `d+1` with `n^{d+1}`-coefficient `α` and any `H ≥ 1`, `‖∑_{0≤n<N} e(f n)‖^{2^d} · H^d(N+H) ≤ 8^{2^d}(N+H)^{2^d} · W_d((d+1)!α)`, with no additive error term (each diagonal is absorbed by the zero shift).
- `dioSum`, `dioSum_le_of_approx`, `weylMulti_le_dioSum`, `weylMulti_le_of_approx` — the `r+1` shifts folded onto their product, and the resulting one-dimensional majorant sum estimated by the repository's existing counting lemma from a coprime approximation `|d!α − a/q| ≤ 1/q²`.
- `norm_monomialSum_pow_le_of_approx` and `norm_monomialSum_pow_mul_le_of_approx` — the two combined for the monomial phase `α n^d`, the latter in the clean form `‖∑_{n<N} e(α n^{r+2})‖^{2^{r+1}} · H ≤ 16^{2^{r+1}} N^{2^{r+1}} (r + 11 + 2 log N)` valid whenever `H^{r+1} ≤ q ≤ N`; for `H` of size `N^{1/(r+1)}` this is a saving of `N^{−1/((d−1)2^{d−1})}` over the trivial bound, up to a logarithm.

The exponent reached is `1 − 1/((d−1)2^{d−1})`, weaker than the classical `1 − 1/2^{d−1}`; the loss is the crude fold of the shift tuples onto their product, where the classical argument uses the average divisor bound, which is not formalized here. No Vinogradov mean value theorem, no unconditional badly-approximable form in general degree, and nothing about `ζ` follows. These limitations are stated in the module docstring, the task-board row and the evidence file rather than glossed over.

**Repository bookkeeping**, following the project's own conventions: new row `M1-WEYL-GENERAL` (status `DONE_WEAK`, with an explicit open boundary) in `docs/goal/task-board.yaml` (validates: 135 tasks); the stale "the general degree-`d` case is not formalized" clauses in the quadratic, min-sum and cubic rows updated; new evidence file `docs/goal/evidence/2026-08-30-m1-weyl-general.md` including an adversarial-revalidation section; statement pins for the six new results added to `scripts/revalidation.lean` (verified to elaborate); `#print axioms` checks and the module import added to `scripts/audit.sh`; the module added to `RiemannHypothesis.lean` and to the README module table; `docs/current-goal-state.md` regenerated.

Two caveats about this environment, unchanged from the previous session: the available Mathlib is an earlier revision than the one the project pins, so roughly fifty pre-existing modules and the vendored `Zeta23` library still fail to compile for version-drift reasons, and consequently a full `lake build` and `./scripts/audit.sh` cannot pass here. That is pre-existing and independent of the new module, which builds cleanly on its own. All work is committed and pushed.

# Summary of changes for run 5167c987-42bc-4232-bf59-20aa72e64c5b
Continued and completed the next stage of the project. Everything below builds with `lake build` and passes the repository's own audit script end to end (`./scripts/audit.sh` → OK), with no `sorry` outside `Challenge.lean` and axioms exactly `propext`, `Classical.choice`, `Quot.sound` for every new statement. All work is committed and pushed.

**1. Finished integrating the cubic Weyl bound (`RiemannHypothesis/WeylCubic.lean`).**
The module itself was already proved; this session completed everything the repository requires around it: a new task-board row `M1-WEYL-CUBIC` with an honest open boundary, a new evidence file `docs/goal/evidence/2026-08-30-m1-weyl-cubic.md` (claim / proof / why the row exists / scope / adversarial revalidation), axiom checks in `scripts/audit.sh`, pinned statements in `scripts/revalidation.lean`, a README row, and a regenerated `docs/current-goal-state.md`. The open boundaries of the quadratic rows, which said the degree-3 case was missing, were corrected to point at the new row. Main results: `‖∑_{0≤n<N} e(α n³)‖⁸ ≤ 2²² (4N/q+1)² N⁷ (1+log 4N)²` from a coprime approximation `|6α − a/q| ≤ 1/q²` with `q ≤ 4N`; the unconditional form for badly approximable `6α`; and the explicit instance `α = √2/6`. The exponent obtained is 7/8, weaker than the classical 3/4, and this is stated in the module, the row and the evidence.

**2. New mathematics: the large sieve for sifted sets (`RiemannHypothesis/LargeSieveSifted.lean`).**
This closes, over prime moduli, the gap named by the existing Farey large sieve row ("the large sieve for exponential sums at rational points only", with no sieve consequence drawn). Proved from scratch: orthogonality of the additive characters modulo `q`; Parseval's identity `∑_{b<q} ‖∑_{n∈A} e(nb/q)‖² = q ∑_r (#{n ∈ A : n ≡ r})²`; the Cauchy–Schwarz lower bound over the classes a set actually meets; the lower bound at a prime modulus; and hence Montgomery's inequality `|A| ∑_{p≤Q} (p − ω_p)/ω_p ≤ Q² + πN` for `A ⊆ [0,N)` meeting at most `ω_p` residue classes modulo each prime `p ≤ Q`. Two consequences are drawn: a set meeting at most half the classes modulo every prime `p ≤ Q` satisfies `|A| · #{p ≤ Q} ≤ Q² + πN`; and, as a worked example with no hypothesis left to the caller, the squares below `N` satisfy `#{n < N : n is a square} · #{odd primes p ≤ Q} ≤ 3(Q² + πN)`, using that the squares meet at most `(p+1)/2` classes modulo an odd prime. The module records that only prime moduli are treated — the multiplicative extension to squarefree moduli via the Chinese remainder theorem, which is what a Selberg- or Bombieri–Vinogradov-strength application would need, is not formalized — that the constant carries the inherited factor `π`, that for the squares themselves the bound is weaker than the trivial `√N`, and that nothing about `ζ` follows.

The module was given the same treatment as the rest of the repository: imported from `RiemannHypothesis.lean`, a new board row `M2-LARGE-SIEVE-SIFTED`, an evidence file `docs/goal/evidence/2026-08-30-m2-large-sieve-sifted.md`, ten axiom checks in `scripts/audit.sh`, six pinned statements in `scripts/revalidation.lean`, a README row, and a regenerated goal state (`134 tasks validate`).

The Riemann Hypothesis itself remains open and is not claimed anywhere; the frontier rows of the board (RH, Vinogradov, the density and mollifier rows) are still marked as needing design, as before.

# Summary of changes for run bcc26a7a-b332-48be-8545-1a0809760325
I picked up the project, restored its build, and added two new pieces of formalized mathematics, each fully integrated into the repository's own evidence/audit machinery.

**Build repair.** The delivered `lake-manifest.json` had lost the `vendor/zeta23` path dependency and pointed at a mathlib revision incompatible with the pinned `lean-toolchain`, so nothing compiled. Restoring the pinned toolchain (`v4.33.0`) in both `lean-toolchain` files and re-resolving the dependencies fixed it; `lake build` now completes with 0 errors.

**New: `RiemannHypothesis/WeylMinSum.lean` — the counting lemma of Weyl's method.** This closes the gap explicitly named in the scope section of `RiemannHypothesis/WeylQuadraticQuantitative.lean` and in the board row `M1-WEYL-QUADRATIC`. For a rational approximation `|β − a/q| ≤ 1/q²` with `a`, `q` coprime, and any majorant `g` of `min(N, 1/(2‖βk‖))`:
- `sum_block_le`: over `q` consecutive integers, `∑ g k ≤ 4N + q(1 + log q)` (the classical grid argument: `gridIndex`, `grid_sub_le_intDist`, `gridIndex_injOn`, plus a harmonic sum);
- `sum_Ioc_le`: the counting lemma `∑_{0 < k ≤ H} g k ≤ (H/q + 1)(4N + q(1 + log q))`;
- `normSq_quadSum_le_of_approx_count`, `normSq_quadSum_le_of_approx_large`, `norm_quadSum_le_of_approx_large`: feeding it into the differencing inequality with `H = N` rather than `H = q/2` gives `‖∑_{n<N} e(α n²)‖ ≤ 9 √(N(1 + log 2N))`, improving the repository's previous exponent `3/4` to `1/2` up to a logarithm.

**New: `RiemannHypothesis/WeylBadlyApproximable.lean` — an unconditional rate.** The bounds above are conditional on the existence of an approximation with a denominator in a prescribed range. Using Dirichlet's approximation theorem, that hypothesis is discharged for the badly approximable coefficients:
- `BadlyApproximable`, `exists_coprime_approx`, `le_den_of_badlyApproximable`, `normSq_quadSum_le_of_den_le`;
- `norm_quadSum_le_of_badlyApproximable`: if `2α` is badly approximable with constant `c`, then `‖∑_{n<N} e(α n²)‖ ≤ √((16/c + 26) N (1 + log N))` for every `N ≥ 1`, with no hypothesis left to the caller;
- `badlyApproximable_of_quadratic`: every quadratic irrational is badly approximable (Liouville's argument, with the explicit constant `1/(|A|(2|x|+1) + |B|)`), hence `exists_norm_quadSum_le_of_quadratic`;
- `badlyApproximable_sqrt_two` and `norm_quadSum_sqrt_two_le`: the fully explicit instance `‖∑_{n<N} e((√2/2) n²)‖ ≤ √(90 N (1 + log N))`.

Both files build with no `sorry` and no warnings; `#print axioms` reports exactly `propext, Classical.choice, Quot.sound` for every statement. Both modules are imported by `RiemannHypothesis.lean`; their main statements are pinned in `scripts/revalidation.lean` (statement written out, repository declaration supplied as the proof term) and their axiom checks added to `scripts/audit.sh`. Two evidence notes were added under `docs/goal/evidence/`, two new rows (`M1-WEYL-MIN-SUM`, `M1-WEYL-BADLY-APPROXIMABLE`) added to `docs/goal/task-board.yaml` with their open boundaries stated, the boundaries of `M1-WEYL-QUADRATIC` and `M1-WEYL-EQUIDISTRIBUTION` updated to point at what is now closed, and `README.md` and `docs/current-goal-state.md` regenerated. `scripts/audit.sh` passes end to end and the board validator reports 129 tasks valid.

**What is not done, honestly.** The Riemann hypothesis itself is not proved, and no route to it is claimed: the board's `M4-RH` row and the research rows it depends on (`M3-GAP`, `M3-VINOGRADOV`, `M2-DENSITY`, `M2-SELBERG-CLT`, `M2-PAIR-CORRELATION`, `M1-NUMERICAL`, and the rest) remain `TODO_NEEDS_DESIGN`. Most previously `DONE_WEAK` rows still carry their recorded open boundaries. Nothing in the new work says anything about the zeta function: it is about exponential sums only, no subconvexity bound, approximate functional equation or density estimate follows. Within the new work itself, the logarithm is not removed (the bound is `√(N log N)`, not `N^{1/2+ε}`), the constants are not optimized, only the quadratic phase is treated — the general degree-`d` Weyl inequality is still open — and only the badly approximable coefficients get a rate. The `sorry`s in `Challenge.lean` are the repository's intended problem statement and are answered in `Solution.lean`; they were left untouched.

# Summary of changes for run a16999a2-f560-434b-9791-7f5f3a8bb93b
I continued the Riemann Hypothesis formalization from where the previous session stopped, and closed out the piece of work that was still open: the **power saving in Carlson's density theorem**.

**What was unfinished:** `RiemannHypothesis/CarlsonPowerSaving.lean` contained four `sorry`s — the combination of the two halves of the quantitative mean square, its transport to circle averages, the counting argument, and the two-sided form.

**What I proved (all sorry-free, verified by a full build):**

- `exists_integral_normSq_zeta_mul_mollifier_sub_one_le_rpow` — the mean square of `ζ M_y − 1` on a vertical segment for a mollifier length that may grow with the height: `∫_a^b ‖ζ M_y − 1‖² ≤ C (b y^{−(σ₀−1/2)} + b^{1−c})` whenever `y ≤ 4 b^γ`, obtained from the Montgomery–Vaughan half and the Euler–Maclaurin half with explicit exponent bookkeeping (plus a small auxiliary fact `four_mul_rpow_le_self`).
- `exists_integral_circleAverage_normSq_mollifiedZeta_sub_one_le_rpow` — the same estimate for circle averages, by Fubini, with the shifted endpoints costing at most a factor two.
- In a new file `RiemannHypothesis/CarlsonDensityPowerSaving.lean` (the mean-square file was getting long, so the counting argument lives separately):
  - `exists_ncard_zerosRightOf_high_le_rpow` — the Jensen counting inequality run with `y = ⌈T^γ⌉` and `λ = T^{c'}`, balancing the three terms;
  - `exists_ncard_zerosRightOf_le_rpow` — **`N(σ, T) ≤ C·T^{1−c}` with `c > 0`, for every fixed `1/2 < σ < 1` and every `T ≥ 1`**, strengthening the previously available `o(T)`;
  - `exists_ncard_zerosOffCriticalLine_le_rpow` — the two-sided form.

Zeroes are counted without multiplicity. The exponent `c` is not explicit and is far from Carlson's `1 − 4σ(1−σ)`: only the existence of *some* power saving is claimed. Nothing about the location of individual zeroes follows, and the Riemann hypothesis is neither proved nor disproved.

**Project hygiene:** the two new modules are imported from `RiemannHypothesis.lean`; the new statements are pinned in `scripts/revalidation.lean` and their axioms checked in `scripts/audit.sh` (they use exactly `propext`, `Classical.choice`, `Quot.sound`); a new task-board row `M2-DENSITY-POWER-SAVING` with an evidence file under `docs/goal/evidence/` was added, the board re-validated (127 tasks) and `docs/current-goal-state.md` regenerated; the README module table and the density section were updated. The full `lake build` succeeds, `scripts/audit.sh` ends in `OK`, and the only remaining `sorry`s in Lean code are the three intentional ones in `Challenge.lean`. All work is committed and pushed.

# Summary of changes for run fb179065-9a28-48f9-be2c-5d7c294c2e09
I continued the project by closing the gap the repository's own notes recorded as open: the mean value theorem for Dirichlet polynomials with the error term *inside* the sum (the Montgomery–Vaughan shape), and its discrete counterpart. Both are now proved without `sorry`, and both are fully wired into the repository's bookkeeping and audit gates.

**New module `RiemannHypothesis/GaussianMeanValue.lean` (completed).** The three remaining unproved statements in this file are now proved, so the module is sorry-free:

- `integral_normSq_dirichletPoly_le_mv` — for `T ≥ 6`,
  `∫₋ᵀᵀ ‖D(σ + i t)‖² dt ≤ 58 ∑_{n ≤ N} ‖a n‖² n^(−2σ) (T + n)`,
  and `integral_Icc_normSq_dirichletPoly_le_mv`, the same over `[0, T]`.
- `sum_exp_neg_sq_log_sub_le` — the arithmetic input: `∑_{n ≤ N} exp(−L²(log n − log m)²) ≤ 1 + 6 m / L` for `L ≥ 3`.

The route is the Gaussian majorant rather than the generalized Hilbert inequality: on `[−T, T]` the indicator is at most `e·exp(−t²/T²)`; the resulting oscillatory integral turns the weighted mean square into a bilinear form with kernel `exp(−(T/2)²(log n − log m)²)`; the row sums of that kernel are bounded by splitting at `n = 2m` (near the diagonal, the logarithmic separation is compared with the integer separation and the resulting Gaussian is summed by the integral test; far from it, the kernel is dominated by `m²/n²` times a small constant); Schur's test then gives the bilinear bound. Supporting lemmas proved along the way include the integral test for Gaussians, `|y − x| / max x y ≤ |log y − log x|`, the tail bound `∑_{n > M} 1/n² ≤ 1/M`, and the numerical estimate `e√π ≤ 4.8182`.

**New module `RiemannHypothesis/GaussianMeanValueDiscrete.lean`.** Feeding the above into the repository's Gallagher/Sobolev lemma gives the discrete version in the same shape:
`∑_i ‖D(σ + i t_i)‖² ≤ 58 (2/δ + δ (log N)²) ∑_{n ≤ N} ‖a n‖² n^(−2σ) (T + n)` for `δ`-separated `t_i ∈ [δ/2, T − δ/2]` and `T ≥ 6`, together with the corresponding large-values count.

**Honest scope.** The constant `58` is explicit but not sharp (Montgomery and Vaughan's theorem has the asymptotically optimal main term); only the *shape* of the error term is claimed. All statements are about Dirichlet polynomials, not about ζ: no zero-density estimate follows and no zero is located. These caveats are recorded in the module docstrings, the task-board rows, and the evidence notes.

**Repository bookkeeping and verification.** Both modules are imported from the root `RiemannHypothesis.lean`; two new task-board rows (`M2-MEANVALUE-MV`, `M2-DISCRETE-MEANVALUE-MV`) with exit criteria and explicit open boundaries were added, with matching evidence notes under `docs/goal/evidence/`; the eight new statements are pinned in `scripts/revalidation.lean` and their axioms checked in `scripts/audit.sh`; `docs/current-goal-state.md` was regenerated. The full `lake build` succeeds, `#print axioms` on every new result gives exactly `propext, Classical.choice, Quot.sound`, no `sorry` remains outside `Challenge.lean`, and `./scripts/audit.sh` ends with `OK` (125 tasks validate). All work is committed and pushed. `ARISTOTLE_SUMMARY.md` was left untouched.

# Summary of changes for run 5ec97750-dcad-46e1-9621-9dd2c101b3f6
Short answer: **no — not everything on the project's task board is finished, and it cannot honestly be marked as such.** The Riemann hypothesis itself is still open and is not proved here. What I did this session was restore the project to a verified, building state and clean it up; here is the exact status.

**What I verified (not just claimed)**
- `lake build` completes with **0 errors** (9158 jobs), and the repository's own `scripts/audit.sh` prints `OK`.
- The **only** `sorry`s anywhere in the build are the three intentional ones in `Challenge.lean` — the statement of record, which the repository's convention requires to be left unproved there and which `Solution.lean` discharges. No other source file (including the vendored library) contains a `sorry`; the remaining textual matches there are comments.
- The audit's other checks pass: every compared theorem depends on exactly `propext`, `Classical.choice`, `Quot.sound`; no `Float`; the closed task-board rows are pinned in `scripts/revalidation.lean`; the board validates (119 tasks).

**What I fixed this session**
1. *The project as delivered did not build at all.* `lake-manifest.json` was inconsistent with `lakefile.toml`: it named a different mathlib revision and URL, and it was missing the vendored `Zeta23` path dependency, so every `lake` command failed before compiling a single file. I re-resolved the dependencies so the manifest now agrees with `lakefile.toml` (mathlib `db584cd6…`) and with `lean-toolchain` (`v4.33.0`), and committed the corrected manifest so the problem does not recur.
2. *Linter and deprecation cleanup in this repository's own sources.* I applied every mathlib deprecation rename flagged by the build (e.g. `Set.mem_setOf_eq → Set.mem_ofPred_eq`, `Set.Finite.diff → Set.Finite.sdiff`, `intervalIntegral.integral_finset_sum → intervalIntegral.integral_finsetSum`, `Matrix.det_of_upperTriangular → Matrix.det_of_isUpperTriangular`, `ENat.toNat_coe → ENat.toNat_natCast`, and others), replaced the deprecated `push_neg` uses, and added the explanatory comment the style linter requires next to a `maxHeartbeats` override. After this, the build emits **no warnings at all** from this repository's files apart from the three intentional `sorry` notices in `Challenge.lean`. I fixed the code rather than disabling any linter, and left the third-party vendored library untouched.

**What remains open (from `docs/current-goal-state.md`, 119 tasks)**
- `DONE_STRONG`: 83 · `DONE_WEAK`: 25 · `TODO_NEEDS_DESIGN`: 10 · `TODO_READY`: 1.
- Still genuinely open, and honestly marked so on the board: the Riemann hypothesis itself (`M4-RH`, and the `M3-GAP` row it depends on — no known route); Carlson's density theorem behind `M1-ALMOST-ALL-STRIP` (the Bohr–Landau `O(T)` bounds proved here do not reach the required `o(T)`; a mollified mean square is needed); the logarithm-free convexity exponent in `M1-GROWTH`; the mollifier, density, Selberg CLT and pair-correlation rows in M2; Vinogradov's method, the Atiyah verification and the geometric route in M3; and the large-scale numerical verification.

So: the repository is in a clean, fully verified, reproducible state, and all the work that *is* claimed there is machine-checked — but the task board is deliberately not complete, because the mathematics of its top rows is open research rather than unfinished formalization. All changes are committed and pushed.

# Summary of changes for run 74add9e2-7953-4cee-82d1-92a36d2bb758
## About `lean-toolchain` and "4.28"

`lean-toolchain` still reads `leanprover/lean4:v4.33.0` — it was never changed. What showed `4.28` was `lake-manifest.json`: its mathlib entry carried `inputRev: "v4.28.0"` together with a mathlib revision from the 4.28 line, which contradicted the mathlib commit pinned in `lakefile.toml` (a Lean 4.33 mathlib). That inconsistency was what broke the build. It has been fixed by re-resolving the dependencies, so the manifest now agrees with `lakefile.toml` and with toolchain v4.33.0; the vendored `Zeta23` path dependency (`vendor/zeta23`), which was missing from the manifest, is also present again. The full build and the repository's own audit both pass.

## Work completed this session

**Build and audit.** `lake build` succeeds (9157 jobs, 0 errors) and `scripts/audit.sh` prints `OK`: no `sorry` outside `Challenge.lean` (whose 3 `sorry`s are the statement of record, discharged in `Solution.lean`), no `Float`, all compared theorems depending on exactly `propext`, `Classical.choice`, `Quot.sound`, all closed task-board rows pinned in `scripts/revalidation.lean`, and the task board validating (119 tasks).

**New mathematics: a discrete mean value theorem (`RiemannHypothesis/GallagherDiscrete.lean`).** This supplies the Sobolev/Gallagher step that the large-values row previously left open. All of it is sorry-free with the three standard axioms:

- `Gallagher.hasDerivAt_normSq_comp` — the derivative of `t ↦ ‖f t‖²` is `2 Re(conj(f t)·f' t)`, bounded by `2‖f‖‖f'‖`.
- `Gallagher.mul_normSq_le_integral_of_mem_Icc` — the one-interval Sobolev inequality, from the fundamental theorem of calculus.
- `Gallagher.sum_integral_window_le` — the windows around δ-separated points are disjoint, so their integrals add up to at most the integral over the enclosing interval.
- `Gallagher.sum_normSq_le_of_separated` — **Gallagher's lemma**: `δ ∑ ‖f(tᵢ)‖² ≤ 2 ∫_A^B ‖f‖² + δ² ∫_A^B ‖f'‖²`.
- `hasDerivAt_dirichletPoly_line` — the derivative of a Dirichlet polynomial along a vertical line is `−i` times the polynomial with coefficients `aₙ log n`; `sum_normSq_logCoeff_le` bounds the new mean-square weight by `(log N)²` times the old one.
- `sum_normSq_dirichletPoly_at_separated_le` — the **discrete mean value theorem**: for δ-separated `tᵢ ∈ [δ/2, T−δ/2]`, `∑ᵢ ‖D(σ+itᵢ)‖² ≤ (2/δ + δ(log N)²)(T + 8N(1+log N)) ∑_{n≤N} ‖aₙ‖² n^(−2σ)`.
- `card_le_of_dirichletPoly_large_separated` — the large-values count that follows by Chebyshev.

Scope, stated explicitly in the module docstring and the task-board row: these are statements about Dirichlet polynomials, not about ζ; the constants are the elementary ones (an `N log N` error rather than the Montgomery–Vaughan `N`); no zero-density estimate is claimed and no zero of ζ is located.

**Documentation and gates.** Added the task-board rows `M2-MOLLIFIED-MEAN-SQUARE` and `M2-DISCRETE-MEANVALUE` with evidence files `docs/goal/evidence/2026-08-28-m2-mollified-mean-square.md` and `docs/goal/evidence/2026-08-28-m2-discrete-meanvalue.md`; refreshed the open boundary of `M2-LARGE-VALUES`; regenerated `docs/current-goal-state.md`; pinned all the new statements in `scripts/revalidation.lean` and added the corresponding `#print axioms` checks to `scripts/audit.sh`. The new module is imported from the root `RiemannHypothesis.lean`.

All work is committed and pushed.


# Summary of changes for run b2a2f651-e889-4b18-88a8-056320c2a1cb
密度这条线的前三步现在都已形式化并通过完整构建,四步中的第四步(组装成 Ingham 型密度估计)仍然是未完成的。所有内容无 `sorry`,公理恰为 `propext, Classical.choice, Quot.sound`,`scripts/audit.sh` 输出 `OK`。

## 第 1 步:大筛不等式 — `RiemannHypothesis/LargeSieve.lean`

- `intDist θ = |θ − round θ|`(到最近整数的距离)及其基本性质,包括 Jordan 不等式 `2‖θ‖ ≤ |sin πθ|`。
- Dirichlet 核 `kernel N θ = ∑_{n<N} e(nθ)`,核估计 `‖K(θ)‖ ≤ 1/(2‖θ‖)`,以及 δ-分离点上的行和界 `sum_norm_kernel_row_le`。
- `large_sieve`:对模 1 两两 δ-分离的点,`∑_i ‖∑_{n<N} a_n e(n t_i)‖² ≤ (N + δ⁻¹(1 + log (2δ)⁻¹)) ∑_n ‖a_n‖²`,以及计数形式 `card_le_of_large_values`。
- 常数带对数损失(尖锐常数 `N + δ⁻¹` 需要 Selberg 主项函数,未形式化),这一点在文档和 open_boundary 里写明了。

## 第 2 步:Halász–Montgomery 大值估计 — `RiemannHypothesis/HalaszMontgomery.lean`

- `sum_normSq_le_of_rowSum_le`(坐标形式,对偶 + Cauchy–Schwarz + Gram 行和)与 `halasz_montgomery`(内积空间形式)。
- 特化到 Dirichlet 多项式:`sum_normSq_dirichletPoly_le` 与大值计数 `card_le_of_dirichletPoly_large`(`R ≤ Δ‖a‖²/V²`)。
- 说明其范围:Gram 行和界 `Δ` 是假设而非供给。把已有的 `integral_normSq_dirichletPoly_mvt_zero` 转到离散分离点上需要 Gallagher/Sobolev 那一步,仓库里没有;所以这里没有声称任何数值型大值定理。

## 第 3 步:Mollifier 零点检测 — `RiemannHypothesis/Mollifier.lean`(本次新增)

- `mollifier y s = ∑_{n≤y} μ(n) n^{−s}`,系数 `detectCoeff y n = ∑_{d∣n, d≤y} μ(d)`。
- 初始区间的消失:`detectCoeff_one`(`c₁ = 1`)与 `detectCoeff_eq_zero_of_le`(`2 ≤ n ≤ y` 时 `c_n = 0`),用的正是仓库 `MertensSums.lean` 里的 `sum_divisors_moebius`。
- `zeta_mul_mollifier_eq_one_add_tail`:`re s > 1` 时 `ζ(s)M_y(s) = 1 + ∑_{n>y} c_n n^{−s}`;`LSeries_tailCoeff_eq` 给出尾部 `= ζ(s)M_y(s) − 1`,故在零点处为 `−1`。
- 另外给出**有限形式、对一切 `s` 成立、不需任何收敛条件**的恒等式:`mollified_partialSum` 与 `mollified_partialSum_eq_one_add_tail`,即 `M_y(s)∑_{k≤K}k^{−s} = 1 + ∑_{y<m≤yK} c_{y,K}(m) m^{−s}`,系数 `c_{y,K}(m) = ∑_{d∣m, d≤y, m/d≤K} μ(d)` 在 `2 ≤ m ≤ min(y,K)` 上消失。
- 诚实的范围说明:无穷级数版本住在 `re s > 1`,那里 ζ 没有零点,所以它本身检测不到零点;要把它带进临界带需要 AFE 或围道移位,这里没有做,因此**没有**任何密度估计从这个文件推出。

## 第二候选:把 MethodCeiling 的手法推广到这条线上(本次新增)

- 大筛的天花板(`LargeSieve.lean`):定义 `AdmissibleConstant C`(常数 `C δ N` 使大筛不等式对一切 δ-分离族成立)。两个构型给出下界——单点全 1 系数迫使 `C ≥ N`;`⌊(2δ)⁻¹⌋+1` 个点 `0, δ, 2δ, …` 配单点支撑系数迫使 `C ≥ ⌊(2δ)⁻¹⌋+1`。合起来 `le_of_admissibleConstant : max N (2δ)⁻¹ ≤ C δ N`。所以常数的两项都不可去,唯一还开着的就是那个对数因子。
- 大值估计的天花板(`HalaszMontgomery.lean`):`exists_sharp_rowSum` 给出正交构型,使不等式在 `Δ = 1` 时取等;`largeValues_constant_ge_one` 由此证明任何普适常数 `c ≥ 1`。也就是说 `R ≤ Δ‖a‖²/V²` 的常数已经最优,想改进大值计数就必须用到 Gram 行和之外的信息(这正是 Guth–Maynard 那类工作在做的事)。

## 第 4 步:仍未完成

组装出 `N(σ,T) ≪ T^{3(1−σ)/(2−σ)+ε}` 需要两块本仓库还没有的东西:把 mollifier 恒等式带进临界带的显式误差项,以及把积分型均值定理转成离散分离点上的 Gram 行和界。这两点都在相应的 `open_boundary` 字段里写明,没有作任何未经证明的声称。

## 仓库簿记

按仓库自己的约定做了登记:README 模块表新增三行;`docs/goal/task-board.yaml` 新增 `M2-LARGE-SIEVE`、`M2-LARGE-VALUES`、`M2-ZERO-DETECTION` 三行(状态 DONE_WEAK,含 exit_criteria 与 open_boundary);`docs/goal/evidence/` 新增三份证据说明;所有主要命题在 `scripts/revalidation.lean` 中被完整写出并钉住;`scripts/audit.sh` 新增 19 项 `#print axioms` 检查;`docs/current-goal-state.md` 已重新生成。完整 `lake build` 成功(9155 个任务),`scripts/audit.sh` 输出 `OK`。所有改动已提交并推送。

# Summary of changes for run 86d92e93-19c3-430b-8fc5-d05582c13fbc
## What I did

**1. Restored a working build.** The project's dependency set was inconsistent with its own pin (Lean v4.33.0 with the Mathlib revision named in `lakefile.toml`). I refetched and re-resolved the dependencies, regenerated `lake-manifest.json`, and confirmed a full `lake build` of the whole repository (9152 targets, no errors), including the vendored `Zeta23` library.

**2. Finished the one unfinished module.** `RiemannHypothesis/LindelofFromRH.lean` was a skeleton with 13 `sorry`s and was not imported anywhere. It is now fully proved and wired into the library root. It establishes Littlewood's theorem away from the critical line — the Riemann hypothesis implies the Lindelöf growth bound at every fixed distance from the line:

- `norm_riemannZeta_le_exp_of_zetaStripForm` — under the Riemann hypothesis, for `1/2 + δ ≤ re s ≤ 5/2` and `im s ≥ 100`, `‖ζ(s)‖ ≤ 3 exp(4 (60 log(im s)/δ)^λ)` with `λ = log(5 − 2δ)/log(5 − δ) < 1`.
- `exists_bound_riemannZeta_of_zetaStripForm` — for every `δ ∈ (0, 1/2)` and `ε > 0` there are `C, T₀ > 0` with `‖ζ(s)‖ ≤ C (im s)^ε` whenever `re s ≥ 1/2 + δ` and `im s ≥ T₀`.
- `exists_bound_riemannZeta_abs_im_of_zetaStripForm` — the two-sided form, with `|im s|`, which I added using the conjugation symmetry.

The proof takes the holomorphic logarithm of `(s − 1) ζ(s)` supplied by the hypothesis on `re s > 1/2`, normalizes it at the centre `3 + i t`, bounds its real part on two discs (`O(1)` on radius 1, `≤ 6 log t` on radius 5/2), converts both into modulus bounds by Borel–Carathéodory, and interpolates with the repository's Hadamard three-circles theorem. One skeleton lemma (`mem_halfPlane_of_mem_ball`) was stated with a hypothesis (`4 ≤ t`) under which it is false; I strengthened it to `6 ≤ t`, which every use satisfies, and noted this in its docstring.

**3. Kept the repository's own gates green.** `./scripts/audit.sh` ends in `OK`: everything builds; the only `sorry`s are the three intentional ones in `Challenge.lean`; the new theorems' `#print axioms` (now checked by the audit script) report exactly `propext, Classical.choice, Quot.sound`; the three new statements are pinned in `scripts/revalidation.lean`; the conditional-theorem manifest was regenerated, since all three assume the (unproved) Riemann hypothesis; and the task board validates with a new row `M2-LINDELOF-FROM-RH` plus an evidence note in `docs/goal/evidence/`. The `README.md` module table and narrative, and the `ThreeCircles.lean` docstring, were updated accordingly.

**Scope, stated plainly.** Nothing here claims the Riemann hypothesis, and nothing here proves the Lindelöf hypothesis: the critical line itself is not covered, because the constants degenerate as `δ → 0`. All three new theorems are explicitly conditional on the hypothesis and are recorded as such.

All work is committed and pushed.

# Summary of changes for run 1a09038b-ddec-4a39-93b4-66bed90640f1
项目已在 **Lean v4.33.0**（原始配置）下完成并全部通过检查。

关于「为什么 cancel」：此前的工作曾把项目降级到较旧的 Lean/Mathlib 版本，而您希望的是在原本的 v4.33.0 上把项目做完。本轮就是按这个目标把项目恢复并修完的。

本轮完成的事情：
- `lean-toolchain` 与 `vendor/zeta23/lean-toolchain` 均为 `leanprover/lean4:v4.33.0`；`lakefile.toml`（以及 vendored 的 `vendor/zeta23/lakefile.toml`）以 git 依赖方式固定 Mathlib 修订 `db584cd6…`，`lake-manifest.json` 一致。
- 修完了升级带来的最后几处源代码不兼容：
  - `RiemannHypothesis/ZeroGaps.lean`：区间求和拆分处的类型推断卡住，改为显式给出被求和函数并用 `simp only [Finset.range_eq_Ico]` 统一改写。
  - `RiemannHypothesis/WeilTestFunctions.lean`：适配 `Real.fourier_mul_convolution_eq` 的新签名，并去掉 `testTransform_weilSquare` 中不再需要的连续性假设（调用处与 `scripts/revalidation.lean` 中的语句锚点同步更新）。
  - `RiemannHypothesis/LiouvilleFunction.lean`：新版 Mathlib 已自带 `ArithmeticFunction.liouville`，本地重复定义会与之冲突（导致根模块 import 失败）。现改为直接使用 Mathlib 的版本，文件保留为薄封装并附带说明，下游 `LiouvilleCriterion.lean`、`LiouvilleSums.lean` 不受影响。
  - `vendor/zeta23/.../Tactic/AdditiveCombination.lean`：去掉重复命名空间导致的告警（重命名 tactic 语法节点）。
- 验证结果：
  - `lake build` 全量构建成功（9144 个目标，0 错误）。
  - `bash scripts/audit.sh` 以 `OK` 结束：构建通过；除 `Challenge.lean` 中三处有意保留的 `sorry` 外全仓库无 `sorry`；被比较定理的 `#print axioms` 只依赖 `propext, Classical.choice, Quot.sound`；无 `Float`；已关闭任务的结论在 `scripts/revalidation.lean` 中均有语句锚点；条件/无条件边界一致；任务板 108 项全部校验通过。
- 所有改动已提交并推送。

剩余的仅是若干非致命的 Mathlib 弃用提示（如 `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`），不影响构建与审计结果。

# Summary of changes for run 16118861-7299-4408-bf55-dee2c85468c4
## What I did

**1. Restored the build.** The repository as delivered did not compile against the pinned Mathlib. I fixed the packaging (a missing manifest entry for the vendored `Zeta23` path package, and the toolchain pin) and then worked through the many small incompatibilities that the pinned Mathlib introduced, across roughly two dozen files in `RiemannHypothesis/` and `vendor/zeta23/` — renamed or removed lemmas, ambiguous names needing qualification, changed tactic behaviour, and goals needing an explicit beta-reduction step. `lake build` now completes successfully for the whole project (8464 targets), and the repository's own end-to-end gate `scripts/audit.sh` prints `OK`.

**2. Added new mathematics: van der Corput's second-derivative test for exponential sums**, in the new module `RiemannHypothesis/VanDerCorputSums.lean`. This closes a gap that the existing task board explicitly recorded as open: the Kusmin–Landau inequality already in the repository assumes the phase derivative stays trapped between two consecutive integers over the whole range, which fails as soon as the derivative varies appreciably. The new module removes that assumption. Writing `e(θ) = exp(2πiθ)`:

- `norm_sum_e2pi_le_of_grow` — if `f'` grows at speed at least `r > 0` on `[a, a+L]`, then `‖∑_{j<L} e(f(a+j))‖ ≤ 2(V+2)((1+2/λ) + (2λ/r+1))`, with `V = f'(a+L) − f'(a)` and `λ > 0` free.
- `norm_sum_e2pi_le_of_grow_sqrt` — the balanced choice `λ = √r/2`, giving `2(V+2)(2 + 5/√r)`.
- `norm_sum_e2pi_le_of_deriv_two` — the second-derivative test proper: `0 < r ≤ f'' ≤ R` with `r ≤ 1` gives `‖∑_{j<L} e(f(a+j))‖ ≤ 2(R·L + 2)(2 + 5/√r)`, which for `R` comparable to `r` is the classical `≪ L√r + 1/√r`.
- `norm_sum_e2pi_le_of_deriv_two_neg` — the same bound for a decreasing derivative, `−R ≤ f'' ≤ −r`.
- `norm_sum_e2pi_logPhase_le` — the worked instance for the phase of ζ, `f(x) = −(t/2π) log x`, on a dyadic block `[N, 2N)`.

The proof classifies each index by the integer nearest to `f'` there: monotonicity makes every fibre a contiguous block, Kusmin–Landau bounds the blocks where `f'` is far from every integer, the blocks near an integer are short (because `f'` moves at speed at least `r`) and are counted trivially, and there are at most `2(V+2)` blocks.

The module contains no `sorry`, and all five public statements depend on exactly `propext`, `Classical.choice`, `Quot.sound`.

**3. Integrated it into the repository's own bookkeeping**, following the existing conventions: import in `RiemannHypothesis.lean`, a README module-table entry, a new task-board row `M1-VDC-SECOND-DERIVATIVE` with its exit criteria and an explicit open-boundary statement, an evidence file `docs/goal/evidence/2026-08-27-m1-vdc-second-derivative.md` including an adversarial-revalidation section, machine-checked statement pins in `scripts/revalidation.lean` (so a later weakening of any of the five theorems breaks the build), and `#print axioms` checks in `scripts/audit.sh`. The board validates (108 tasks) and `docs/current-goal-state.md` was regenerated.

## Honest scope

The Riemann hypothesis itself remains unproved, here and everywhere. `Challenge.lean` still carries its three intentional `sorry`s (they are the challenge template; the corresponding equivalences are proved in the library and bridged in `Solution.lean`), and there is no other `sorry` in the project. The new module draws no consequence for ζ: `norm_sum_e2pi_logPhase_le` bounds a single dyadic block and is not summed over blocks, so no subconvexity bound, approximate functional equation, or density estimate follows from it. The constants are not optimized.


# Summary of changes for run 879d60fe-cfc9-4237-81a7-0c22327d2383
Continued the Riemann-hypothesis formalization project. Everything below builds inside a full `lake build`, passes `bash scripts/audit.sh` (exit 0), and uses only the standard axioms `propext, Classical.choice, Quot.sound`. No `sorry` remains anywhere in the library; the only `sorry`s in the repository are the three in `Challenge.lean`, which the project's own conventions require to be left open there (their proofs are supplied in `Solution.lean`).

**1. Completed the outstanding bookkeeping for the n-th zero ordinate.** The pins in `scripts/revalidation.lean`, the axiom checks in `scripts/audit.sh`, the evidence note `docs/goal/evidence/2026-08-25-m2-zero-ordinate.md` and the task-board row `M2-ZERO-ORDINATE` for `RiemannHypothesis/ZeroOrdinate.lean` are now verified by a full audit run and committed.

**2. Closed the Littlewood/Backlund gap on the task board.** Two modules in the repository — `RiemannHypothesis/BacklundZeta.lean` (`S(t) = O(log t)` in the form needed for Littlewood's lemma) and `RiemannHypothesis/ZetaDensityLittlewood.lean` (Littlewood's lemma for ζ with every term bounded, and the resulting density bound `N(σ; T₁, T₂) = O(T₂)` for fixed σ > 1/2) — were proved but had no task-board row. I added the row `M1-BACKLUND-ARGUMENT` with a full evidence and adversarial-revalidation note (`docs/goal/evidence/2026-08-25-m1-backlund-argument.md`), and, since the horizontal argument terms that `M1-LITTLEWOOD-BOUNDS` had left explicit are exactly what those modules bound, moved `M1-LITTLEWOOD-BOUNDS` from a partially-open state to fully closed with an empty open boundary. The dependent row `M1-ALMOST-ALL-STRIP` was updated to record that both available routes now give `O(T)` and that the remaining gap is Carlson's density theorem.

**3. New mathematics: `RiemannHypothesis/ZeroGaps.lean`.** Writing γ_n for the ordinate of the n-th zero of ζ in the upper half plane (counted with multiplicity) and `zeroGap n = γ_{n+1} − γ_n`, this new module proves:
- the ordinates increase and the gaps telescope, `∑_{n<N} zeroGap n = γ_N` (with γ_0 = 0);
- `γ_n / n → 0`, hence **the average gap tends to 0**;
- for every ε > 0, infinitely many gaps are smaller than ε;
- **`liminf (γ_{n+1} − γ_n) log γ_n ≤ 2π`** and the matching **`limsup (γ_{n+1} − γ_n) log γ_n ≥ 2π`**: for every ε > 0 there are infinitely many n with the normalized gap below 2π + ε, and infinitely many with it above 2π − ε — so the normalized gaps are pinned on both sides of the value 2π predicted by the counting asymptotic;
- along the way, `log γ_{n+1} / log γ_n → 1`.

The module is imported by `RiemannHypothesis.lean`, its statements are pinned verbatim in `scripts/revalidation.lean`, its axioms are checked in `scripts/audit.sh`, and it has an evidence note with an adversarial-revalidation section (`docs/goal/evidence/2026-08-25-m2-zero-gaps.md`) and a task-board row `M2-ZERO-GAPS`. The board validator reports 95 tasks validating and `docs/current-goal-state.md` was regenerated.

**Scope, stated honestly.** None of this asserts the Riemann hypothesis. The gap results are consequences of the Riemann–von Mangoldt counting asymptotic; no strict improvement over `liminf ≤ 2π ≤ limsup` is claimed, zeroes are counted with multiplicity (so simplicity of the zeroes is not claimed), and the density bound reached along the Littlewood route is of Bohr–Landau strength `O(T)`, not Carlson's stronger estimate. The remaining open rows on the board (log-free convexity, Carlson's density theorem, mollified mean squares, and the M3 research rows) are research-grade and remain open.


# Summary of changes for run 3413f5e0-bce7-4fdd-ae19-22f84da781a0
Continued the formalization work and closed the outstanding analytic gap in the rectangle/argument-principle line of the project.

**New mathematics proved (no `sorry`, axioms exactly `propext`, `Classical.choice`, `Quot.sound`):**

- `RiemannHypothesis/ArgumentSegment.lean` — strengthened `exists_continuousOn_arg` so that *every* increment `θ v − θ u` of the continuous branch of the argument (built by integrating `g′/g`, with no branch cut chosen) is the imaginary part of `∫ᵤᵛ g′/g`, and added `exists_continuousOn_arg_horizontal`, the version for a horizontal side of a rectangle.
- `RiemannHypothesis/Littlewood.lean` (new module) — the Fubini step `integral_integral_re_logDeriv_eq_integral_log_norm_of_border` (the double integral of `re(f′/f)` across a rectangle may be computed in either order even though the integrand blows up at the zeroes inside), and **Littlewood's lemma** `littlewood_lemma`: for `f` analytic on a neighbourhood of a closed rectangle and nonvanishing on its border, `2π ∑_ρ ord_ρ(f)(re ρ − z.re)` equals the integral of `log‖f‖` over the left side minus the right side, plus the two horizontal argument terms and the right-hand vertical argument term. `littlewood_lemma_arg` states the same with the horizontal terms written as increments of genuine continuous arguments of `f`.
- `RiemannHypothesis/ZetaLittlewood.lean` (new module) — the specialization to `ζ`: `zeta_littlewood_lemma`, `zeta_littlewood_lemma_arg`, and `zeta_littlewood_lemma_nontrivialZeros`, where the sum is over `Rectangle z w ∩ nontrivialZeroSet`, i.e. the nontrivial zeroes of `ζ` inside the rectangle. These are identities, not bounds; no zero-density estimate follows without bounds on `log‖ζ‖` on the two vertical sides, and nothing here bears on the Riemann hypothesis itself, which remains open.

**Repository hygiene, per the project's own conventions:**

- Both new modules are exported from `RiemannHypothesis.lean`; the full `lake build` succeeds and `scripts/audit.sh` exits 0 (build, no `sorry` outside `Challenge.lean`, axiom checks, no `Float`, pinned claims, conditional-theorem manifest, task-board validation).
- All new results are pinned in full in `scripts/revalidation.lean` and their axioms checked in `scripts/audit.sh`.
- `docs/goal/task-board.yaml`: the row `M1-RECTANGLE-ARGUMENT-PRINCIPLE` moves from `DONE_WEAK` to `DONE_STRONG` — its open boundary ("Littlewood's lemma proper: the argument half and the Fubini step") is now empty — with new exit criteria and gates; `M1-ZETA-RECTANGLE-COUNT` records the `ζ` specialization. New evidence file `docs/goal/evidence/2026-08-25-m1-littlewood.md`, an addendum to the existing `ζ` evidence file, regenerated `docs/current-goal-state.md`, and updated `README.md` (file table, highlights, and a new section on the argument half and Littlewood's lemma).
- Everything is committed and pushed.


# Summary of changes for run ee311c62-e270-4403-8d3b-65c4e71b517b
I picked up the in-flight work on the mean square of ζ inside the critical strip and finished it, then extended it with two consequences and recorded everything under the repository's own conventions.

**New module `RiemannHypothesis/StripMeanSquare.lean` (no `sorry`, now imported by `RiemannHypothesis.lean`).** Its main result is

`exists_integral_normSq_riemannZeta_le` : for fixed σ with 2/3 < σ < 1 there is a constant C > 0 with `∫₀ᵀ ‖ζ(σ + i t)‖² dt ≤ C·T` for every T ≥ 1.

This is the first mean-square bound of the repository *inside* the critical strip; the pre-existing `MeanSquare.lean` covers only the half-plane σ > 1 of absolute convergence. The route, all proved in the file:
- elementary sums `sum_Icc_rpow_neg_le` and `sum_rpow_neg_div_abs_sub_le`;
- `offDiagSum_one_le`, bounding the off-diagonal term of the mean value theorem for the truncated zeta sum by `O(N^(2−2σ)(1 + log N))`;
- `integral_normSq_dirichletPoly_one_le`, the mean square of the truncated zeta sum;
- `norm_riemannZeta_sub_dirichletPoly_le`, the Euler–Maclaurin bound for ζ minus that sum;
- `integral_inv_sq_shift_le` for the pole term, and the choice `N = ⌈T^(1/σ)⌉₊` balancing the two errors.

Two consequences were added on top: `exists_integral_norm_riemannZeta_le` (the first moment `∫₀ᵀ ‖ζ(σ + i t)‖ dt = O(T)`) and `exists_volume_norm_riemannZeta_ge_le` (a large values estimate: the set of t ∈ (0, T] with `‖ζ(σ + i t)‖ ≥ V` has measure at most `C·T/V²`), the form in which a mean square feeds zero-density arguments.

Scope, stated in the module docstring, the evidence file and the task board: the exponent 2/3 is exactly the balance point of the zeroth-order Euler–Maclaurin expansion; the classical Bohr–Landau range σ > 1/2 needs the higher-order expansion, which is not formalized here. No asymptotic is claimed and nothing about the location of the zeroes is deduced.

**Verification and bookkeeping.** `lake build` succeeds for the whole project; the only `sorry`s remain in `Challenge.lean`, where the repository intends them. `#print axioms` for each new result reports exactly `propext, Classical.choice, Quot.sound`. The full gate `scripts/audit.sh` passes (exit 0), including the new axiom checks, the statement pins added to `scripts/revalidation.lean`, and board validation. I also added the task-board row `M1-STRIP-MEAN-SQUARE` (status DONE_WEAK, with its open boundary recorded), the evidence file `docs/goal/evidence/2026-08-24-m1-strip-mean-square.md` with an adversarial-revalidation section, and a README entry for the new module. An incidental name clash with an existing lemma in `MeanFluctuation.lean` was resolved by splitting out `continuous_riemannZeta_line_of_lt_one` / `continuous_normSq_riemannZeta_line_of_lt_one`.

All work is committed and pushed.

# Summary of changes for run 7141f00e-5604-4cdd-87a9-94fed35376ea
明白，抱歉之前的偏题。先说结论：**λ-演算的内容早已从仓库中彻底删除，本次会话也再次核查确认** —— `LambdaCalculus/` 目录、`LambdaCalculus.lean`、lakefile 里的构建目标、README 里的相关段落全部不存在了。现在仓库里唯一还提到它的地方是历史记录文件 `ARISTOTLE_SUMMARY.md`（那是上一轮留下的说明文档，按要求不予改动）。除此之外全仓库搜索 "lambda" 只剩黎曼假设本身的记号：von Mangoldt 的 Λ(n)、完备化 zeta 的 Λ(s)、de Bruijn–Newman 常数 Λ。整个项目只做黎曼假设这一个主题。

本次会话在黎曼假设方向上做了两件事，全部编译通过、无 `sorry`、公理恰为 `propext, Classical.choice, Quot.sound`：

1. **修正此前有误导性的文档。** `RiemannHypothesis/EightyPercentRoute.lean` 中把未证的 `SpeiserTransfer` 说成"Levinson–Montgomery 形式的 Speiser 定理"，这是不对的：Levinson–Montgomery 计的是 ζ′ 的零点而非 ξ′ 的零点，并不能给出这个 `Prop`；而且按重数计时该假设等价于在线计数的反向比较，本身就已经蕴含 86.864% 的零点在临界线上，比它想达到的 80% 目标更强。相应的更正写进了模块文档、`README.md`（新增一节说明 Rolle 与该假设的真实代价）、任务板与证据文件，并把新结果钉进了 `scripts/revalidation.lean` 与 `scripts/audit.sh` 的公理检查。

2. **证明了 Speiser 定理容易方向的定量形式**（新文件 `RiemannHypothesis/SpeiserRH.lean`）：
   - `windowCountOffLineMult_eq_zero_of_zetaStripForm`：假设成立时窗口内 ζ 没有离线零点；
   - `speiserOffLineTransfer_of_zetaStripForm`：黎曼假设蕴含那条"转移"假设（因此它夹在假设与 86.864% 之间，不是可以随意假定的技术输入）；
   - `xiDerivWindowCountOffLineMult_le_log_of_zetaStripForm`：**若 ζ 的全部非平凡零点都在临界线上，则在每个二进窗口 (T,2T] 内 ξ′ 按重数计至多有 O(log T) 个离线零点**。证明只用临界线上 Hardy 函数 Ξ 的 Rolle 定理加两个 Riemann–von Mangoldt 公式；比 Speiser 的"完全没有离线零点"弱，弱的正是那两个公式的 O(log T) 误差项；
   - `not_zetaStripForm_of_xiDeriv_offLine_gt`：其逆否形式，是一条证伪判据。

验证情况：`bash scripts/audit.sh` 全绿（整库 `lake build` 成功、库内无 `sorry`、公理检查通过、任务板 82 行校验通过），文档 `docs/current-goal-state.md` 已重新生成，所有改动已提交并推送。

需要说明的边界：临界线上零点比例的**无条件**结果仍是 2/3（最优窗口下 0.6725…），本次工作没有推进这个数字；它澄清并封住了此前那条"通往 80%"路线中被高估的一环，并把其中真正能用实分析拿到的一半变成了定理。

# Summary of changes for run e258aa3e-dcc6-456f-b21a-8b7517581d7b
I followed the recommendation in your note and built the **Scott `D∞` line** end to end, in the self-contained `LambdaCalculus/` library of this repository. Everything compiles with no `sorry`, and every result depends only on `propext`, `Classical.choice`, `Quot.sound`. The Riemann-hypothesis material is untouched and the full project still builds (9099 jobs, clean).

Since the λ-calculus assets referred to in your note (`SimpleTypes.lean`, `Combinators.lean`, `ComplexityClasses`, `EvalGK/Leftmost`) are not present in this repository, the untyped λ-calculus side had to be built here first; that part was already in place from earlier work in this session and is now completed by `D∞`.

**What is new**

* `LambdaCalculus/Tower.lean` — the tower `D 0 = Prop`, `D (n+1) = [D n → D n]` of ω-CPOs, with a single cast-free recursion defining the canonical continuous maps `lev n m : D n →𝒄 D m`, and the full embedding–projection calculus: `lev_self`, `p_e`, `e_p_le`, `lev_emb_cancel`, `lev_proj_cancel`, `emb_proj_le`, `lev_comp_le`.
* `LambdaCalculus/Dinf.lean` — **Scott's `D∞`**:
  * `Dinf` as the inverse limit `{x : Π n, D n // ∀ n, p n (x (n+1)) = x n}`, with its ω-CPO structure, projections `pInf n` and embeddings `eInf n`;
  * `ωSup_retract` : every point is the supremum of its finite approximations (`D∞` is the colimit of its levels);
  * `Phi : D∞ →𝒄 [D∞ → D∞]` and `Psi : [D∞ → D∞] →𝒄 D∞`, with **both** halves of the isomorphism proved (`Phi_Psi`, `Psi_Phi`), packaged as an order isomorphism `orderIsoHom : Dinf ≃o (Dinf →𝒄 Dinf)`;
  * hence `D∞` is an **extensional reflexive object** in the category of ω-CPOs, is nontrivial, and is therefore a λ-model: soundness of β (`denote_reds_Dinf`, `denote_conv_Dinf`), the semantic form of confluence (`denote_of_common_reduct`), validity of η (`denote_eta_Dinf`), and a semantic proof that λβ is consistent (`consistency_of_lambda_beta_Dinf`).
* `LambdaCalculus/Model.lean` — added `abs_ap` and `denote_eta` (validity of the η-rule in any extensional reflexive ω-CPO), and Curry's fixed-point combinator `Y` with `ap_denote_Y` / `exists_ap_fixed_point`.
* `LambdaCalculus/CPO.lean` — small additions on suprema of chains of continuous maps.
* Documentation: a new `LambdaCalculus/README.md` describing the library and its main statements, plus a short pointer from the top-level `README.md`.

**Not done (and why):** the second direction you listed, Curry–Howard–Lambek (STLC ⟺ CCC), would require the simply-typed calculus and its syntactic category from scratch; I did not start it rather than leave a partially proved file behind. Your note's own judgement was that `D∞` is the higher-value target, and that is what is now fully machine-checked.


# Summary of changes for run 20de0ab3-52e6-4441-a83b-b5401032c70d
## Your question about `lake-manifest.json`

**Yes — the lock file was the real problem, and it is now fixed.**

The delivered `lake-manifest.json` had been rewritten so that every dependency was a bare `path` entry pointing into `.lake/packages/`, and the contents of that directory were a **v4.28.0-era Mathlib** (its own `lean-toolchain` read `v4.28.0`). On top of that, the `Zeta23` entry was missing from the manifest altogether. The symptoms were `dependency 'Zeta23' not in manifest` and then `bad import 'Mathlib.Analysis.Complex.BranchLogRoot'` — that module (and `Mathlib.NumberTheory.ArithmeticFunction.Liouville`, needed by `Criteria.lean` and `LiouvilleCriterion.lean`) simply does not exist in the v4.28.0 Mathlib.

Note that the project itself was never on v4.28.0: both `lean-toolchain` files (root and `vendor/zeta23/`) pin `leanprover/lean4:v4.33.0`, and `lakefile.toml` pins Mathlib at `db584cd6d46c92f209a44c0f1c829460d327499d`, which is a v4.33.0 Mathlib. Only the lock file was stale.

The manifest has been regenerated so that it agrees with the pins: Mathlib as a git dependency at `db584cd6…`, and `Zeta23` restored as a `path` dependency at `vendor/zeta23`. `lake build` now completes cleanly (9091 jobs), and `bash scripts/audit.sh` ends `OK: 80 tasks validate` / `OK`. The build section of the README now tells you to run `lake exe cache get` before `lake build`.

## Other work in this session

**New mathematics — `RiemannHypothesis/SpeiserMultiple.lean`** (unconditional, `sorry`-free, axioms exactly `propext`, `Classical.choice`, `Quot.sound`):

- `xiDerivMultiplicity_add_one`: at a nontrivial zero, `m_{ξ′}(ρ) + 1 = m_ζ(ρ)`.
- `xiDerivFn_eq_zero_of_multiple` / `xiDerivFn_ne_zero_of_simple`: a *multiple* zero of ζ is a zero of ξ′ at the same point, and a *simple* one is not — so this local argument reaches exactly the multiple zeroes.
- `windowZerosOffLineMultiple_subset` and `ncard_windowZerosOffLineMultiple_le_bad`: the counting form.
- `ncard_windowZerosOffLineMultiple_le_windowCount`: unconditionally, for every ε > 0 and all large T, at most `(0.13136 + ε)·N(T,2T)` of the zeroes of ζ in the dyadic window are both multiple and off the critical line.
- `windowMultipleOffLineExcess` and `windowMultipleOffLineExcess_le_bad` / `_le_windowCount`: the same two bounds in multiplicity-weighted form, each multiple off-line zero counted `m_ζ(ρ) − 1` times.
- `RiemannHypothesis/EightyPercentRoute.lean` gained the unconditional `xiDerivWindowCountBad_le` and was refactored to use it.

**To be plain about the limits:** `SpeiserTransfer` itself is still **not** proved. Its content is the transfer for the *simple* off-line zeroes, which needs the argument principle for `ξ′/ξ` (not present in this repository or in Mathlib), and `xiDerivFn_ne_zero_of_simple` shows no local argument can supply it. None of the conditional 84 % / 70 % results became unconditional.

**Housekeeping:** removed a duplicate declaration of `analyticOrderAt_xiFn_eq` (the new file now imports and reuses the one in `ZeroMultiplicityBound.lean`); added the new theorems to the axiom checks in `scripts/audit.sh` and to the machine-checked claim pins in `scripts/revalidation.lean`; added task-board row `M1-SPEISER-MULTIPLE` with an evidence and adversarial-revalidation note at `docs/goal/evidence/2026-08-23-m1-speiser-multiple.md`.

**README:** the stale zero-free-region text was replaced (de la Vallée Poussin row plus a section on the classical exponent one, covering `ZeroFreeClassical.lean` / `ZeroLocationClassical.lean`); the fifteen previously unlisted source files were added to the layout table; a "Five routes to the hypothesis" section and a section on the unconditional part of Speiser's transfer were added; the opening was broadened and the attribution block moved to a Provenance section at the end. The optional split of the README into a separate `docs/mathematics.md` was not done — it is a single navigable document with many internal links, and splitting it risks breaking them.

The only `sorry`s remaining anywhere in the project are the three intentional ones in `Challenge.lean`, which are discharged in `Solution.lean`.


# Summary of changes for run a3286860-a596-4967-af0a-a6bf423b9e7a
Continued the Riemann-hypothesis formalization; everything below is committed and pushed, the whole project builds, and `bash scripts/audit.sh` ends with `OK` (68 task-board rows validating).

**Repair first.** As delivered the project again did not resolve its dependencies — the lock file `lake-manifest.json` had lost the vendored `Zeta23` entry and pointed at a different Mathlib from the one the sources are written against, so `lake build` failed immediately. The lock file is regenerated to match `lakefile.toml` (Mathlib at the pinned revision, `Zeta23` from `vendor/zeta23`); after that the full build succeeds.

**New mathematics — two modules, both `sorry`-free, every result depending on exactly `propext`, `Classical.choice`, `Quot.sound`.**

1. `RiemannHypothesis/OffLineQuadruple.lean` — off-line zeroes come in quadruples. Composing the conjugation and functional-equation symmetries gives the reflection `criticalReflect s = 1 − conj s` in the critical line, which fixes the imaginary part and reflects the real part in `1/2`. Proved: the zeroes of height at most `T` are stable under all three symmetries; an off-line zero `ρ` has four pairwise distinct off-line companions `ρ, conj ρ, 1 − ρ, 1 − conj ρ` of the same height (`offLineQuadruple_distinct`); `N_off(T) = 4 · #{zeroes of height ≤ T with re < 1/2 and im > 0}`, hence `4 ∣ N_off(T)`; and if one zero of height at most `T` lies off the critical line then at least four do (`four_le_ncard_offLineNontrivialZeros`).

2. `RiemannHypothesis/ZeroMultiplicitySymmetry.lean` — the symmetries preserve multiplicities, which removes the "distinct zeroes only" caveat that the previous counting results carried. Proved: the general fact that the vanishing order of `z ↦ conj (f (conj z))` at `conj z₀` equals that of `f` at `z₀` for arbitrary `f`; that inside the critical strip `ζ` and the completed zeta function vanish to the same order (they differ by the nonvanishing analytic factor `Γ_ℝ`); hence that the multiplicity of a zero is unchanged by `s ↦ conj s`, by `s ↦ 1 − s` and by reflection in the critical line; and, for the counting functions **with multiplicity**, that `N(T)` is even and the off-line count is four times the upper-left count, hence divisible by four.

Scope, stated plainly: nothing here decides whether any off-line zero exists — the Riemann hypothesis is neither proved nor disproved, there is still no term of the conjecture's type anywhere in the repository, and the audit script checks that none appears. The statements give no information about the location of the zeroes and no rate.

**README.** Added a `Highlights` section immediately after the introduction: a table of the strongest results (the equivalent formulations; more than two thirds of the zeroes simple and on the critical line; 80 % of the distinct zeroes simple; 80 % of the zeroes distinct; at most a third off the line; the unconditional de Bruijn–Newman bridge `H₀(z) = Ξ(z/2)/8`; the prime number theorem; the explicit zero-free region; the zero-counting results; Hardy's theorem quantified; and the new quadruple/multiplicity results), each linked to the module that proves it, with attribution where a result is restated from the vendored `Zeta23` library. It is followed by an explicit "what is deliberately not claimed" paragraph and a description of what the audit script checks. Also added module-table rows and dedicated sections for the two new modules, and corrected the zero-free-region description to the exponent actually proved.

**Bookkeeping**, following the repository's conventions: two new task-board rows (`M2-OFF-LINE-QUADRUPLE`, `M2-MULTIPLICITY-SYMMETRY`, both `DONE_STRONG`) with dated evidence files including adversarial-revalidation sections; full statement pins (including `rfl`-pins of the new definitions) in `scripts/revalidation.lean`; `#print axioms` checks and imports added to `scripts/audit.sh`; the modules imported from `RiemannHypothesis.lean`; and `docs/current-goal-state.md` regenerated.

# Summary of changes for run 80dcc786-e2fc-4df3-ad5a-7616fa8a3371
Short answer: it depends which "80 %" you mean — one of them is finished, the other is not.

**Finished and machine-checked (no `sorry`, axioms exactly `propext`, `Classical.choice`, `Quot.sound`):**
- **At least 80 % of the *distinct* nontrivial zeros of ζ are simple** — `eighty_percent_simple_among_distinct` and its cumulative form, plus the ε-free ratio version `four_fifths_le_liminf_windowCountSimple_div_windowCountDistinct` (`RiemannHypothesis/EightyPercentSimple.lean`). The denominator is shown to tend to infinity, so the quotient really is a proportion.
- **At least 80 % of the nontrivial zeros of ζ are distinct** — `eighty_percent_distinct` (+ cumulative), from the 5/6 theorem (`RiemannHypothesis/EightyPercent.lean`).
- **At least 80 % of the zeros of ξ′ are simple and on the critical line**, and at least 92 % of the distinct zeros of ξ′ are simple.
- **The 80 % simplicity statement for Dirichlet L-functions**, χ primitive mod q > 1.

**Not finished (and not claimed):** raising the proportion of zeros **on the critical line** to 80 %. What the project proves there is 2/3; the 80 % version is recorded as a statement only — the Prop `EightyPercentOnCriticalLine`, together with `one_fifth_off_critical_line_of_eightyPercent` showing what it would buy. That remains an open research problem, as does the Riemann hypothesis itself: there is still no term of the conjecture's type anywhere in the repository, and the audit script checks that none appears.

**Overall project status, re-verified this session rather than taken on trust:** `bash scripts/audit.sh` ends with `OK` — full build, axiom check over ~196 declarations, statement pinning, and 66 task-board rows validating (51 `DONE_STRONG`, 2 `DONE_WEAK`, 13 still open: `M1-ALMOST-ALL-STRIP` plus twelve rows needing machinery that is not available, among them the prime number theorem, the mean-value/mollifier/density rows, and `M4-RH`). A repository-wide search for `sorry` finds only the three intentional ones in `Challenge.lean`, which are discharged in `Solution.lean`.

**One real fix made this session:** as delivered, the project no longer resolved its dependencies — the lock file (`lake-manifest.json`) had lost the vendored `Zeta23` entry and pointed at a Mathlib different from the one the sources are written against, so `lake build` failed immediately with `dependency 'Zeta23' not in manifest`. The lock file is now regenerated to match `lakefile.toml` (Mathlib at the pinned revision, `Zeta23` from `vendor/zeta23`), and after that the whole project builds and the audit passes. That change is committed and pushed; no Lean sources were modified.

# Summary of changes for run 3372ab5b-54e3-4263-b842-0a755a07a8a1
The Lean formalization is done, builds cleanly, and is committed and pushed. It lives in the new module `RiemannHypothesis/EightyPercentSimple.lean` (imported by `RiemannHypothesis.lean`), contains no `sorry`, and every result uses only the standard axioms `propext`, `Classical.choice`, `Quot.sound`. The repository's own gate, `scripts/audit.sh`, ends with `OK` (full build, no `sorry` outside `Challenge.lean`, axiom check over 200 declarations, statement pinning, task-board validation).

Formalized and proved (all unconditional, all about the zeros of ζ in an ordinate window, with `N` = zeros with multiplicity, `N_d` = distinct zeros, `Nˢ` = simple zeros):

- `two_mul_ncard_le_ncard_simple_add_finsum` — the general counting inequality: for a finite set of points with multiplicities ≥ 1, `2·#S ≤ #{simple} + ∑ multiplicities`; and its instance `two_mul_windowCountDistinct_le_add` : `2·N_d ≤ Nˢ + N`.
- `mtConstant_gt_three_quarters` : `3/4 < c₁*` for the Montgomery–Taylor constant `√2·tan(1/√2)/(1 + tan(1/√2)/√2)`, proved from `x − x³/6 < sin x` and Mathlib's Taylor bound for `cos` at `x = 1/√2`.
- `eighty_percent_simple_among_distinct` and `eighty_percent_simple_among_distinct_cumulative` : **at least 80 % of the distinct nontrivial zeros of ζ are simple**, `ε`-free — `0.8·N_d ≤ Nˢ` for all large `T`, on dyadic windows `(T, 2T]` and on `(0, T]`.
- `four_fifths_le_liminf_windowCountSimple_div_windowCountDistinct` : the same as a ratio, `4/5 ≤ liminf Nˢ(0,T)/N_d(0,T)`, together with `tendsto_windowCountDistinct_atTop` so the denominator is eventually positive and the quotient is a genuine proportion.
- `four_fifths_simple_among_distinct` (+ cumulative) : the `ε`-form `Nˢ/N_d ≥ 4/5 − ε` from the `5/6` distinctness theorem alone.
- `ninety_two_percent_simple_among_distinct_xiDeriv` (+ cumulative) : at least 92 % of the distinct zeros of `ξ′` are simple.
- `eighty_percent_simple_among_distinctL` : the 80 % statement for `L(·, χ)`, χ primitive modulo `q > 1`.

On the original wish to raise the proportion to 80 %: increasing the proportion of zeros *on the critical line* from `2/3` to `80 %` is an open research problem, and nothing in the project proves it. Rather than leave that implicit, the target is recorded as a statement only — `EightyPercentOnCriticalLine` (a `Prop`, in the style of the project's other known-but-unproved statements) — with `one_fifth_off_critical_line_of_eightyPercent` proving what it would give: at most a fifth of the zeros off the critical line.

Supporting work: the package manifest had lost the vendored dependency, so nothing compiled at the start of this session; that is repaired and a full build is verified. The new results are also pinned statement-by-statement in `scripts/revalidation.lean`, axiom-checked in `scripts/audit.sh`, and documented in `README.md`, the task board (`docs/goal/task-board.yaml`, 66 rows validate) and a new evidence note `docs/goal/evidence/2026-08-21-m1-simple-eighty.md`.

Scope, stated plainly: these are asymptotic statements with no effective threshold `T₀`; the denominator is the number of distinct zeros in the window; and none of them bears on the Riemann hypothesis itself.

# Summary of changes for run 191be37f-6acf-494c-81cf-63350cbc7390
Picked up the Riemann-hypothesis formalization where the previous run left off and brought it to a fully consistent, self-auditing state. Everything below builds and is committed and pushed.

**Repairs and bookkeeping completed**
- Fixed the statement-pinning file `scripts/revalidation.lean`, which no longer elaborated: the pin for the "80 % of the zeroes are distinct" result now matches the theorem's actual (stronger, ε-free) form. The file now elaborates cleanly.
- Extended `scripts/audit.sh` so its axiom check covers all the newer modules (`Zeta23Bridge`, `CriticalLine`, `CriticalLineOrdinates`, `OffLine`, `EightyPercent`, `PrimeNumberTheorem`, `ExplicitFormula`, `PartialProved`) — 190 declarations are now axiom-checked. Its textual `sorry` scan previously misfired on prose in the vendored sources; that directory is now excluded, with a comment explaining that the vendored code is covered by the axiom checks instead. `bash scripts/audit.sh` now ends with `OK`.
- Rewrote the affected parts of `README.md`: module-table rows and new sections for the two-thirds/five-sixths proportion results, Hardy's theorem, the ordinate results, the prime number theorem, Weil's explicit formula, and the new off-line bound; the "Provenance and status" section now states accurately what is and is not proved. Regenerated `docs/current-goal-state.md` and updated the task board (65 rows validate).

**New mathematics added (sorry-free, axioms exactly `propext`, `Classical.choice`, `Quot.sound`)**
- `RiemannHypothesis/OffLine.lean`: the two-thirds theorem read from the side the hypothesis is about. Defines the off-line counts `windowCountOffLine` and `offCriticalZeroCount`, proves the splitting identities `N_off + N₀* = N_d` and `N_off(T) + N₀(T) = N(T)`, and deduces `one_third_off_critical_line` (and its cumulative form) — `N_off ≤ (1/3 + ε)·N` for all large `T` — together with `limsup_offCriticalZeroCount_div_le_one_third`, i.e. `limsup N_off(T)/N(T) ≤ 1/3`.
- `RiemannHypothesis/CriticalLineOrdinates.lean`: added that the real zeroes of `Ξ` are unbounded below as well as above, in existence form and as `not_bddAbove_setOf_riemannXi_ofReal_eq_zero` / `not_bddBelow_setOf_riemannXi_ofReal_eq_zero`.
- Each new result is pinned in `scripts/revalidation.lean` (full statement, repository declaration as proof term), documented in a dated evidence file under `docs/goal/evidence/`, and recorded on the task board.

**Scope and honesty**
The Riemann hypothesis itself remains open and is not claimed anywhere: there is no proof term of the conjecture in the repository — it occurs only inside equivalences. The proportion results are `liminf`/`limsup` statements with no effective threshold, and several of them are restatements of the vendored library under `vendor/zeta23`, attributed in each module. The only remaining `sorry`s are the three intentional ones in `Challenge.lean`, which are the statements of record and are proved in `Solution.lean`.

Remaining open board rows (zero-density/Bohr–Landau, mean values, mollifiers, pair correlation, Weil positivity, numerical verification) are unchanged; they need machinery that is neither in Mathlib nor in the vendored sources.


# Summary of changes for run 9b63d9ab-dcd0-422d-9714-ee2754591221
## Short answers

**Did I finish?** The project as scoped is in a clean, fully verified state (`lake build` succeeds, `./scripts/audit.sh` prints `OK`, and the only `sorry`s in the repository are the three intentional ones in `Challenge.lean`, which are discharged in `Solution.lean`). But the task board still has open rows, so "finished" in the sense of "nothing left to do" is not the case — and it cannot be, because of the next answer.

**Did I try to finish the Riemann hypothesis itself?** No — and to be plain about it: **the Riemann hypothesis is not proved in this repository, and it remains an open problem.** There is deliberately no term of type `ZetaForm` anywhere in the project, and `scripts/audit.sh` checks that nothing sneaks one in. Everything in the repository is either an *equivalent reformulation* of RH, a *classical partial result*, or a *statement recorded without proof*. Claiming otherwise would be false.

What I did do this session is close the largest genuinely-reachable gap that the previous work had explicitly flagged as unproved.

## What was added this session

Two new modules, both `sorry`-free, with axioms exactly `propext`, `Classical.choice`, `Quot.sound`:

- `RiemannHypothesis/ThetaW.lean` — the theta series `ω(x) = ∑_{n≥1} e^{−πn²x}` and the profile `W(u) = e^u ω(e^{4u})`. Proves the theta functional equation in the form `W(−u) = W(u) + sinh u`, hence `W'(0) = −1/2`; justifies termwise double differentiation of the series; proves `Φ = (W'' − W)/8`, identifying the de Bruijn–Newman weight already defined in the repository; and establishes the decay estimates making the relevant cosine integrals absolutely convergent.
- `RiemannHypothesis/FourierXi.lean` — folds the Mellin integral of Mathlib's modified theta kernel from `(0,1]` onto `(1,∞)`, substitutes `x = e^{4u}`, and obtains **Riemann's integral representation** `Ξ(z) = 1/2 − (4z²+1)∫₀^∞ W(u)cos(2uz) du`. On the other side, integrating the exact derivative of `W'(u)cos(uz) + zW(u)sin(uz)` over `(0,∞)` leaves only the boundary term `−W'(0) = 1/2`. Combining gives, **unconditionally**:
  - `dbnH_zero_eq_riemannXi : H₀(z) = Ξ(z/2)/8`
  - `zeta_iff_dbnH_zero : ZetaForm ↔ ∀ z, H₀(z) = 0 → z.im = 0`

The second statement carries no hypotheses. Previously the repository only had a *conditional* bridge, `zeta_iff_dbnH_zero_of_eq`, which assumed `∀ z, H₀(z) = Ξ(z)`. That hypothesis is **false** — the correct normalisation halves the variable and divides by 8 — so the conditional theorem, though correctly proved, was vacuous. It has been left in place (user-provided content is not deleted) with a docstring recording the correction and pointing at the unconditional replacement; the same correction is noted in `scripts/revalidation.lean`.

Again: `zeta_iff_dbnH_zero` is an *equivalence between two open statements*. It makes the de Bruijn–Newman route to RH unconditional inside this repository; it does not prove RH.

## Bookkeeping

Both modules are imported from `RiemannHypothesis.lean`; a new board row `M2-H0-EQUALS-XI` (`DONE_STRONG`) was added with an evidence file at `docs/goal/evidence/2026-08-21-m2-h0-equals-xi.md` including the required adversarial-revalidation section; every new claim is pinned in `scripts/revalidation.lean`; axiom checks and imports were added to `scripts/audit.sh`; the README gained a module-table entry and a new "`H_0` really is `Ξ`" section; and `docs/current-goal-state.md` was regenerated. `bash scripts/audit.sh` prints `OK` (62 tasks validate). All work is committed and pushed.


# Summary of changes for run cfffface-e48e-4155-9b59-2f9442d31359
**Yes — the project is finished and green, and I added one more piece of proved mathematics this session.**

**State when I picked it up.** I re-verified everything rather than trusting the earlier notes: `lake build` succeeds for the whole project, `scripts/audit.sh` reports `OK`, and the only `sorry`s in the repository are the three intentional ones in `Challenge.lean` (the statement of record, proved in `Solution.lean`) — the repository's own convention. Nothing was broken or left half-done.

**New this session — `RiemannHypothesis/ZeroSymmetryCount.lean`** (no `sorry`; every theorem depends on exactly `propext`, `Classical.choice`, `Quot.sound`). It turns the symmetries already proved in `RiemannHypothesis/Symmetry.lean` into statements about the zero set itself and about the counting function `N(T) = #{ρ : ζ ρ = 0, 0 < re ρ < 1, |im ρ| ≤ T}`:
- `im_ne_zero_of_mem_nontrivialZeroSet` — no nontrivial zero is real (ζ does not vanish on `(0,1)`);
- `conj_mem_nontrivialZeroSet`, `one_sub_mem_nontrivialZeroSet` — the zero set is stable under `s ↦ conj s` and under `s ↦ 1 − s`;
- `conj_image_upperNontrivialZeroSet` — conjugation maps the upper half of the zero set bijectively onto the lower half;
- `infinite_upperNontrivialZeroSet`, `infinite_lowerNontrivialZeroSet` — each half-plane contains infinitely many nontrivial zeroes;
- `ncard_nontrivialZeros_eq_two_mul` — `N(T) = 2 · #{zeroes of height ≤ T with im > 0}`, and hence `even_ncard_nontrivialZeros` — **`N(T)` is even**.

Scope, stated plainly: zeroes are counted without multiplicity (with multiplicity the parity claim would additionally need the orders of vanishing at `ρ` and `conj ρ` to agree, which is not proved), the infinitude statements are qualitative with no rate, and nothing here concerns the real parts of the zeroes.

**Bookkeeping**, following the repository's existing conventions: new task-board row `M2-ZERO-SYMMETRY-COUNT` (`DONE_STRONG`), an evidence file `docs/goal/evidence/2026-08-21-m2-zero-symmetry-count.md` with an adversarial-revalidation section, full statement pins (including `rfl`-pins of the two new definitions) in `scripts/revalidation.lean`, `#print axioms` checks plus the import in `scripts/audit.sh`, a README module-table row and a new README section, the module added to `RiemannHypothesis.lean`, and `docs/current-goal-state.md` regenerated.

**Verification after the change:** `lake build` succeeds; `bash scripts/audit.sh` prints `OK` with 61 task-board rows validating; a repository-wide search for `sorry` finds only `Challenge.lean`.

**What is still open, honestly.** The Riemann hypothesis itself is not proved, and no term of the conjecture's type exists anywhere in the repository — the `M4-RH` row remains open, as do the prime number theorem, Hardy/Levinson/Conrey/Selberg, the explicit formula and the other rows the board marks as such. All work is committed and pushed.

# Summary of changes for run 2ad2812c-8694-45d6-ab74-12d4d1b331db
**Direct answer to your question: no — the Riemann hypothesis is not proved here, and this project does not claim it.** It is an open problem, and nowhere in the repository is there a proof term of the conjecture itself (`RiemannHypothesis.ZetaForm`). What the repository contains is the precise *statement* of the hypothesis, the equivalence of its standard formulations, and a body of classical, machine-checked results about the zeta function around it. The task board in `docs/goal/task-board.yaml` records the row for the conjecture itself (`M4-RH`) as still open, as do the rows for the prime number theorem, Hardy's theorem, the explicit formula, and the Levinson/Conrey/Selberg results — all of which need machinery that is neither in Mathlib nor in this repository.

**State of the project as returned to you: complete and green.**
- `lake build` succeeds for the whole project.
- `scripts/audit.sh` reports `OK`, with 60 task-board rows validating.
- The only `sorry`s in the repository are the three intentional ones in `Challenge.lean` (the statement of record; they are proved in `Solution.lean`), which is the repository's own convention.
- Every audited theorem depends on exactly `propext`, `Classical.choice`, `Quot.sound`.

**New mathematics added this session** — a new module `RiemannHypothesis/ZeroCountLower.lean`, `sorry`-free, closing the gap between the two zero-counting results that were already present (the upper bound `N(T) = O(T log T)` and the infinitude of the zero set). Writing `N(T) = #{ρ : ζ ρ = 0, 0 < re ρ < 1, |im ρ| ≤ T}`:
- `monotone_ncard_nontrivialZeros` : `T ↦ N(T)` is monotone;
- `exists_mem_nontrivialZeroSet_lt_abs_im` : for every height `T` there is a zero of `ζ` in the open critical strip with `T < |im s|` — the nontrivial zeroes are not confined to any horizontal strip;
- `exists_le_ncard_nontrivialZeros` : every natural number is a lower bound for `N(T)` at some height;
- `tendsto_ncard_nontrivialZeros_atTop` : `N(T) → ∞` as `T → ∞`.

Scope, stated plainly: zeroes are counted without multiplicity and the results are qualitative — no rate is obtained, since the divergence inherits the non-effectivity of the infinitude proof (a proof by contradiction). Nothing here bears on the real parts of the zeroes, so none of it approaches the Riemann hypothesis.

**Bookkeeping**, following the repository's existing conventions: new task-board row `M2-ZERO-COUNT-LOWER` (`DONE_STRONG`); an evidence file `docs/goal/evidence/2026-08-20-m2-zero-count-lower.md` with an adversarial-revalidation section; full statement pins in `scripts/revalidation.lean` and axiom checks plus the import in `scripts/audit.sh`; a new README module-table row and section; `docs/current-goal-state.md` regenerated; the module added to `RiemannHypothesis.lean`.

All work is committed and pushed.

# Summary of changes for run 8ddfff0f-9a48-48b9-a4ce-349db4a7b730
The project is finished and every gate passes.

**New mathematics proved this session (no `sorry`, axioms exactly `propext`, `Classical.choice`, `Quot.sound`):**

- `RiemannHypothesis/ZeroInfinite.lean` (new module) — **ζ has infinitely many zeroes in the open critical strip** (`infinite_nontrivialZeroSet`; equivalently `infinite_setOf_xiFn_eq_zero` for ξ). Supporting results, stated generally so they can be reused:
  - `exists_rootMultiset_factorization`: an entire function that is not identically zero and whose zeroes lie in a finite set equals `∏(z − ρ)` (over a multiset of roots, with multiplicity) times an entire function with no zeroes. Proved by induction on the total order of vanishing, dividing out one root at a time via `dslope`.
  - `rootProd` and its two estimates (`norm_rootProd_le`, `one_le_norm_rootProd`), `differentiable_dslope`, `analyticOrderAt_ne_top`, and `xiFn_eq_zero_iff_mem_nontrivialZeroSet` (the zeroes of ξ are exactly the nontrivial zeroes of ζ).
  - The contradiction: if the strip held only finitely many zeroes, ξ would be a finite product of linear factors times `exp G` with `G` linear (order-one growth + Borel–Carathéodory + a compactness bound on a disc), so ‖ξ‖ would be at most exponential along the real axis — contradicting `‖ξ(2n+2)‖ ≥ π^{−(n+1)}·n!`.
- `RiemannHypothesis/ZeroExists.lean` was refactored: the "factorial beats every exponential" step is now the reusable theorem `xiFn_growth_contradiction`, used by both the existence and the infinitude proofs; an unused hypothesis was dropped.

**Repository bookkeeping completed** (following the repo's own conventions) for both the previously unrecorded `ZeroExists.lean` and the new `ZeroInfinite.lean`:
- task-board rows `M2-ZERO-EXISTS` and `M2-ZERO-INFINITE` (both `DONE_STRONG`), board validates with 59 tasks;
- evidence files `docs/goal/evidence/2026-08-20-m2-zero-exists.md` and `...-m2-zero-infinite.md`, each with an adversarial-revalidation section, plus cross-references added to the earlier `M2-ZERO-SUM` evidence (its "no zero is known to exist" caveat is now superseded);
- statement pins for all new results written out in full in `scripts/revalidation.lean`, and `#print axioms` checks plus imports added to `scripts/audit.sh`;
- README module table and two new sections; `docs/current-goal-state.md` regenerated.

**Verification:** `lake build` succeeds for the whole project; the only `sorry`s in the repository remain the three intentional ones in `Challenge.lean` (proved in `Solution.lean`); `bash scripts/audit.sh` prints `OK`. All work is committed and pushed.

# Summary of changes for run 147b0953-8e11-4a5b-a724-d5de1ad2f756
I picked the project up where it stood and closed the work that was left open, keeping the repository's own conventions (task board, evidence files, statement pinning, audit script). `lake build` succeeds, `scripts/audit.sh` reports `OK` with 54 tasks validating, and the only `sorry`s in the repository remain the three intentional ones in `Challenge.lean`. Every theorem below depends on exactly `propext`, `Classical.choice`, `Quot.sound`. All work is committed and pushed.

**1. `RiemannHypothesis/DeBruijnNewman.lean` — finished and wired in.** The file was present but did not compile (nine broken proofs) and was not part of the build, the audit, the pins, the README or the board. It is now `sorry`-free and integrated. It defines the de Bruijn–Newman weight `Φ(u) = ∑_{n≥1}(2π²n⁴e^{9u} − 3πn²e^{5u})e^{−πn²e^{4u}}`, the family `H_t(z) = ∫_0^∞ e^{tu²}Φ(u)cos(uz)du`, and the constant `Λ = inf{t | every zero of H_t is real}`, and proves: the decay estimate `|Φ(u)| ≤ C e^{9u}e^{−πe^{4u}}` for `u ≥ 0`, absolute convergence of the defining integral, and that `z ↦ H_t(z)` is **entire** for every real `t` (differentiation under the integral sign against `C e^{tu² + (11+‖z‖)u − 2u³}`). I also added the symmetries `H_t(−z) = H_t(z)` and `H_t(conj z) = conj H_t(z)`, so the zero set is symmetric about the real axis. The two literature results — `RH ↔ Λ ≤ 0` and `Λ ≥ 0` — are recorded as `Prop`s only and are *not* proved; nor is the identification of `H₀` with `Ξ`.

**2. New file `RiemannHypothesis/Xi.lean` — the Riemann `Ξ` function and a new equivalent form of the hypothesis.** `Ξ(z) = ½ s(s−1)Λ(s)` at `s = ½ + iz`, written as `½(s(s−1)Λ₀(s) + 1)` so that it is manifestly entire. Proved: `Ξ` is entire; `Ξ(z) = ½ s(s−1)Λ(s)` off the two poles; `Λ` is zero-free for `re s ≥ 1` and (by the functional equation) for `re s ≤ 0`; `Ξ(z) = 0` **iff** `s = ½+iz` lies in the open critical strip and `ζ(s) = 0`; hence `zeta_strip_iff_xi` and `zeta_iff_xi`: **the Riemann hypothesis is equivalent to "every zero of `Ξ` is real"**. Also proved: `Ξ` is even (the functional equation in the `Ξ`-variable), `Ξ` is real on the real axis, and — as auxiliary results of independent use — that `Γ_ℝ`, `Λ` and `Λ₀` commute with complex conjugation inside the critical strip. Finally, a conditional bridge `zeta_iff_dbnH_zero_of_eq`: granting the (here unproved) Fourier representation `H₀ = Ξ`, the hypothesis is exactly the reality of the zeroes of `H₀`.

**3. Bookkeeping.** Two board rows updated/added — `M2-DE-BRUIJN-NEWMAN` and the new `M0-XI`, both `DONE_STRONG` — each with an evidence file under `docs/goal/evidence/` containing an adversarial-revalidation section; full statement pins in `scripts/revalidation.lean`; `#print axioms` checks and imports in `scripts/audit.sh`; new README module-table rows and two new README sections; `docs/current-goal-state.md` regenerated.

**What remains open, honestly.** The Riemann hypothesis itself is not proved, and no term of the conjecture's type exists anywhere in the repository — everything added here is an equivalence, a symmetry, or an analytic estimate. Still open on the board and correctly marked as such: the log-free convexity bound, the exponent-1 de la Vallée Poussin zero-free region, the explicit formula, the prime number theorem, Hardy/Levinson/Conrey/Selberg, and the proofs (as opposed to statements) of `RH ↔ Λ ≤ 0` and `Λ ≥ 0`; these need contour-integration, zero-counting and mollifier machinery that is neither in Mathlib nor in this repository.

# Summary of changes for run a2f49518-8b90-46bb-b746-3af6cd89ea75
I picked up the project where the previous session left off and closed the outstanding work, leaving the repository building cleanly with the full audit passing.

**Completed this session**

1. **Mertens' second theorem** — `RiemannHypothesis/MertensSecond.lean` (previously a skeleton with six unproven lemmas) is now fully proved, with no `sorry`:
   - `primeRecipSum x = ∑_{p ≤ x} 1/p` (definition);
   - `sum_by_parts_Ioc`, the discrete Abel summation identity;
   - `sum_inv_sq_le` : `∑_{n=2}^{M} 1/n² ≤ 1`;
   - the two one-term estimates `log n (f(n) − f(n+1)) = log log(n+1) − log log n + O(1/n²)` for `f(n) = 1/log n`, and the telescoping bounds built from them;
   - `mertens_second_nat` : `|∑_{p ≤ N} 1/p − log log N| ≤ 50` for `N ≥ 2`;
   - `mertens_second` : `|∑_{p ≤ x} 1/p − log log x| ≤ 52` for real `x ≥ 4`.

   The proof is Abel summation applied to the prime form of Mertens' first theorem (proved earlier in this repository). Only boundedness of the error is established — the existence of the Meissel–Mertens constant is not proved — and the explicit constants are not sharp.

2. **Mertens' third theorem, bounded form** — new file `RiemannHypothesis/MertensThird.lean`, also `sorry`-free:
   - `primeProd x = ∏_{p ≤ x} (1 − 1/p)⁻¹` (definition);
   - `neg_log_one_sub_bounds` : `t ≤ −log(1 − t) ≤ t + 2t²` for `0 < t ≤ 1/2`;
   - `log_primeProd_sub_primeRecipSum_bounds` : the log of the product exceeds `∑_{p ≤ x} 1/p` by at most `2`;
   - `mertens_third` : `|log ∏_{p ≤ x} (1 − 1/p)⁻¹ − log log x| ≤ 54` for `x ≥ 4`;
   - `mertens_third_bounds` : `e^{−54} log x ≤ ∏_{p ≤ x} (1 − 1/p)⁻¹ ≤ e^{54} log x`.

   The sharp asymptotic with the constant `e^γ` is *not* proved, only comparability with `log x`.

3. **Bookkeeping**, following the repository's existing conventions: two new task-board rows (`M1-MERTENS-SECOND`, `M1-MERTENS-THIRD`, both `DONE_STRONG`), two new evidence files under `docs/goal/evidence/` each containing an adversarial-revalidation section, full statement pins in `scripts/revalidation.lean`, `#print axioms` checks and imports in `scripts/audit.sh`, README module-table rows and prose sections, and a regenerated `docs/current-goal-state.md` (50 tasks validate).

**Verification.** `lake build` succeeds; `bash scripts/audit.sh` reports `OK`; the only `sorry`s in the repository are the three intentional ones in `Challenge.lean`; and every new theorem depends on exactly `propext, Classical.choice, Quot.sound`.

**What remains open.** The Riemann hypothesis itself is not proved and no term of type `ZetaForm` exists anywhere in the repository — that row, and the prime number theorem row, remain open, as the board records. All work is committed and pushed.

# Summary of changes for run a5fb1d4e-ca37-43a2-92b9-d0c448b511df
I continued the project's task board and closed three more rows, each with a sorry-free Lean proof, statement pinning, evidence, and an adversarial-revalidation note. The full audit (`scripts/audit.sh`) reports `OK` with 46 tasks validating; all work is committed and pushed.

**New results (all proved, no `sorry`, axioms exactly `propext`, `Classical.choice`, `Quot.sound`)**

1. `RiemannHypothesis/StripGrowth.lean` — the trivial convexity bound inside the critical strip:
   `norm_riemannZeta_le_strip` : for `0 < re s ≤ 1` and `|im s| ≥ 3`,
   `‖ζ(s)‖ ≤ (8 / re s) · |im s|^(1 − re s) · (1 + log|im s|)`.
   Proved by truncating the continued Euler–Maclaurin representation at `N = ⌈|im s|⌉`. At `re s = 1/2` this is `O(√|t| log|t|)`, improving the previously available bound that was linear in `|t|`.

2. `RiemannHypothesis/ZeroLocation.lean` — reflecting the repository's zero-free region in the critical line (via the symmetry `ζ(s) = 0 → ζ(1−s) = 0`) confines the zeroes:
   `zero_mem_shrinking_strip` : `ζ(s) = 0` and `|im s| ≥ 4` imply
   `2^(−45)/(log|im s|)^9 ≤ re s ≤ 1 − 2^(−45)/(log|im s|)^9`, and equivalently
   `zero_abs_re_sub_half_le` : `|re s − 1/2| ≤ 1/2 − 2^(−45)/(log|im s|)^9`.

3. `RiemannHypothesis/PrimeCounting.lean` — the prime number theorem reduced to a single analytic input:
   `chebyshev_theta_tendsto_of_psi` (`ψ(x)/x → 1` ⟹ `θ(x)/x → 1`),
   `primeCounting_tendsto_of_chebyshev_theta` (`θ(x)/x → 1` ⟹ `π⌊x⌋/(x/log x) → 1`), and their composite
   `primeCounting_tendsto_of_chebyshev_psi`.
   These are implications; the hypothesis `ψ(x) ~ x` is itself equivalent to the prime number theorem and is **not** proved.

**Bookkeeping**: new board rows `M1-STRIP-TRIVIAL-BOUND`, `M1-ZERO-LOCATION`, `M1-PNT-REDUCTION` (all `DONE_STRONG`); the boundaries of `M1-GROWTH` and `M1-PNT` were rewritten to state accurately what is now proved and what is left; new evidence files under `docs/goal/evidence/`; new pins in `scripts/revalidation.lean` and axiom checks in `scripts/audit.sh`; `docs/current-goal-state.md` regenerated; README updated with the new modules and two new sections.

**What is not finished, honestly**: the Riemann hypothesis itself (`M4-RH`) is an open problem and remains unproved — no term of the conjecture's type exists anywhere in the repository. Also still open: the convexity exponent `(1−σ)/2` in `M1-GROWTH` (needs the approximate functional equation or Phragmén–Lindelöf with Gamma-factor asymptotics on vertical lines, which are unavailable); the exponent-1 de la Vallée Poussin region `M1-ZERO-FREE-REGION` (needs the Borel–Carathéodory/Landau estimate for `ζ'/ζ`); and `M1-EXPLICIT`, `M1-PNT`, `M1-HARDY`, `M1-ALMOST-ALL-STRIP` and the M2/M3 rows, which need contour-integration and zero-counting machinery not present. The three `sorry`s in `Challenge.lean` are the repository's existing convention (that file states the problem; `Solution.lean` proves it).

# Summary of changes for run ae61b859-ac6c-4bf6-a3c2-0c8f1aa2e7c8
## What I did

I picked the project up where it stood (statement of the Riemann hypothesis plus the equivalence of its three standard formulations, all building and audit-clean) and carried it forward with new, machine-checked mathematics, documentation, and hygiene work. The repository builds with `lake build`, `scripts/audit.sh` passes, and the only `sorry`s are the three intentional ones in `Challenge.lean` (the statement of record, which the repository's own convention requires to be unproved there and proved in `Solution.lean`).

An important caveat, stated plainly: **the Riemann hypothesis itself is open and is not proved here.** Everything below is about equivalent reformulations, symmetries, and classical estimates.

### New file `RiemannHypothesis/Symmetry.lean` — symmetries of the zero set, five more equivalent forms
- `riemannZeta_conj_of_mem_strip` : `ζ(conj s) = conj (ζ s)` for `0 < re s < 1`. Mathlib has no conjugation symmetry for `ζ`, so I proved it from the project's paired eta series (`dirichletEta_conj`) through the identity `η = (1 − 2^(1−s)) ζ`.
- `riemannZeta_one_sub_eq_zero_of_mem_strip` : zeroes in the strip reflect under `s ↦ 1 − s` (functional equation).
- `riemannZeta_ofReal_ne_zero_of_lt_one` : `ζ` has no zero on the real interval `(0,1)`, because every paired term of the eta series is a positive real.
- Equivalences with the strip form: `zeta_strip_iff_upper_strip` (only zeroes with `im s > 0` matter), `zeta_strip_iff_right_strip` (`ζ ≠ 0` on `1/2 < re s < 1`), `zeta_strip_iff_nonvanishing_right` (`ζ ≠ 0` on `re s > 1/2`), `zeta_strip_iff_self_reflective` (each zero satisfies `s = 1 − conj s`), and `zeta_strip_iff_forall_verifiedUpToHeight` (the hypothesis is exactly the numerical verification succeeding at *every* height).

### New file `RiemannHypothesis/Alternating.lean` — a fully elementary form
- `tendsto_alternating_partialSum_dirichletEta` : for `0 < re s` the **partial sums** of `∑ (−1)ⁿ/(n+1)ˢ` converge to `η(s)` — including inside the strip, where the series is only conditionally convergent and Mathlib's unconditional `tsum` carries no information. Proved by splitting a partial sum into complete pairs plus at most one leftover term of norm `N^(−re s)`.
- `eta_iff_eta_limit`, `zeta_iff_eta_limit` : the Riemann hypothesis is equivalent to a statement with no analytic continuation and no unconditional summation — only limits of partial sums of an explicit series.

### New file `RiemannHypothesis/Bounds.lean` — first classical estimates
- `norm_riemannZeta_le_of_one_lt_re` : `‖ζ(s)‖ ≤ 1 + 1/(re s − 1)` for `re s > 1`, via a sum–integral comparison.
- `three_add_four_cos_add_cos_two_nonneg` : the Mertens inequality `0 ≤ 3 + 4cos θ + cos 2θ`, the elementary input to the classical zero-free region.

### Hygiene and bookkeeping
- Cleared every linter warning in the pre-existing sources (over-long lines, unused `simp` arguments, an unused hypothesis in `Connected.lean`), fixing the code rather than suppressing the linter.
- Extended `scripts/audit.sh` to check the axioms of all the new theorems, and made its axiom check robust to line-wrapped `#print axioms` output. Every checked theorem depends on exactly `propext`, `Classical.choice`, `Quot.sound`.
- Added task-board rows `M0-SYMMETRY`, `M0-ALTERNATING-STRIP`, `M1-ABS-CONV-BOUND` with evidence files under `docs/goal/evidence/`, regenerated `docs/current-goal-state.md`, and updated `README.md` and `formalization.yaml`. The remaining board rows (growth bounds inside the strip, zero-free region, PNT, Hardy, Levinson/Conrey, and the conjecture itself) are left open and honestly marked as such.

All work is committed and pushed.
