# 高斯素数扇区方差在慢增长尺度上的大值

**Large Values of the Variance of Gaussian Prime Counts in Sectors**  
*The slowly growing K regime*

**GPT6.2 Astra**（AI 协作者，数学推导、执笔及 Lean 源码）  
**DM Wu**（研究发起人、项目维护与通讯，GitHub：[@DM-W-2026](https://github.com/DM-W-2026)）

[阅读 PDF](paper.pdf) · [查看 Lean 源码](SlowGrowth.lean)

**摘要**　考察高斯数域中范数不超过 $x$ 的素理想在移动扇区中的计数方差。令 $\log_j$ 表示 $j$ 次迭代自然对数。对于预先指定的 $K=\lfloor\log_2 x/\log_3 x\rfloor$，本文证明，实际方差与 Rudnick–Waxman 预测主项的比值沿一列半径至少达到常数乘 $\log_3 x$。证明分别处理角 Hecke 函数有右偏零点与全族满足其黎曼猜想的情形。在后一情形，同时逼近一组零点的相位，再将光滑素理想和转回同一半径的尖截计数。所得下界限制了方差预测在任意慢增长尺度上的逐点适用范围。

## 1　命题与计数约定

对 $\mathbb Z[i]$ 中素理想 $\mathfrak p=(z)$，置 $u_{\mathfrak p}=2\arg(z)/\pi\bmod 1$。相差一个单位的生成元给出同一点。计入范数 $\mathrm N\mathfrak p\le x$ 的全部素理想，每个理想权为一。分裂素数上方的两个理想分别计数，轴上的惰性素理想也保留。记总数为 $N=N(x)\sim x/\log x$。令 $n_{x,K}(u)$ 为落在中心 $u$、相对宽度 $1/K$ 的圆弧内的计数，圆周测度归一为一。记
$$
 V(x,K)=\int_0^1\bigl|n_{x,K}(u)-N/K\bigr|^2\,du,\qquad
 P(x,K)=\frac NK\min\!\left(1,\frac{2\log K}{\log N}\right).
$$

**定理 1.** 对充分大的 $x$，令 $K_*(x)=\lfloor\log_2 x/\log_3 x\rfloor$。存在常数 $c>0$ 和序列 $x_j\to\infty$，使得
$$
 \frac{V(x_j,K_*(x_j))}{P(x_j,K_*(x_j))}\ \ge\ c\,\log_3 x_j.
$$

**推论.** 将 [1，猜想 1.2] 解读为对任意允许的 $K(x)\to\infty$ 均有 $V(x,K(x))/P(x,K(x))\to1$，上式即给出反例。由于 $\log K_*(x)/\log x\to0$，该结论未判定任何固定 $0<\delta<1$、$K=\lfloor x^\delta\rfloor$ 的情形。[1，第 5 节] 的随机矩阵模型固定 $x=K^\alpha$ 中的 $\alpha$。算术级数的素数方差在慢增长模数下出现大值已有 Fiorilli–Martin [2] 的先例；此处需要处理角 Hecke 特征与原始无权扇区计数的衔接。

## 2　傅里叶投影与零点的两种情形

对每个非零整数 $m$，定义 $\Xi_m((z))=(z/|z|)^{4m}$ 及
$$
 S_m(x)=\sum_{\mathrm N\mathfrak p\le x}\Xi_m(\mathfrak p),\qquad
 b_m(K)=\frac{\sin(\pi m/K)}{\pi m}.
$$
移动圆弧计数是指示函数与素理想角度测度的卷积。减去均值消去零频，由 Parseval 恒等式得到
$$
 V(x,K)=\sum_{m\ne0}|b_m(K)|^2\,|S_m(x)|^2. \tag{1}
$$
在 $1\le m\le K/2$ 上，正弦函数的弦线下界给出 $b_m(K)\ge 2/(\pi K)$。共轭理想使 $S_m(x)$ 为实数，且 $L(s,\Xi_m)=L(s,\Xi_{-m})$。

**有右偏零点的情形.** 假设某个固定 $m\ge1$ 的 $L(s,\Xi_m)$ 在实部 $\beta>1/2$ 处有零点。取 $1/2<\sigma<\beta$。若 $S_m(x)=O(x^\sigma)$，按范数分部求和将一次素理想级数延拓到 $\Re s>\sigma$。对数欧拉乘积中素理想幂次至少为二的部分在此绝对且局部一致收敛。两部分相加再取指数，就在该半平面给出了与 $L(s,\Xi_m)$ 一致的无零函数，产生矛盾。因此沿一列 $x\to\infty$ 有 $|S_m(x)|\ge x^\sigma$。取 $K=K_*(x)$，由 (1) 和 $P\le N/K$ 得 $V/P\gg x^{2\sigma}/(KN)$，其增长快于 $\log_3 x$。

**其余情形.** 各完备函数满足关于 $s\mapsto1-s$ 的函数方程 [1，式 (4.1)]，故余下的情形是所有非零角特征的非平凡零点均位于临界线上。以下在这一分支证明同一下界。两种情形穷尽可能，定理 1 的陈述不假设 GRH。

## 3　使一段角频率在同一尺度产生大值

选取实值 $\eta\in C_c^\infty(\mathbb R)$，积分非零，令 $\check\eta(v)=\eta(-v)$、$g=\eta*\check\eta$。傅里叶变换用正指数 $e^{itv}$。通过缩小 $\eta$ 的支撑，可使 $h(t)=\widehat g(t)=|\widehat\eta(t)|^2$ 在 $[-1,1]$ 上有正下界。$h$ 在全实轴非负且快速衰减。对 $X=e^y$，以 $\Lambda$ 表示理想的 von Mangoldt 函数，置
$$
 B_m(y)=\sum_{\mathfrak a}\frac{\Lambda(\mathfrak a)\Xi_m(\mathfrak a)}
                    {\sqrt{\mathrm N\mathfrak a}}\,
                 g(\log\mathrm N\mathfrak a-y).
$$
在 [1，命题 4.2、引理 4.3] 中取固定的径向测试函数 $\Phi(t)=t^{-1/2}g(\log t)$，再除以 $\sqrt X$。其 Mellin 变换在 $1/2+i\gamma$ 的值为 $h(\gamma)$。由此，对 $m\ge1$ 一致地有
$$
 B_m(y)=-\sum_{\gamma} h(\gamma)e^{i\gamma y}
                +O_g\!\left(y^{-100}\log(2m)\right). \tag{2}
$$
其中 $\gamma$ 遍历零点纵坐标，重数计入。

由 [1，式 (4.2)]，当 $m\to\infty$ 时，高度 $0\le\gamma\le1$ 内的零点数渐近于 $(\log m)/\pi$。又由 [1，式 (4.6)]，每个 $[j,j+1]$ 内零点数为 $O(\log(2m+|j|+2))$。用 $h$ 的快速衰减在单位区间上求和，先固定 $c_0>0$ 足够小，再固定 $D>1$ 足够大，即对所有充分大的 $m$ 得
$$
 \sum_{|\gamma|\le1}h(\gamma)\ge c_0\log m,\qquad
 \sum_{|\gamma|>D}h(\gamma)\le(c_0/8)\log m .
$$
后一选择可独立于 $m$，因为 $\log(2m+|j|+2)\ll\log(2m)+\log(2+|j|)$。

对大整数 $M$，收集 $M\le m\le2M$、$|\gamma|\le D$ 的全部纵坐标，数目 $d\ll_D M\log M$。令 $y_0=\exp(10M\log M)$。将单位 $d$ 维立方体划成 $12^d$ 个等盒，放入 $j y_0(\gamma)_\gamma/(2\pi)$ 的逐坐标小数部分，$0\le j\le12^d$。同盒两点的指标之差给出 $1\le q\le12^d$，使每个 $q y_0\gamma/(2\pi)$ 距整数至多 $1/12$。取 $y=qy_0$，则
$$
 10M\log M\le\log y\le C_D M\log M,\qquad
 \cos(\gamma y)\ge\cos(\pi/6)\quad(|\gamma|\le D).
$$
由 (2) 取实部，所有低高度零点同向贡献，尾部和余项至多消去主项的一部分，故在这个共同的 $y$ 上
$$
 -\Re B_m(y)\gg_g\log M\qquad(M\le m\le2M). \tag{3}
$$

## 4　由光滑和回到一个尖截半径

固定 $A$ 使 $\operatorname{supp}g\subset(-A,A)$，记 $I_X=[e^{-A}X,e^AX]$。先从 (3) 去掉高次素理想幂。对 $\mathbb Q(i)$，有 $\sum_{\mathrm N\mathfrak p\le u}\log\mathrm N\mathfrak p\ll u$（也可由有理素数的 Chebyshev 上界与素理想分解直接推出）。故平方项的未归一化绝对总和为 $O_A(\sqrt X)$，三次及以上为 $O_A(X^{1/3}\log X)$。在窗内除以 $\sqrt{\mathrm N\mathfrak a}$ 后合计为 $O_g(1)$，一致于 $m$。一次项的轴向理想始终计入。

令 $w_X(t)=t^{-1/2}\log t\,g(\log(t/X))$。由 (3)，每个一次项 $\int w_X\,dS_m$ 的实部均 $\le -c_1\log M$。因此可以先对 $m$ 带符号相加，再分部求和。$w_X$ 在端点消失，且直接求导、置 $v=\log(t/X)$，可得 $\int_{I_X}|w'_X(t)|\,dt\ll_g(\log X)/\sqrt X$。于是
$$
 M\log M\ll_g
 \left|\sum_{m=M}^{2M}\int w_X\,dS_m\right|
 \le \sup_{t\in I_X}\left|\sum_{m=M}^{2M} S_m(t)\right|
                         \frac{C_g\log X}{\sqrt X}.
$$
阶梯函数在有限窗内只取有限多个值，故上确界在某个 $x\in I_X$ 取到。对该**同一个** $x$ 用 Cauchy–Schwarz，再利用 $x\asymp_g X$，得到
$$
 \sum_{m=M}^{2M}|S_m(x)|^2\gg_g
                  \frac{x}{(\log x)^2}M(\log M)^2. \tag{4}
$$

最后，$\log_2 x=\log y+o(1)$，$\log_3 x=\log M+\log\log M+O_D(1)$，故对充分大的 $M$ 有 $4M\le K_*(x)\ll_D M$。记 $K=K_*(x)$。在此尺度上，
$P(x,K)\sim 2x\log K/[K(\log x)^2]$。在 (1) 中保留 (4) 的一段频率，便有
$$
 \frac{V(x,K)}{P(x,K)}
 \gg \frac{M(\log M)^2}{K\log K}
 \gg \log M\asymp\log_3 x .
$$
令 $M$ 趋于无穷，所得 $x$ 趋于无穷。结合第 2 节的另一分支即证定理 1。$\square$

**形式化说明.** 附带源码在 Lean 4.19.0 与 mathlib 提交 `c44e0c8` 上核验。前四条定理分别处理有限维相位同时逼近、离散分部求和中的共同半径、由频段能量下界推出方差比值下界，以及该比值在任意远处达到或超过 $2$ 与趋于 $1$ 的不相容。第五条定理把频段能量、投影、主项及参数选择四组估计合成为上述慢增长尺度上的无界比值。共同半径引理取带符号权 $w_j=-\int_{I_j}w_X'(t)\,dt$，其中 $I_j$ 为阶梯函数的各常值段，故 $\sum_j|w_j|\le\int|w'_X|$。显式公式、零点计数、素理想算术以及这些输入与最终数域定理的衔接采用上述纸笔证明。源码中的下界和投影假设以显式参数传入。

**参考文献**

[1] Z. Rudnick and E. Waxman, *Angles of Gaussian primes*, Israel Journal of Mathematics **232** (2019), 159–199. [论文与公式编号](https://arxiv.org/pdf/1705.07498)

[2] D. Fiorilli and G. Martin, *Disproving Hooley’s conjecture*, Journal of the European Mathematical Society **25** (2023), 4791–4812. [DOI](https://doi.org/10.4171/JEMS/1291)
