---
layout: post
title: Specifying System (1)
summary: 时钟 Specifying System TLA+
tags: [ distribute, tla+, formula]
---

本系列来自《Specifying Systems》的阅读笔记。

关于学习资料

youtube上的教程在某些细节上没有展开，要了解每个细节以及TLA+用到的术语，还是要阅读原著
后面的内容全部来自《Specifying System》
一个时钟的例子

尝试用TLA描述小时级别的时序逻辑
[hr=11] -> [hr=12] -> [hr=1] -> [hr=2]
hr=11 状态的值为11
[hr=11] -> [hr=12]，一对连续的状态，称为一个step
要描述一个小时粒度的时钟，只需要描述所有的状态
HCInit == hr \in 1..12
HCNext == hr’ = IF hr \= 12 THEN hr + 1 ELSE 1
HCSpec == HCInit /\ [] [HCNext]_hr
HCNext是一个普通的formula，描述的是：old state到new state的转换，这是一个step
像HCNext这种的formula包含了：primed和unprimed变量的，称为action
一个action的值为true或者false
[]HCNext 表示HCNext always为true
HCSpect描述的是: 对于任意的behavior，HCInit为true，并且每一个Next值always为true，也就是说HCSpect是这个系统的spec
Stuttering steps

Stuttering steps：允许某些behavior中state值不变
考虑这样一个场景：当某个事件发生时，时钟就定格了，也就是在某个state之后state不会再更改。比如[hr=12] -> [hr=11] -> [hr=11] ，这个时钟系统在11的时候被stop了，也就说系统允许在任何hr的值退出
这个formula可以表示为：HCNext \/ (hr’ = hr)，注意：这里的hr’ = hr说明系统允许在任何hr的值退出，因为TLA每次宽度遍历都进入hr’ = hr的话，那么state的值就一直是hr了
TLA+中简称为：[HCNext]_hr，表明在可达的behavior中hr允许stuttering的
behavior

一个无限长的状态序列。比如：[hr=11] -> [hr=“abc”] -> [hr=0.12] -> [hr=e] -> …
一个behavior描述的是状态序列的空间中的一个可能。可以想象成深度遍历的解空间，一个behavior就是其中一个遍历路径
Temporal formula：是关于所有behavior的断言。是所有为true的behavior，合法的behavior。比如：HCSpec == HCInit /\ [] [HCNext]_hr 描述所有符合HCNet约束的behavior。HCSpec称为这个时钟系统的specification
theorem：在任何behavior下都为true的formula称为theorem（不变式），即不变式
1）比如：HCInit断言hr是1到12的整数, []HCinit断言HCInit始终都是true，也就是说对于任何满足HCSpec的behavior，[]HCInit都是true，
2）HCSpec => []HCInit，在任何合法的behavior下都成立，因此是一个theorem
完整的TLA+

----------------------------- MODULE hour ------------------------------
EXTENDS Naturals
VARIABLES hr

HCInit == hr \in 1..12
HCNext == hr' = IF hr # 12 THEN hr + 1 ELSE 1
HCSpec == HCInit /\ [] [HCNet]_hr

------------------------------------------------------------------------
THEOREM HCSpec => [] HCInit
========================================================================
TLA+提供了一些基础的模块比如：Naturals（提供加法，减法等，用可以自己定义加法，比如两个矩阵的加法）， Sequence（列表数据结构）
TLA+中操作的任何变量都必须是声明过的
有一堆减号连接起来的横线，可以出现在任何地方，仅仅用来分割较为完整逻辑的一小段代码
THEOREM HCSpec => [] HCInit 断言了由hour模块，Naturals模块和rules ofTLA+推断出来的一个formula（推论）
HCInit，HCNext，HCSpec都是definition，TLA+是一门方便书写数学定义和推理的语言
总结

要描述一个小时粒度的时钟，只需要描述状态转变规则
stuttering steps允许状态机停留在任一点
behavior是状态序列
temporal formula是对所有behavior的断言
theorem是spec的不变式
