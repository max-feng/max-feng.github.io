---
layout: post
title: Specifying System (2)
summary: Specifying System TLA+
tags: [ distribute, tla+, formula]
---

本系列来自《Specifying Systems》的阅读笔记。

## 问题

要用一个 3 加仑的水壶和一个 5 加仑的水壶得到 4 加仑的水，怎么做呢？

## 思路

* 描述两个水壶所有可能的状态，通过TLA+的宽度遍历机制，暴力搜索所有的状态序列（TLA+中称为behavior）
	+ 给 3 加仑水壶灌满水
	+ 给 5 加仑水壶灌满水
	+ 清空 3 加仑水壶
	+ 清空 5 加仑水壶
	+ 将 3 加仑水壶的水倒到 5 加仑水壶
	+ 将 5 加仑水壶的水倒到 3 加仑水壶


## TLA+代码如下

```
-------------------------- MODULE DieHard  --------------------------
EXTENDS Naturals
VARIABLES small,big

Init == /\ small = 0
       /\ big = 0

TypeOK == /\ small \in 0..3
         /\ big \in 0..5


FillSmall == /\ small' = 3
            /\ big' = big

FillBig == /\ small' = small
          /\ big' = 5


EmptySmall == /\ small' = 0
             /\ big' = big

EmptyBig == /\ big' = 0
           /\ small' = small

SmallToBig == IF small + big < 5
             THEN
                /\ big' = small + big
                /\ small' = 0
             ELSE
                /\ big' = 5
                /\ small' = small - (5 - big)

BigToSmall == IF small + big < 3
             THEN
                /\ small' = small + big
                /\ big' = 0
             ELSE
                /\ small' = 3
                /\ big' = big - (3 - small)


Next == \/ FillSmall
       \/ FillBig
       \/ SmallToBig
       \/ BigToSmall
       \/ EmptyBig
       \/ EmptySmall


=============================================================================
\* Modification History
\* Last modified Thu Apr 26 10:31:15 CST 2018 by max
\* Created Wed Apr 25 21:42:59 CST 2018 by max
```

* 涉及到的语法
	+ TLA的变量没有类型的概念，类型的正确性是通过形式化的定义，来检查某个变量的类型是否正确
	+ TLA要求每个形式的定义，都要列举出所有的变量状态，没有默认值
	+ TLA中的‘=’不是程序设计语言中的赋值操作，仅仅是一个判断是否相等的逻辑运算，满足交换性，比如：big = 5 和 5 = big 是等价的
	
* 运行
	+ 使用TLA+ ToolBox 运行上面的代码（具体使用方法可以参考Lamport TLA+的视频)
	+ TLA+校验的算法不会终止，会一直运行下去
	+ 为了让DieHard正确的终止，添加了bit \= 4的不变式
	+ 最终，TLA遍历出了一个可行的状态序列，使得big为4

![]( {{ site.url }}images/2018-07-16-specify-system-diehard.jpg)

## 总结#

* 描述系统可能的状态转换
* TLA+穷举出所有的状态序列
* 每次状态转换都校验invariant
* TLA+列出违背invariant的状态转换序列
