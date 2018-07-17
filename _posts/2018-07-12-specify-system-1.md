---
layout: post
title: Specifying System (1)
summary: 概述 Specifying System TLA+
tags: [ distribute, tla+, formula]
---

本系列来自《Specifying Systems》的阅读笔记。

## 概述

* 并发系统的正确性是很难证明的，因为异步点太多，人类的大脑不是为并发而进化的，并发系统的行为变化可能性太多
* 如果能够把系统的状态/行为抽象为时态逻辑（Temporal Logic），结借助CPU超强的算力，穷举出所有可能的behavior（状态序列）就可以判断系统是否正确
* 基本的TLA+语法和使用可见状态序列是指数级别，需要深入立即系统和TLA+对状态进行剪枝
* 什么是Temporal Logic：系统随着时间的推移，可能出现的状态序列
* TLA+是基于数理逻辑的语言，如果你对数理逻辑很有研究，那么会如鱼得水

## What is a specification?

* spec描述应该实现什么，而不是描述如何实现
* 用来验证设计，而不是教你如何设计
* 在动手coding之前，进行specify能帮助你更好的理解你的系统
* 只验证设计是否正确而不验证性能
* specification的基础是数学，因为只有数学语言是精确的
* 这里用到的数学是更加形式化的数学，而不是我们在学校时学到的经典数学（大部分也不是精确的）。形式化的数学看起来很冗长，但是能用最少的数学概念描述一个系统。


## Why TLA+

* 1977年，艾米尔.伯努利用时序逻辑temporal logic来specify一个系统，但是只能描述部分系统
* 1980年代，Lamport发明了TLA（temporal logical action），选择了数学家们（而不是程序员）所喜爱的一阶逻辑理论和集合理论
* TLA提供了specify系统的数学基础，数学描述现实的系统，TLA来形式化数学：TLA就是来解决如何用程序描述数学的问题，而TLA+就是这门语言，仅仅借鉴了编程语言的模块化的思想，除此之外都是数学概念
* TLA+可以方便描述任何离散的系统（因为它建立于集合论），尤其是异步系统
* TLA+使用简洁的数学语言来描述状态转换
* TLA+不是用来描述程序执行的指令序列

## 一个例子
* C语言代码

```
int i;
void main() {
    i = someNumber();
    i = I + 1;
}
```

* 和这段代码等价的spec是下面这段tla（emacs上可以安装一个插件，以prity-print方式显示希腊字符）

![]({{ site.url }}images/2018-07-12-specify-system-1.jpg)


* 几点说明：
	* TLA+支持以模块方式组织代码
	* 以——————————— MODULE SimpleProgram ----------------------开始
	* 以====================================================结尾
	* 任何TLA+ spce都要有Init和Next，Init和Next被称为formula
	* TLA+会默认用Init进行初始化状态，默认用Next迭代可能到达的状态
	* Init == (pc = "start") /\ (i = 0), ‘==’ 定义一个 formula
	* 逻辑与运算符‘/\’：a /\ b 表示先发生a，再发生b
	* 逻辑或运算符‘\/’：a \/ b 表示要么发生a，要么发生b
	* Next formula描述的是一个状态机，‘\/’运算连接起来的是两个状态入口“start”和“middle”
	* pc’ 和 i’ 是下一个状态中pc和I的值，记做(pc primae, i prime)
	* TLA+ 使用宽度遍历，暴力遍历所有可达的状态
	
## 总结
* 任何系统都能够使用状态机描述
* specify状态机所有可达的状态
* TLA+使用CPU超强的算力穷举所有可能的状态序列



