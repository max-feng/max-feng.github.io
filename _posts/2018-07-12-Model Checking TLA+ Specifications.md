---
layout: post
title: Model Checking TLA+ Specifications
summary: Model Checking TLA+ Specifications
tags: [ distribute, TLA, replication, paper ]
---

《Model Checking TLA+ Specifications》论文笔记。这篇论文是TLC作者Yuanyu发表的，由于时间比较早，TLC的部分特性都还没有支持，所以这片论文的部分只有部分观点是有益的。



## TLA+特点

模型校验器以能处理的系统大小或者能校验的property分类。系统通常以硬件描述语言或者为系统定制的语言。

TLC校验的spec是使用TLA+语言描述。TLA+是具有完备语义的，表达能力极强，描述推理的语言，而不是仅仅为了模型校验：

1. 当系统太庞大太复杂，模型校验不能完全覆盖的时候，只能通过逻辑推理进行校验。我们想通过模型校验对有限状态机进行设计层次的校验，以发现设计上的错误，因此spec语言一定要能有方便的描述推理；
2. 我们希望系统的设计者来对系统的正确性进行形式化的证明。这样不需要专业的验证化小组来描述系统了，可以省略了从设计方案到形式化逻辑的翻译过程。因此，这门语言一定要具有极强的表达能力。 

我们先对并发系统或者事件驱动系统进行验证，比如：网络通信，cache一致性协议。这类设计典型的RTL实现层次高1，2层。通常不是有限状态机，包含任意数目的processor和任意数目的quueue。ad hoc技术能把这类spec规约成有限状态机，但是对精确的细节很敏感。而TLC可以方便选择有限模型描述类似的spec，并校验所有的case。



## TLA+的不变式

TLA：Temporal Logic of Actions。TLA+是对TLA的扩展。TLA的设计目标是使用最简单最直接的方式形式化并发系统的正确性。经过20年的实践发现，基于不变式的方式是对并发系统正确性推理的很好的方式。优秀的程序员再设计多线程算法时都会使用不变式的方式来思考问题

TLA+是一种形式化语言，完备的实现了第一阶逻辑和ZF吉和理论。

在TLA中spec被拆分成formula。在校验正确性的关键步骤是找到系统的不变式：在所有可达的状态中都为TRUE的谓词表达式。大量的实践表明校验系统的不变式是发现bug的最有效的方式。



## TLC是如何工作的

1. TLC使用Explicit state representation；
2. TLC内部有两个结构体（宽度遍历）：seen和sq
    a. seen 所有已经reach过的state；seen是所有reach过状态的fingerprints: 64位整数（比如状态的checksum），同时为了做错误回溯，也记录了前继节点）；
    b. sq 所有seen的后继节点，sq里是真正完整的状态；
3. TLC对Init和Next是特殊处理的：
    a. 从Init生成所有可能的状态，放入seen和sq；
    b. 重写Next，扩展成尽量多的‘或’运算，每个‘或’都是一个分支；
4. TLC启动线程池：从sq取出一个state s，生成所有合法的后继节点t
    a. 检查t是否已经在seen中；
    b. 如果没有，校验t是否满足invariant；
    c. 如果满足，把t加入到seen中（并记录前继节点是s）；
    d. 如果t满足constraint，则把t加入到sq中；
    如果TLC发现某个t不满足invariant，或者s没有任何后继节点，TLC生成t的trace。


 