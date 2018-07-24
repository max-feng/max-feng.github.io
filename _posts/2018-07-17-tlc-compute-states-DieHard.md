---
layout: post
title:  TLC是如何计算DieHard状态的
summary: DieHard TLC TLA+
tags: [ distribute, tla+, formula]
---

## 从DieHard分析TLC是如何计算状态的

## TLC计算状态的算法

TLC维护两个变量：seen和sq。seen用来记录已经处理过的状态；sq记录将要计算的状态；


## 问题

* 描述两个水壶所有可能的状态，通过TLA+的宽度遍历机制，暴力搜索所有的状态序列（TLA+中称为behavior）
	+ 给 3 加仑水壶灌满水
	+ 给 5 加仑水壶灌满水
	+ 清空 3 加仑水壶
	+ 清空 5 加仑水壶
	+ 将 3 加仑水壶的水倒到 5 加仑水壶
	+ 将 5 加仑水壶的水倒到 3 加仑水壶

## TLA+代码
为了方便调试，在每个子句开始时打印了状态。

```matlab
-------------------------- MODULE DieHard  --------------------------
EXTENDS Naturals, TLC
VARIABLES small,big

S == <<small, big>>

Init == /\ Print("Init", TRUE)
        /\ small = 0
        /\ big = 0

TypeOK == /\ Print("TypeOK", TRUE)   
          /\ Print(S, TRUE) 
          /\ small \in 0..3
          /\ big \in 0..5


FillSmall == /\ Print("FillSmall", TRUE) 
             /\ Print(S, TRUE) 
             /\ small' = 3
             /\ big' = big
             /\ Print(S, TRUE) 

FillBig == /\ Print("FillBig", TRUE)  
           /\ Print(S, TRUE) 
           /\ small' = small
           /\ big' = 5
           /\ Print(S, TRUE) 


EmptySmall == /\ Print("EmptySmall", TRUE)  
              /\ Print(S, TRUE) 
              /\ small' = 0
              /\ big' = big
              /\ Print(S, TRUE) 

EmptyBig ==  /\ Print("EmptyBig", TRUE)
             /\ Print(S, TRUE)   
             /\ big' = 0
             /\ small' = small
             /\ Print(S, TRUE) 

SmallToBig ==  /\ Print("SmallToBig", TRUE)
               /\ Print(S, TRUE)  
               /\ IF small + big < 5
                  THEN
                    /\ big' = small + big
                    /\ small' = 0
                    /\ Print(S, TRUE) 
                  ELSE
                    /\ big' = 5
                    /\ small' = small - (5 - big)
                    /\ Print(S, TRUE) 

BigToSmall == /\ Print("BigToSmall", TRUE)
              /\ Print(S, TRUE)  
              /\ IF small + big < 3
                  THEN
                    /\ small' = small + big
                    /\ big' = 0
                    /\ Print(S, TRUE) 
                  ELSE
                    /\ small' = 3
                    /\ big' = big - (3 - small)
                    /\ Print(S, TRUE) 


Next == \/ FillSmall
        \/ FillBig
        \/ SmallToBig
        \/ BigToSmall
        \/ EmptyBig
        \/ EmptySmall


=============================================================================
\* Modification History
\* Last modified Wed Jul 18 15:47:26 CST 2018 by max
\* Created Wed Apr 25 21:42:59 CST 2018 by max
```



## 运行结果分析

1. Init生成的状态加入sq中；

2. 从sq中取出一个状态，一次执行Next的几个子句，每执行一个子句就会得到一个新状态，加入sq中；

3. 每次得到新状态都要进行invariant的校验；

4. 如果新状态曾经被计算过（seen），直接丢掉，也不进行invariant的计算；

   

```
========================   这是第1轮 ========================
==== 初始状态是<<0, 0>>
"Init"  TRUE
"TypeOK"  TRUE
<<0, 0>>  TRUE

"FillSmall"  TRUE
<<0, 0>>  TRUE
<<0, 0>>  TRUE
"TypeOK"  TRUE
<<3, 0>>  TRUE 得到新状态<<3, 0>>

"FillBig"  TRUE
<<0, 0>>  TRUE
<<0, 0>>  TRUE
"TypeOK"  TRUE
<<0, 5>>  TRUE  得到新状态<<0, 5>>

"SmallToBig"  TRUE
<<0, 0>>  TRUE
<<0, 0>>  TRUE

"BigToSmall"  TRUE
<<0, 0>>  TRUE
<<0, 0>>  TRUE  \* <<0, 0>>这个状态在INIT之后就已经在seen中了，被处理过了。因此这个地方直接丢掉这个状态：不进入sq；不进行invariant校验；


"EmptyBig"  TRUE
<<0, 0>>  TRUE
<<0, 0>>  TRUE

"EmptySmall"  TRUE
<<0, 0>>  TRUE
<<0, 0>>  TRUE

第1轮总结：本轮新增状态<<3, 0>> 和 <<0, 5>>

========================   开始第2轮 ========================
==== 2.1 从sq中取出第一个状态<<3, 0>>，开始计算Next
"FillSmall"  TRUE
<<3, 0>>  TRUE
<<3, 0>>  TRUE

"FillBig"  TRUE
<<3, 0>>  TRUE
<<3, 0>>  TRUE
"TypeOK"  TRUE
<<3, 5>>  TRUE  得到新状态<<3, 5>>

"SmallToBig"  TRUE
<<3, 0>>  TRUE
<<3, 0>>  TRUE
"TypeOK"  TRUE
<<0, 3>>  TRUE  得到新状态<<0, 3>>

"BigToSmall"  TRUE
<<3, 0>>  TRUE
<<3, 0>>  TRUE

"EmptyBig"  TRUE
<<3, 0>>  TRUE
<<3, 0>>  TRUE

"EmptySmall"  TRUE
<<3, 0>>  TRUE
<<3, 0>>  TRUE

==== 2.2 从sq中取出第一个状态<<0, 5>>，开始计算Next
"FillSmall"  TRUE
<<0, 5>>  TRUE
<<0, 5>>  TRUE

"FillBig"  TRUE
<<0, 5>>  TRUE
<<0, 5>>  TRUE

"SmallToBig"  TRUE
<<0, 5>>  TRUE
<<0, 5>>  TRUE

"BigToSmall"  TRUE
<<0, 5>>  TRUE
<<0, 5>>  TRUE
"TypeOK"  TRUE   
<<3, 2>>  TRUE  得到新状态<<3,2>>

"EmptyBig"  TRUE
<<0, 5>>  TRUE
<<0, 5>>  TRUE

"EmptySmall"  TRUE
<<0, 5>>  TRUE
<<0, 5>>  TRUE

"FillSmall"  TRUE
<<3, 5>>  TRUE
<<3, 5>>  TRUE

"FillBig"  TRUE
<<3, 5>>  TRUE
<<3, 5>>  TRUE

第2轮总结：本轮新增状态 <<3, 5>>,  <<0, 3>>, <<3,2>>

========================   开始第3轮 ========================
==== 3.1 从sq中取出第一个状态<<3, 5>>，开始计算Next
"SmallToBig"  TRUE
<<3, 5>>  TRUE
<<3, 5>>  TRUE

"BigToSmall"  TRUE
<<3, 5>>  TRUE
<<3, 5>>  TRUE

"EmptyBig"  TRUE
<<3, 5>>  TRUE
<<3, 5>>  TRUE

"EmptySmall"  TRUE
<<3, 5>>  TRUE
<<3, 5>>  TRUE

==== 3.2 从sq中取出第一个状态<<0, 3>>，开始计算Next
"FillSmall"  TRUE
<<0, 3>>  TRUE
<<0, 3>>  TRUE
"TypeOK"  TRUE
<<3, 3>>  TRUE  得到新状态<<3, 3>>

"FillBig"  TRUE
<<0, 3>>  TRUE
<<0, 3>>  TRUE

"SmallToBig"  TRUE
<<0, 3>>  TRUE
<<0, 3>>  TRUE

"BigToSmall"  TRUE
<<0, 3>>  TRUE
<<0, 3>>  TRUE

"EmptyBig"  TRUE
<<0, 3>>  TRUE
<<0, 3>>  TRUE

"EmptySmall"  TRUE
<<0, 3>>  TRUE
<<0, 3>>  TRUE

==== 3.3 从sq中取出第一个状态<<3, 2>>，开始计算Next
"FillSmall"  TRUE
<<3, 2>>  TRUE
<<3, 2>>  TRUE

"FillBig"  TRUE
<<3, 2>>  TRUE
<<3, 2>>  TRUE

"SmallToBig"  TRUE
<<3, 2>>  TRUE
<<3, 2>>  TRUE

"BigToSmall"  TRUE
<<3, 2>>  TRUE
<<3, 2>>  TRUE

"EmptyBig"  TRUE
<<3, 2>>  TRUE
<<3, 2>>  TRUE

"EmptySmall"  TRUE
<<3, 2>>  TRUE
<<3, 2>>  TRUE
"TypeOK"  TRUE
<<0, 2>>  TRUE  得到新状态<<0, 2>>

第3轮总结：本轮新增状态<<3, 3>>和<<0, 2>>

========================   开始第4轮 ========================
==== 4.1 从sq中取出第一个状态<<3, 3>>，开始计算Next
"FillSmall"  TRUE
<<3, 3>>  TRUE
<<3, 3>>  TRUE

"FillBig"  TRUE
<<3, 3>>  TRUE
<<3, 3>>  TRUE

"SmallToBig"  TRUE
<<3, 3>>  TRUE
<<3, 3>>  TRUE
"TypeOK"  TRUE
<<1, 5>>  TRUE  得到新状态<<1, 5>>

"BigToSmall"  TRUE
<<3, 3>>  TRUE
<<3, 3>>  TRUE

"EmptyBig"  TRUE
<<3, 3>>  TRUE
<<3, 3>>  TRUE

"EmptySmall"  TRUE
<<3, 3>>  TRUE
<<3, 3>>  TRUE

==== 4.2 从sq中取出第一个状态<<0, 2>>，开始计算Next
"FillSmall"  TRUE
<<0, 2>>  TRUE
<<0, 2>>  TRUE

"FillBig"  TRUE
<<0, 2>>  TRUE
<<0, 2>>  TRUE

"SmallToBig"  TRUE
<<0, 2>>  TRUE
<<0, 2>>  TRUE

"BigToSmall"  TRUE
<<0, 2>>  TRUE
<<0, 2>>  TRUE
"TypeOK"  TRUE
<<2, 0>>  TRUE  得到新状态<<2, 0>>

"EmptyBig"  TRUE
<<0, 2>>  TRUE
<<0, 2>>  TRUE

"EmptySmall"  TRUE
<<0, 2>>  TRUE
<<0, 2>>  TRUE

第4轮总结：本轮新增状态<<1, 5>>和<<2, 0>>

========================   开始第5轮 ========================
==== 5.1 从sq中取出第一个状态<<1, 5>>，开始计算Next
"FillSmall"  TRUE
<<1, 5>>  TRUE
<<1, 5>>  TRUE

"FillBig"  TRUE
<<1, 5>>  TRUE
<<1, 5>>  TRUE

"SmallToBig"  TRUE
<<1, 5>>  TRUE
<<1, 5>>  TRUE

"BigToSmall"  TRUE
<<1, 5>>  TRUE
<<1, 5>>  TRUE

"EmptyBig"  TRUE
<<1, 5>>  TRUE
<<1, 5>>  TRUE
"TypeOK"  TRUE
<<1, 0>>  TRUE   得到新状态<<1, 0>>

"EmptySmall"  TRUE
<<1, 5>>  TRUE
<<1, 5>>  TRUE

==== 5.1 从sq中取出第一个状态<<2, 0>>，开始计算Next
"FillSmall"  TRUE
<<2, 0>>  TRUE
<<2, 0>>  TRUE

"FillBig"  TRUE
<<2, 0>>  TRUE
<<2, 0>>  TRUE
"TypeOK"  TRUE
<<2, 5>>  TRUE  得到新状态<<2, 5>>

"SmallToBig"  TRUE
<<2, 0>>  TRUE
<<2, 0>>  TRUE

"BigToSmall"  TRUE
<<2, 0>>  TRUE
<<2, 0>>  TRUE

"EmptyBig"  TRUE
<<2, 0>>  TRUE
<<2, 0>>  TRUE

"EmptySmall"  TRUE
<<2, 0>>  TRUE
<<2, 0>>  TRUE

第5轮总结：本轮新增状态 得到新状态<<1, 0>>和<<2, 5>>

========================   开始第6轮 ========================
==== 6.1 从sq中取出第一个状态<<1, 0>>，开始计算Next
"FillSmall"  TRUE
<<1, 0>>  TRUE
<<1, 0>>  TRUE

"FillBig"  TRUE
<<1, 0>>  TRUE
<<1, 0>>  TRUE

"SmallToBig"  TRUE
<<1, 0>>  TRUE
<<1, 0>>  TRUE
"TypeOK"  TRUE
<<0, 1>>  TRUE   得到新状态<<0, 1>>

"BigToSmall"  TRUE
<<1, 0>>  TRUE
<<1, 0>>  TRUE

"EmptyBig"  TRUE
<<1, 0>>  TRUE
<<1, 0>>  TRUE

"EmptySmall"  TRUE
<<1, 0>>  TRUE
<<1, 0>>  TRUE

==== 6.3 从sq中取出第一个状态<<2, 5>>，开始计算Next
"FillSmall"  TRUE
<<2, 5>>  TRUE
<<2, 5>>  TRUE

"FillBig"  TRUE
<<2, 5>>  TRUE
<<2, 5>>  TRUE

"SmallToBig"  TRUE
<<2, 5>>  TRUE
<<2, 5>>  TRUE

"BigToSmall"  TRUE
<<2, 5>>  TRUE
<<2, 5>>  TRUE
"TypeOK"  TRUE
<<3, 4>>  TRUE 得到新状态 <<3, 4>> 
```

## 从时序的角度看TLA的实行过程

```
Next == A \/ B \/ C 
```

TLC使用宽度遍历：
1. 第1层遍历后得到的时序是：T1 = A 或 B 或 C；
2. 第2层遍历是基于第1层时序的：T2 = T1 x (A B C)，也就是 T2 = AA 或 AB 或 AC 或 BA 或 BB 或 BC 或 CA 或 CB 或CC；
3. 第3层遍历是基于第2层时序的：T3 = T2 x (A B C)，也就是 T3 = AAA ABA ACA BAA BBA BCA CAA CBA CCA  | AAB ABB ACB BAB BBB BCB CAB CBB CCB  | AAC ABC ACC BAC BBC BCC CAC CBC CCC

可以看到，TLC会遍历所有可能出现的时序组合。对于一个子句来说，可以在任意时刻发生这个动作。