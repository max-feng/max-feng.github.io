---
layout: post
title: Consensus On Transaction Commit
summary: Paxos和事务提交相结合解决2PC中的单点故障，容忍半数coordinator故障，同时理论上将延时降低和2PC一致
tags: [ 2PC, 3PC, Paxos, Commit, paper ]
---

## 1. 分布式事务介绍

分布式事务是在多个节点上执行一序列操作，这些操作后紧跟着一个操作，标记要么commit，要么abort。各个节点执行事务提交协议来决定这个事务是应该commit还是abort。事务能够提交当且仅当所有的节点都同意提交。在分布式系统中实现这种all-or-nothgin的原子性是不实际的。

经典的事务提交协议是2PC：使用一个单一节点的coordinator（协调者）来达成一致。一旦协调者出现故障，会阻塞整个2PC的执行。我们使用Paxos一致性算法，通过多个协调者来实现分布式事务的提交，同时性能上达到理论上的最优值。它能够保证只要多数派协调者正常工作，分布式事务的提交就可以正常的执行下去。

算法模型
 - Compute model：假设算法是在多个进程上执行，进程之间通过交互消息进行同步，进程通过持久化避免failure；
- Cost model：计算节点之间的消息交互，消息延迟，持久化的写延迟。假设同一节点上进程之间的消息延迟可以忽略不计；
- Failure model：节点和进程failure；消息丢包重发乱序；
- 拜占庭：不处理比特反转等拜占庭错误；

一般一个算法的正确性包括两个方面：safety和liveness
- Safety：描述算法哪些行为是允许发生的（达成的commit之后不能丢失）；
- Liveness：描述算法哪些行为是一定要发生的（比如最终会达成commit）；



## 2. 事务提交

在分布式系统中，事务是有一组运行在不同节点上的resource manager执行(简称RM)。当某个RM发射commit或者abort请求后事务就执行结束了。当且仅当所有的RM都同意执行commit，事务才得以commit，否则事务就abort了。事务的最基本的特性是所有的RM要么全部同意commit，要么全部同意abort，这也是事务的一个不变式。
在工程实践中，一个RM必须先加入事务的运行过程。假设参与事务的RM数目是固定的。
假设所有的RM开始的状态是'working'，算法的目标是所有的RM要么全部是'committed'，要么全部是'aborted'状态。

算法的Safety体现在：
- Stability： 一旦一个RM进入comitted或者aborted状态，这个RM就一直停留在这个状态上；
- Consistency：不存在一个RM是commited状态，另一个RM是aborted状态；

此外，RM还有一个prepared状态：
- 一个RM要进入committed状态，当且仅当所有的RM都进入过prepared状态。

事务最终进入commit，须经过以下时序：
- 所有的RM以任意顺序进入prepared状态；
- 所有的RM以任意顺序进入committed状态；


事务最终进入abort，须经过以下时序：
- 任意RM在working状态可以进入aborted状态；

当一个RM发现不能完成自己的那部分事务时就进入abort状态。

![image-20180810104719095]({{ site.url }}/images/2018-08-10-paxos-commit-2-rm-state.jpg)

另外，FLP定理指出在一个确定的纯异步的环境下是不可能达成stability和consistency，所以本算法假设消息是最终在一定时间内可达到的。事务提交协议的Liveness如下：
- Non-Triviality：如果在算法执行过程中网络没有故障，那么：
    1. 所有的RM都会进入prepared，然后都会进入committed；
    2. 某个RM进入aborted，其他的RM最终都会进入aborted；
- Non-Blocking：任意时刻，只要有足够多的网络节点不发生故障，那么所有RM的最终要么是committed要么是aborted；足够多是保证一个消息的response最终能够达到。

用TLA+精确地定义事务提交。两个状态谓词：
1. canCommit：为TRUE的条件是对于任意一个RM要么是prepared要么是committ；
2. notCommitted： 为TRUE的条件是没有RM是committed；

next-state描述任意RM所有可能的状态转换：
1. Prepare：任意RM可以从working状态进入prepared状态；
2. Decide：对于任意RM，
   a）如果在prepared状态并且此时的canCommit为TRUE，那么这个RM就可以进入committed状态；
   b）如果RM在working或者prepared并且此时的notCommitted为TRUE，那么就进入aborted状态；

   

## 3 Two-Phase Commit
### 3.1 2PC协议
2PC提交协议是一个事务提交协议，通过一个TM做为协调者来推动所有的RM在事务提交协议上的前进。TM的状态有：
1. init；
2. preparing；
3. committed；
4. aborted；


2PC算法流程：
1. 某个RM进入prepared状态，并给TM发送prepared消息；
2. TM进入preparing状态并向其他RM发送prepared消息；
3. RM收到prepared消息后，如果此时是working状态，则进入prepared状态，并给TM回prepared消息；
4. 如果TM收到的所有RM消息都是prepared，则进入committed状态，并给所有的RM发送committed消息；
5. 否则，TM进入aborted状态，并给所有RM发送aborted消息，RM收到aborted消息后进入aborted状态；

![image-20180810113345344]({{ site.url }}/images/2018-08-10-paxos-commit-3.1-2pc-flow.jpg)

像其他的异步算法处理failure一样，2PC执行过程中，发送任意消息前都会把当前状态持久化。比如TM收到一个prepared消息后，先持久化prepared状态在介质上，然后在内存中进入prepared状态。当发生failure，TM重启后从介质上读取到之前的状态，并继续执行2PC算法。理论上，宕机和机器pause是等价的。

### 3.2 2PC的复杂度
事务提交协议复杂度的重要指标是算法在正常运行到committed状态的消息数。
1. 初始RM给TM发送prepard消息 (1 message)；
2. TM给其他RM发送prepared消息 (N-1message)；
3. 每个RM给TM回复prepared的response消息 (N-1 message)；
4. TM给所有的RM发送Committed消息 (Nmessage)；

可以看到：

- ***一个RM要进入Committed状态需要经过4个relay***；
- 总共有3N-1消息被发送；
- 如果TM和发起2PC的RM在同一个node上，可以省掉TM和这个RM的2个消息，那么总共有3N-3个。

### 3.3 2PC的问题
2PC算法可以正确的处理RM的failure。比如：算法执行过程中，某个RM宕机，TM必须等到所有RM的回复才能做出决定，那么此时的TM会因为收不到RM的响应而超时，TM向所有的RM发送aborted消息。其他的RM进入aborted状态。如果TM发生了failure，所有的RM收不到aborted消息或者committed消息，就不知道如何进行下去了，TM阻塞了2PC的运行。

非阻塞的事务提交协议：即使TM出现failure，也不阻塞事务的运行。这些协议称为3PC，通常在一个TM出现failure后，选择另外一个TM继续执行协议。然后，这些3PC的正确性都没有得到证明。



## 4. Paxos Commit
### 4.1 Paxos一致性算法
paxos算法是多数派算法，算法保证最多只有一个v最终choosen出来。在节点数为2F+1的集群中，可以容忍F个节点failure。算法也分成两个阶段：
1. Phase 1a： leader选择一个ballot来构造prepare消息进行广播，期望获得其他acceptor节点授权对该ballot的执行权利；
2. Phase 1b： acceptor收到prepare消息后
	a. 如果没有把执行权承诺给更大的ballot，就承诺给当前这个ballot，并持久化ballot，承诺后续不在接受比ballot小的执行权，同时返回此时acceptor已经接受的v；
	b. 否则，就拒绝这个balotl的执行权；
3. Phase 2a：leader在收到多数acceptor的响应后，两种可能的结果
	a. Free：没有任何acceptor发出过phase2本消息，也就是目前为止没有choosen一个v；此时，leader可以发射出自己v，通常选择client发过来的第一个v；
	b. Forced：某些acceptor曾经发出过2b消息，那么选出最大ballot对应的v；此时的这个v可能已经达成了一致意见，leader能做的就是帮助其他acceptor也对这个v达成一致意见。使用v发射请求；
4. Phase 2b：当acceptor收到<balotl, v>，如果没有承诺过比ballot更大的执行权，就执行这个<ballot, v>；否则忽略；
5. Phase 3： 当leader收到多数派的Phase2b响应后，就可以得出结论：v已经被多数派达成一致意见；

当ballot=0时可以跳过phase1，因此不会有比ballot=0更小的v达成一致意见。此时直接发送自己的v。phase1的作用有两个：
1. 得到ballot的执行权；
2. 得到此时可能已经达成一致的v；
paxos算法可以从两方面优化：
1. phase 2a消息只发送到多数派上；
2. phase 2b消息直接回给client；

### 4.2 Paxos Commit
在2PC的算法中TM会出现单点故障。可以借助多副本的一致性算法，TM充当client对要做出的决定（committed/aborted）发射出proposal，一致性算法最终决议出一个值。Mohan, Strong, and Finkelstein提出了同步算法，TM等待所有的RM回复prepare消息后再发射proposal。但是，等待RM回复给TM消息要多一个消息的延迟。下面讨论Paxos Commit算法是如何消除掉这个消息延迟的。

Paxos Commit算法使用独立的Paxos instance，即每个RM对应一个Paxos instance，都可以独立的发出committed/aborted的proposal。最终只有当所有instance被choosen的值都是committed，事务才会被committed。这种每个RM一个instance的想法可以应用到所有的一致性算法上，但是如何优化时延就和具体的算法息息相关了。

Paxos Commit算法使用2F+1个acceptors和一个current leader。所以，Paxos Commit算法的角色有：
1. N个RM；
2. 2F+1个acceptor；
3. 一个leader；
我们假设RM知道所有acceptor的信息(比如IP)。Paxos算法中ballot=0的phase2a消息可以选定任意的v。通常是由leader发送phase2a消息，显然，可以通过事先选定任意角色发送phase2a消息，Paxos算法任然能够正确运行。在Paxos Commit中，RM各自发送phase2a消息，选定的value为committed或者aborted。
![image-20180813113951090]({{ site.url }}/images/2018-08-10-paxos-commit.jpg)

Paxos Commit算法的执行过程如下：
1. 任意一个想要进行事务提交的RM发送BeginCommit消息给leader；
2. leader向所有其他RM发送Prepare消息；
![image-20180820003332021]({{ site.url }}/images/2018-08-10-paxos-commit-4.2-1.jpg)	
3. 如果RM决定要参与这个事务的commit，就发送<phase2a ballot=0 value=Prepared>消息给所有的acceptor；
![image-20180820003504656]({{ site.url }}/images/2018-08-10-paxos-commit-4.2-2.jpg)
4. 否则，RM发送<phase2a ballot=0 value=Aborted>消息给所有的acceptor；
5. acceptor每收到phase2a消息，都向leader回复phase2b消息（*Paxos Commit算法比其他算法优化的地方*）；
![image-20180820003632772]({{ site.url }}/images/2018-08-10-paxos-commit-4.2-3.jpg)
6. leader可以知道：对于某个RM的instance，如果收到了F+1个phase2b的回复，而且这些回复的value是一致的，那么根据Paxos算法，就可以认为choosen了一个值；
7. 如果leader确定了所有RM的instance值，并且全部都是Prepared，则事务可以提交，leader向所有的RM发送commit消息，促使RM进入committed；
![image-20180820003721347]({{ site.url }}/images/2018-08-10-paxos-commit-4.2-4.jpg)
8. 如果leader确定了所有RM的instance值，并且有一个是Aborted，则事务可以放弃执行，leader向所有的RM发送abort消息，促使RM进入Aborted；

上述算法还有优化的空间：
1. acceptor可以将所有的phase2b消息打包一次性发给leader；
2. acceptor可以将phase2b消息直接发给RM，RM替代leader的角色，这样可以减少延迟，但是增加了总的消息数目；
3. 如果acceptor收到过abort的phase2a消息，可以忽略其他消息，直接通知leader或者RM进入aborted状态；

每个RM的instance在ballot=0的消息中可能达不到choosen状态，leader会因为超时，主动使用更大的ballot执行phase1a的流程。如果leader执行到phase2a阶段时，发现没有任何value（可能RM网络分区导致发给acceptor的<phase2a, ballot=0>的消息没有达到，或者其他什么原因），则尝试让Aborted达成choosen，一旦决定这样做，RM曾经发给acceptor的<phase2a, ballot=0>消息就会被拒绝掉。
leader的超时处理必须是发送aborted消息，因为，在leader超时时可能有RM发送给某个acceptor的abort消息刚刚达到，而没有达成choosen状态。此时leader恰好超时，但是没有收到这个acceptor的phase1b消息。

### 4.3 The Cost of Paxos Commit
下面计算Paxos Commit算法在事务最终达成commit的消息数目：
1. 事务发起者RM发送一个BeginCommit消息 (1个)；
2. leader向其他RM发送Prepare消息(N-1个)；
3. 每个RM广播<phase2a, ballot=0>消息，fast paxos只需要发送F+1个 N(F+1)个；
4. acceptor打包发送phase2b给acceptor (F+1个)；
5. leader广播最终的committed或者aborted消息（N个）；

最终，***RM要经历5个消息延迟得知事务是被committed还是aborted***。总的消息数目是(N+1)(F+3)-2个。如果第一个RM和leader在同一个node上可以节省一个消息，另外，第一个RM可以把BeginCommit消息和phase2a消息打包，又能节省一个消息，那么一共是N+1)(F+3)-4个。如果acceptor个数比RM多，每个acceptor和RM部署在一起，那么每个RM广播phase2a消息时，发到本node上的消息就可以省略了，那么又能节省出F+1个，最终剩下N(F+3)-3个。

如果phase2b消息直接发给RM，那么可以节省一个消息延迟，只要4个延迟就能完成事务提交。但是会多出N(F+1)个消息。

从磁盘写入的次数上，Paxos Commit中一个acceptor可以把多个RM的多个instance一次性打包写盘。

![image-20180816140955213]({{ site.url }}/images/2018-08-10-paxos-vs-2pc-msg.jpg)


## 5 Paxos Commit和 2PC Commit的角色对比

在2PC中TM可以单独决定是commit还是abort，在做出决定之前把状态存入本地的磁盘中，当TM宕机会阻塞整个2PC协议的运行。Paxos算法可以对一个值进行一致性决议，本质上Paxos Commit是把2PC中TM的存储替换成Paxos中的acceptor的存储，把TM替换成leader。另外，Paxos Commit做了延迟优化。但是，Paxos Commit中的leader不能单方面的决定abort，leader必须要走一遍标准的Paxos协议的prepare+accept两阶段把abort值进行一遍决议。

![image-20180816142449305]({{ site.url }}/images/2018-08-10-role-paxos-vs-2pc-role.jpg)

## 6 Transaction Creation and Registration
前面讨论的是固定数目的RM参与单个事务的Paxos Commit算法。在真实系统中往往是先创建一个事务，然后RM加入。下面介绍如何在参与事务RM成员数目固定的算法基础上，修改以支持可变数目RM的事务算法。

为了支持可变RM数目的事务，引入一个registrar角色。registrar地位和RM类似，做为一个额外的RM，记录参与事务的RM集合。不同的是registrar在Paxos协议中的输入是一个RM集合，而不是commit/abort。同样的，给registrar也分配一个Paxos实例。

一个事务提交的条件是：
1. regstar选定一个RM集合，并且在leader上达成一致；
2. RM集合中每个RM对应的Paxos实例都choosen出Prepared；

### 6.1 Transaction Creation
每个节点本地都有启动一个transaction service。通过这个service，RM可以创建和管理事务。创建事务的时候，service构造出descriptor，包含：uid，registrar，initial leader，其他候选leader，acceptors。
该事务的整个执行期间的消息都会带上descriptor，这样接收者可以从descriptor找到对应的事务，以及后续要给哪些进程发送消息。

### 6.2 Join a Transaction
一个RM要加入事务，需要先向registrar发送join消息。join消息需要包含事务的descriptor，因为registrar可能是第一次收到这个事务的descriptor。创建事务的RM向其他参与者广播descriptor。
registrar收到join消息后，把RM加入事务的RM集合，同时回复ack。RM收到ack后表明该RM就是事务的参与者之一了。

### 6.3 Committing a Transaction
事务的发起者RM向registrar发送BeginCommit，而不是向leader发送，因为registrar知道所有事务的参与者。紧接着registrar向所有其他事务的参与者RM发送Prepare消息，同时，拒绝后续参与这个事务的join消息，因为此时事务已经开始了。

registrar在收到BeginCommit后，要进行参与事务RM集合的决议。descriptor中包含了RM集合和acceptors，因此registrar只需要向acceptor发送包含RM集合的phase2a消息，前面提到过registrar也对应一个Paxos实例。如果registrar的实例choosen失败，leader也会发送Abort消息，帮助这个registrar的Paxos实例运行到终点。

### 6.4 Learning the Outcome

acceptor出现故障是很容易理解的，因为acceptor之间运行的是Paxos协议，在2F+1个acceptor的集群中，可以容忍F个故障。只要有多数派的acceptor正常工作，Paxos Commit协议就可以正常运作，这也是算法的设计目标。

如果一个节点P在只有事务descriptor的情况下是如何学习到事务最终是committed还是aborted了呢？descriptor中包含了所有可能的Leader，任意进程P可以向所有可能的leader发送该事务的descriptor询问事务的执行结果。如果所有的leader都故障了，P必须等待至少一个leader恢复。否则，正常运行的leader会返回事务结果给P。

然而可能出现没有一个leader知道事务的执行结果。需要运行标准Paxos协议的Learning过程。此时任意选择一个leader L，L使用一个新的ballot执行registrar的Paxos实例，直到达到choosen状态。如果达成的状态是abortd则终止事务，否则L就得到了一个参与事务的RM集合。L开始进入Paxos Commit流程，使用新的ballot给每个参与事务的RM执行一个Paxos实例，如果最终所有的RM都达到了Prepared状态，则L就学习到了’事务可以提交‘的这一结果。L就可以把这个事务的结果通知给其他进程。
这个过程也可能出现失败，比如由于网络分区，选取出了两个不同的leader，这两个leader同时发送给acceptor，出现踩踏问题，但是Paxos算法可以保证最终只能一个一致的结果。只要只有一个Leader在Learning，最终就能保证一定学习到事务执行的结果。

2PC的Learning过程是非常简单的，TM同时扮演者acceptor，leader，registrar角色。任意进程P想要知道事务的执行结果，只要给TM发送消息即可。如果TM故障了，只能等待别无他法。

如果RM或者事务的发起者Leader失败了，事务提交协议就暂时hang住了。只要有进程使用上述过程尝试学习该事务的执行结果，都会推动事务的继续前进。比如，RM在发送phase2a消息后，超时了没有收到后续的消息。RM尝试向Leader学习事务的执行结果，Leader使用新的ballot运行标准paxos协议发送phase2a消息，最终Leader学习到所有RM的状态，然后回复给这个RM。

## 7 总结
2PC是经典的事务提交协议，也被称为是同步的协议，因为2PC是不能容错的，一旦TM出现故障其他RM必须同步的等TM恢复过来。
Paxos Commit引入了多个TM，只要多数派正常运行，就不会阻塞事务提交协议的运行。
在正常failure-free的场景下，Paxos Commit只比2PC多一个消息时延，在经过Fast Paxos优化后，这个多出来的消息时延也可以被消除掉。理论上达到了非阻塞协议的最小时延。


## 8 TLA+代码
作者附带了TLA+的形式化描述，并没有包含failover相关的逻辑。通过tla+也能进一步精确的了解算法。

```matlab
----------------------------- MODULE PaxosCommit ----------------------------
EXTENDS Integers

Maximum(S) == 
  LET Max[T \in SUBSET S] == 
        IF T = {} THEN -1
                  ELSE LET n    == CHOOSE n \in T : TRUE
                           rmax == Max[T \ {n}]
                       IN  IF n \geq rmax THEN n ELSE rmax
  IN  Max[S]

CONSTANT RM,             \* The set of resource managers.
         Acceptor,       \* The set of acceptors.
         Majority,       \* The set of majorities of acceptors
         Ballot          \* The set of ballot numbers

ASSUME  \* We assume these properties of the declared constants.
  /\ Ballot \subseteq Nat
  /\ 0 \in Ballot
  /\ Majority \subseteq SUBSET Acceptor
  /\ \A MS1, MS2 \in Majority : MS1 \cap MS2 # {}


Message ==
  [type : {"phase1a"}, ins : RM, bal : Ballot \ {0}] 
      \cup
  [type : {"phase1b"}, ins : RM, mbal : Ballot, bal : Ballot \cup {-1},
   val : {"prepared", "aborted", "none"}, acc : Acceptor] 
      \cup
  [type : {"phase2a"}, ins : RM, bal : Ballot, val : {"prepared", "aborted"}]
      \cup
  [type : {"phase2b"}, acc : Acceptor, ins : RM, bal : Ballot,  
   val : {"prepared", "aborted"}] 
      \cup
  [type : {"Commit", "Abort"}]
  
-----------------------------------------------------------------------------
VARIABLES
  rmState,
  aState,
  msgs

PCTypeOK ==  
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ aState  \in [RM -> [Acceptor -> [mbal : Ballot,
                                      bal  : Ballot \cup {-1},
                                      val  : {"prepared", "aborted", "none"}]]]
  /\ msgs \in SUBSET Message

PCInit ==
  /\ rmState = [rm \in RM |-> "working"]
  /\ aState  = [ins \in RM |-> 
                 [ac \in Acceptor 
                    |-> [mbal |-> 0, bal  |-> -1, val  |-> "none"]]]
  /\ msgs = {}
  
Send(m) == msgs' = msgs \cup {m}

RMPrepare(rm) == 
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ Send([type |-> "phase2a", ins |-> rm, bal |-> 0, val |-> "prepared"])
  /\ UNCHANGED aState
  
RMChooseToAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ Send([type |-> "phase2a", ins |-> rm, bal |-> 0, val |-> "aborted"])
  /\ UNCHANGED aState

RMRcvCommitMsg(rm) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<aState, msgs>>

RMRcvAbortMsg(rm) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<aState, msgs>>
-----------------------------------------------------------------------------
Phase1a(bal, rm) ==
  /\ Send([type |-> "phase1a", ins |-> rm, bal |-> bal])
  /\ UNCHANGED <<rmState, aState>>

Phase2a(bal, rm) ==
  /\ ~\E m \in msgs : /\ m.type = "phase2a"
                      /\ m.bal = bal
                      /\ m.ins = rm
  /\ \E MS \in Majority :    
        LET mset == {m \in msgs : /\ m.type = "phase1b"
                                  /\ m.ins  = rm
                                  /\ m.mbal = bal 
                                  /\ m.acc  \in MS}
            maxbal == Maximum({m.bal : m \in mset})
            val == IF maxbal = -1 
                     THEN "aborted"
                     ELSE (CHOOSE m \in mset : m.bal = maxbal).val
        IN  /\ \A ac \in MS : \E m \in mset : m.acc = ac
            /\ Send([type |-> "phase2a", ins |-> rm, bal |-> bal, val |-> val])
  /\ UNCHANGED <<rmState, aState>>

Decide == 
  /\ LET Decided(rm, v) ==
           \E b \in Ballot, MS \in Majority : 
             \A ac \in MS : [type |-> "phase2b", ins |-> rm, 
                              bal |-> b, val |-> v, acc |-> ac ] \in msgs
     IN  \/ /\ \A rm \in RM : Decided(rm, "prepared")
            /\ Send([type |-> "Commit"])
         \/ /\ \E rm \in RM : Decided(rm, "aborted")
            /\ Send([type |-> "Abort"])
  /\ UNCHANGED <<rmState, aState>>
-----------------------------------------------------------------------------
Phase1b(acc) ==  
  \E m \in msgs : 
    /\ m.type = "phase1a"
    /\ aState[m.ins][acc].mbal < m.bal
    /\ aState' = [aState EXCEPT ![m.ins][acc].mbal = m.bal]
    /\ Send([type |-> "phase1b", 
             ins  |-> m.ins, 
             mbal |-> m.bal, 
             bal  |-> aState[m.ins][acc].bal, 
             val  |-> aState[m.ins][acc].val,
             acc  |-> acc])
    /\ UNCHANGED rmState

Phase2b(acc) == 
  /\ \E m \in msgs : 
       /\ m.type = "phase2a"
       /\ aState[m.ins][acc].mbal \leq m.bal
       /\ aState' = [aState EXCEPT ![m.ins][acc].mbal = m.bal,
                                   ![m.ins][acc].bal  = m.bal,
                                   ![m.ins][acc].val  = m.val]
       /\ Send([type |-> "phase2b", ins |-> m.ins, bal |-> m.bal, 
                  val |-> m.val, acc |-> acc])
  /\ UNCHANGED rmState
-----------------------------------------------------------------------------
PCNext ==  \* The next-state action
  \/ \E rm \in RM : \/ RMPrepare(rm) 
                    \/ RMChooseToAbort(rm) 
                    \/ RMRcvCommitMsg(rm) 
                    \/ RMRcvAbortMsg(rm)
  \/ \E bal \in Ballot \ {0}, rm \in RM : Phase1a(bal, rm) \/ Phase2a(bal, rm)
  \/ Decide
  \/ \E acc \in Acceptor : Phase1b(acc) \/ Phase2b(acc) 
-----------------------------------------------------------------------------
PCSpec == PCInit /\ [][PCNext]_<<rmState, aState, msgs>>


THEOREM PCSpec => PCTypeOK
-----------------------------------------------------------------------------
TC == INSTANCE TCommit

THEOREM PCSpec => TC!TCSpec
=============================================================================

```
