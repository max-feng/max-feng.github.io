---
layout: post
title: PostgreSQL 并行hashjoin 源码解读
summary: PostgreSQL的并行hashjoin使得多个进程并发的scan表，并发的build hash table，并发的join，并且动态的调整负载
tags: [ PostgreSQL, hash join,  paper ]
---


# PostgreSQL的并行查询简介

并行查询是 PostgreSQL 的一个大特性，对于单一sql查询，从传统单一进程，提升到多个进程协同完成。

并行查询使用了更多的cpu/mem/io资源，提高了任务的执行效率，在cpu=8以内执行效率线性增长。

并行查询设计的难点是需要协调多个worker进程间的同步：

1）在barrier点上多个进程需要全部前进到这个点上，比如：build inner hash table，必须等该状态完成了，所有的worker才能往下走；

2）在达到barrier点之前，多个进程的工作量尽量按照‘能者多劳’，执行快的进程多做一些工作量，比如：scan，build hash table，probe等；

3）此外，实现上要避免死锁，避免内存分配碎片，处理进程出错；

本文主要讲述并行查询中最复杂的功能：paralle hash join。先从单进程的hashjoin逐步过渡到多进程并行的hashjoin。

从9.6和10版本就开始支持并行join，但是只支持outer table的并行；11版本支持outer和inner都并行执行；



# 并行hashjoin的执行计划

## 一个例子

```sql
select count(*)
  from lineitem
  join orders on l_orderkey = o_orderkey
 where o_totalprice > 5.00;
```



### 10版本的并行hash join计划

```
 Finalize Aggregate
   ->  Gather
         Workers Planned: 2
         ->  Partial Aggregate
               ->  Hash Join
                     Hash Cond: (lineitem.l_orderkey = orders.o_orderkey)
                     ->  Parallel Seq Scan on lineitem
                     ->  Hash
                           ->  Seq Scan on orders

                                 Filter: (o_totalprice > 5.00)
```

过程是：

1）每个worker扫描全部的inner table；
2）在各自的私有内存中build一个hash表；
3）每个worker并行的扫描outer table，并行执行join的probe；

### 11版本的并行hash join计划

```
 Finalize Aggregate
   ->  Gather
         Workers Planned: 2
         ->  Partial Aggregate
               ->  Parallel Hash Join
                     Hash Cond: (lineitem.l_orderkey = orders.o_orderkey)
                     ->  Parallel Seq Scan on lineitem
                     ->  Parallel Hash
                           ->  Parallel Seq Scan on orders
                                 Filter: (o_totalprice > 5.00)
```

过程是：

1）每个worker并行扫描部分inner table（涉及parallel seq scan）；
2）在共享内存中并行的build一个hash表；
3）每个worker并行的扫描outer table，并行执行join的probe；


# hashjoin的设计

## 单进程hashjoin的时间线：

![join]({{ site.url }}/images/2019-12-18-postgres-parallel-hashjoin-single-worker.png)

1）先扫描inner table；
2）建立hash表；
3）在扫描outer table；
平均总的执行时间 = inner plan(扫描+build) + outer plan

## outer表并发执行的时间线
在Postgres10中，每个worker进程都各自在自己的私有内存中建立inner表的hash，然后并发的扫描outer表，并执行join。

下图是3个worker并发执行的时间线。

如前面所说，每个worker完整的执行inner plan，在各自的私有内存build hash table，outer table是并行的扫描，每个worker扫描一部分，并执行join，这样所有worker的结果集的并集就是最终的结果集。

![join]({{ site.url }}/images/2019-12-18-postgres-parallel-hashjoin-3-inner.png)


只对outer plan进行了并行化。该方法适用于nner table很小的时候。它的问题是：
1）仅仅对子系统进行优化；
2）每个worker内都有一份inner table的拷贝，浪费了内存；
阿姆达尔定律指出：对系统中的一个子系统优化改进，受限于可使用该优化方法的时间占比。说白了是顶了天了优化的效果最多是把该被优化的子系统降到接近0。
但是该定律的重要性是说明了：收益递减。要把一个子系统优化从80%优化到40%付出的代价是变多的。

上图中，worker2执行的比较慢，总的执行时间可能取决于worker2，但是也可能worker1和worker3在执行outer plan进行并行的join时适当的多干些活。

平均总的执行时间 = iner plan + (outer plan / worker_num)
## inner和outer都并行执行的时间线
该方案是Posrgres11中的并行hashjoin算法。

inner plan也被多个worker并行执行，在共享内存中进程安全的build出一个共享的hash table。

注意点是：在进行join之前，要等待所有的worker都把inner plan执行完成，也就是要build出一份完成的hash table。因此图中的虚线是所有worker进程的barrier点，只有等所有的进程都达到了虚线，才能继续下面的步骤。

这是通过pg的barrier机制实现。

![join]({{ site.url }}/images/2019-12-18-parallel-hashjoin-3-inner-3ouer.png)

在build hash tabl阶段，worker2执行的慢，该阶段的执行速度也不一定取决于最慢的worker，同理，worker1和worker3可能会多干些活。但是一定要满足在barrier处等待所有的woker都完成build阶段；
平均总的执行时间 = (inner plan + outer plan) / worker_num

从中可以看出，Postgres社区对并行执行方案的演进路径：现在Postgres10版本并行化了outer plan，稳定后，再在Postgres11版本并行化inner plan。

## multi-batch机制
不论是并行的hashjoin还是单进程的hash join都要解决inner table在内存装不的问题。
解决方法是：
1）建立多个batch；
2）对inner table进行分片，分片的临时数据写入相应batch下的小文件；
3）在逐个batch的build hash table和join；

单进程multi-batch

### 并行化multi-batch+只并行outer

![join]({{ site.url }}/images/2019-12-18-parallel-hashjoin-multi-batch-3-inner.png)

每个worker在扫描inner table时做2件事情：
1）扫描inner table：

​	a） 对属于batch-0的tuple，直接在内存中构建hash table，和上面讲的单个batch相同；

​	b）对不属于batch-0的tuple，写入相应batch的inner tuple文件；

2） 并行扫描outer table：直接写入相应batch的outer tuple文件；

3）依次遍历每个batch；

4）把属于该batch的inner tuple文件加载到内存中（batch-0除外，因为它已经在内存中了）；

5）在该batch内，执行单进程的join的逻辑；

为了避免多个worker同时往一个batch写文件加锁的问题，每个batch给每个worker都分配一个inner文件和outer文件。



### 并行化multi-batch+同时并行outer和inner


![join]({{ site.url }}/images/2019-12-18-parallel-hashjoin-multi-batch-3inner-3outer.png)

1）并行扫描并行扫描inner table，属于batch-0的tuple直接在内存中构建一个shared hash table，不属于的写入对应batch的inner tuple文件；
2）并行扫描outer table，写入对应batch的outer_tuples文件；
3）并行的对batch-0执行join；
4）woker1和worker2先完成batch-0的join任务后，分别领取batch1和batch2的join；
5）worker3执行batch3的join；
6）worker1和worker2并行的执行batch4，也是build一个shared hash table，同样需要barrier；
7）worker3只能领取最后的batch5;
8）当worker1和worker2完成了对batch4的join后，会attach到batch5上，3个worker并行的执行；

对于batch-5：

1）开始只有worker3处理；

2）后面worker-1和worker-2也加入进来，3个进程一起处理；



attach的细节：先对batch5进行处理的worker3可能build完hash table，也可能没有。因此内部维护了一个简单的状态机：
1）如果没有build 完成，这个时候worker1和worker2加入进来（也可能只有worker1进来了）那么在加进来的worker并行的build hash table，在join之前必须barrier；
2）如果已经build完成了，那么无需barrier；
3）实现的关键在barrier的相关模块中，每个worker加进来执行attach时，barrier中维护计数，在需要等待的地方判断计数是否归零，没有看到归零的进程等待，直到计数为0；

# 总结并行hash join的效果
## 在内存能装下inner table的场景

![join]({{ site.url }}/images/2019-12-18-parallel-hashjoin-3-inner-3ouer.png)

## 在内存装不下inner table的场景

![join]({{ site.url }}/images/2019-12-18-parallel-hashjoin-multi-batch-3inner-3outer.png)

可以看到，该方案最大程度的进行并发，’能者多劳‘，不让进程闲着。动态的分配扫描任务，既可以batch内部并行执行，也可以batch之间并行执行。

# 如何实现并行hashjoin

先来比较下单进程版的hashjoin和并行的hashjoin的区别

![join]({{ site.url }}/images/2019-12-18-postgres-parallel-hashjoin-single-multi-batch.png)

![join]({{ site.url }}/images/2019-12-18-parallel-hashjoin-multi-batch-3inner-3outer.png)


# 并行hash join的实现

## hash join 的 plan node

![join]({{ site.url }}/images/2019-parallel-hashjoin-plan-node.png)

在hash join中关键数据结构是HashJoinState和HashState。
HashJoinState对应的exec函数是ExecHashJoinImpl负责维护驱动整个join的过程：

驱动inner plan；

驱动outer plan；

probe；

HashState的exec函数是MultiExecParallelHash，负责并行的build inner表。


## 进程模型

![join]({{ site.url }}/images/2019-12-18-parallel-hashjoin-process-mode.png)

1）处理psql连接的进程做为leader进程；

2）leader进程负责估算大小并初始化DSM；

3）把用户sql的plan tree和其他参数序列化到DSM中；

4）Postgres提供的bgworker机制来启动n个worker：在全局的BackgroundWorkerlist上添加一些node，然后给PostMaster进程发信号，由PostMaster进程来启动worker，参数是DSM的handler；

5）每个worker都attach到DSM，并从ParallerWorkerMain函数开始，反序列plan tree；

6）每个worker执行plan tree，具体进入到parallel-aware的算子；



## 内存管理

![join]({{ site.url }}/images/2019-12-18-postgres-parallel-hashjoin-memory-layout.png)

PostgreSQL是多进程的模型，进程间通过share memory来通信。pg在启动时申请一大片固定的share memory，在这片内存上分配大概50多个结构体以及buffer。每当有新连接进来时就fork一个新的进程，这个进程和main进程共享这些内存。

基于多进程共享内存的编程范式：
1）首先由leader进程分配出共享内存（比如：mmap），返回handle指针；
2）每个worker进程创建私有的xxxDesc结构体；
3）worker进程attach上来，xxxDesc指向handle，注册一些回调函数，refcnt++等；

### dsm

对于并行查询，多个worker间需要通信，但是需要的内存量是不确定的。pg提供动态的创建共享内存机制(dsm)给并行查询分配内存。

并行查询的leader进程负责创建dsm，follower进程attach上去，attach动作是为了生成一个私有的dsm描述符，并把dsm中的refcnt加1。

### dsa
dsm机制是通过系统调用（linux平台是mmap）来分配出来的内存，不支持小内存分配；而且如果在dsm上分配几个有关联关系的的小对象是有问题，比如：
strct A {
    B *b;
}
dsm在每个进程上的地址空间是不同，指针b的地址是创建该dsm的进程锁看到的地址，为了解决这两个问题，提供dsa机制：
1）在dsm上分配小块内存；
2）通过dsa_pointer描述结构体之间的引用关系；dsa_pointer本质上是一个相对hanle指针的偏移量；

### batch内部的内存

![join]({{ site.url }}/images/2019-12-18-postgres-parallel-hashjoin-in-batch-memory.png)


一个batch的构成：

1）ParallelHashJoinBatch结构，管理该batch的基础信息，比如：bucket的个数；

2）两个SharedTuplestore，一个inner table，一个outer table；

3）一个大数组做为hash的表头，长度是bucket个数；

4）一个chunk组成的list，每个chunk的大小是32KB，存储一个个的hashtuple，每个hashtuple都有一个头部，在hash表中存的是这个hashtuple的dsa_pointer；

在插入bucket时，通过对buckets[bucketno]的head进行cas，实现线程安全的hash inert。

```
	for (;;)
	{
		tuple->next.shared = dsa_pointer_atomic_read(head);
		if (dsa_pointer_atomic_compare_exchange(head,
												&tuple->next.shared,
												tuple_shared))
			break;
	}
```



### 并行的build inner hash table

![join]({{ site.url }}/images/2019-12-18-postgres-parallel-hashjoin-build-inner-table.png)

1）每个worker并行的扫描inner table；

2）把tuple写入到batch中对应的inner tule文件里，每个worker都有一个文件；

3）对于attach上去的batch则是直接写入内存；

这样图是不精确的，worker1和worker2都应该attach到batch-0上：一边扫描一遍插入batch-0的内存，其他的batch则是写入文件，这样总的内存使用量就是一个bath了，因为batch的引入本来就是为了解决内存不足的问题。



### 并行hashjoin的状态机

![join]({{ site.url }}/images/2019-12-18-postgres-parallel-hashjoin-state-machine.png)

实现并行hashjoin算法的函数是在ExecHashJoinImpl里，这个函数同时实现了单进程版本的hashjoin和并行版本的 hashjon算法。

BUILD_HASHTABLE状态：

​	在MultiExecParallelHash函数中；

​	2）并行的build inner hash table，写入inner tuple文件；

HJ_BUILD_HASHING_OUTER状态：

​	1）这个状态是在build inner之后，所有worker从barrier上detach下来，自动++phase得来的；

​	2）所有的woker并行扫描；

​	3）写入对应的batch的outer_tuples文件；

​	4）到这一步，除了batch0，inner tuple文件和outer tuple文件已经就位；

HJ_NEED_NEW_BATCH状态：

​	1）ExecParallelHashJoinNewBatch函数；

​	2）每个worker选择一个batch，直到所有batch完成：

​			a）给这个batch在dsa上分配bucket（batch0除外）；

​			b）等待所有woker完成分配内存；

​			c）把该batch上的inner文件中的tuple加载该batch的hashtable中；

​			d） 选定一个batch开始处理，其他的batch可能还没有开始处理：

HJ_NEED_NEW_OUTER状态：

​	1）每个worker从自己负责的batch中读取outer tuple文件；

​	2）当自己的batch中所有outer tuple文件处理完毕后，再次回到HJ_NEED_NEW_BATCH，挑选下一个batch处理；

HJ_SCAN_BUCKET状态：

​	1）执行hash查找；

​	2）当执行完成后，回到HJ_NEED_NEW_OUTER状态，处理下一个outer tuple；

HJ_FILL_OUTER_TUPLES状态：

​	外连接，需要填充所有的outer，因此需要回到OUTER

HJ_FILL_INNER_TUPLES状态：

​	内连接，需要填充所有的inner，因此需要回到NEW_BATCH；



并行的关键是：每次一个worker处理完一个batch后，都回到HJ_NEED_NEW_BATCH去领取下一个batch，如果当前只剩下一个batch了，那么所有的workerattach上去并行的处理。

# 总结

PostgreSQL的并行hashjoin的演进，体现了复杂feature的迭代过程。多个worker进程通过共享内存‘争抢’一些工作量来处理，‘能者多劳’处理快的worker不会因为得不到任务而处于idle的状态。

并行查询需要高改造10来个算子，使得这些算子感知多进程之间通信，可想代码量是很大的。

可以考虑使用类似gp的motion也许会有意外的收获，只不过gp中节点间是通过interconnect通信，这里通过共享内存通信。

