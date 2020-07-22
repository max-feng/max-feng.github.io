---
layout: post
title: PostgreSQL B+tree索引原理 论文解读
summary: PostgreSQL B+tree索引能够并发的分裂，核心有2个机制：rightlink和highkey
tags: [ PostgreSQL, B+tree, index,  paper ]
---

# 1. 论文背景

PostgreSQL数据库的nbtree索引参考了2篇论文：

* 《Efficient Locking for Concurrent Operations on B-Trees》：高并发读写的原理；
* 《A SYMMETRIC CONCURRENT B-TREE ALGORITHM》：高并发删除的原理；

### B+Tree基础

![ly-1]({{ site.url }}/images/2020-07-18-b+tree.png)

是一种平衡多路搜索树，最大化中间节点数目以减少树的高度，平衡操作不经常发生，减少随机访问，适用于节点间访问时间（从一个page跳到另一个page）远远大于节点内部（解析和二分搜索page内部）的场景，用来组织外部介质上的索引布局。

* 树的高度更少，它的中间节点不存储关键字对应的记录，只存储索引关键字，使得每个中间节点能够最大量的保存关键字；
* 搜索时间恒定，叶子节点保存了所有父节点关键字的记录，每次都要到叶子节点搜索；
* 自带排序，叶子节点之间是有序的，可以支持范围搜索，缓存命中率更高；
* 全表遍历，只需要遍历全部的叶子节点；

上面介绍的只是B+Tree的静态结构，在并发的搜索，插入，删除时如何尽量少的上锁，提高整体的并发度就是本篇论文的核心点。

# 2. 概述

本片论文首次提出了在标准的Btree数据结构基础上，增加两个机制来优化并发读写的性能。

```
1. right link；
2. high key；
```


论文假设所有的buffer都是私有的，可以做到：

* 读操作无需上锁；
* 更新只需要上常量数目的锁；

也称为B-link-Tree（PostgreSQL的buffer是全局的，读需要上读锁。如果产生了页面分裂需要对新页面及其右邻居上锁）

# 3. Btree并发操作的算法演进
在B-link-Tree之前对Btree的并发操作的方法是基于lock-coupling和lock-subtree的算法。就是通过对多个父子节点上锁或者子树上锁，使得search/insert/delete相互隔离，如果串行执行一般。


## lock-coupling(读写隔离)
从父节点到子节点descengding操作需要：先对子节点上锁，再释放当前父节点的锁。
这里，需要同时对父子节点上锁，否则其他writer就可能有机会同时得到这两个锁并完成分裂过程。

![2020-07-18-b+tree]({{ site.url }}/images/2020-07-18-btree-1.1-lock-coupling.png)

一个执行时序：

1. write1开始执行search(d)搜索；
2. writer1对父节点进行的搜索，发现需要进入‘abd’的子节点进行搜索；
3. writer1释放d的锁；
4. writer2执行insert(c)操作；
5. writer2上锁'd'节点成功；
6. writer2上锁‘abd'节点成功；
7. writer2对’abd‘进行了分裂，产生了’ab','cd'两个节点；
8. writer1再去原来'abd'页面上搜索'd'时就找不到了；

## lock-subtree(写写隔离)
writer操作需要对subtree上锁，理论上锁的最小粒度是在他们的公共祖先地方上锁，达到写写互斥。分裂的过程是自底向上进行的，writer1对一个节点n上锁并且更新了，此时writer2可能已经在这个子树下面它最终也要修改n，如果不在subtree地方上锁，当一个writer1修改了n，另外一个自底向上后发现n已经变化了，导致插入的地方不对。
lock-subtree本身是比较难以实现的，一个最直观的做法是对root节点上锁，但是这样就彻底阻止其他的操作了，尤其是并发的lock-coupling，更加剧了冲突。

## optimitic descending(乐观更新)
writer过程中对中间节点上读锁，对真正要更新的叶子节点上写锁，如果最终没有发生分裂或者合并，则更新成功，否则需要从root开始执行lock-subtree算法。

## update during decending(自上向下更新)
避免了lock-subtree，在更新操作的descending过程中，同时对节点重构。过程中仍然需要lock-coupling。

## Lehman and Yao 提出的B-link-tree算法

LY算法的思想是不通过锁来互斥btree的操作（lock-coupling和lock-subtree），而是允许btree操作并发的进行，通过其他手段来恢复出btree的结构。

### B-link-tree
这是LY的原创发明，B+tree每个节点都额外增加一个‘rightlink’指向它的右邻居节点。允许btree的操作并发执行，后续再根据rightlink来复原出完整的btree。

比如，分裂操作分成2个阶段：

1. 水平操作：将原节点n分成n和n'，将key也分成两拨，同时节点n指向节点n'；
2. 垂直操作：将新的节点n'插入父节点中；

![2020-07-18-b+tree]({{ site.url }}/images/2020-07-18-btree-1.2-split.png)

在1和2之间允许其他进程从父节点进行搜索，进入节点n，如果：

1. 目标key在节点n中，则搜索n后返回；
2. 目标key在n'中，通过节点n跳到n'中搜索；

lock-coupling不需要了，因为通过父节点descend到子节点的过程中，如果有对子节点进行的分裂没有即使在插入父节点，导致错误的进入了左子节点，此时只需要通过rightlink往右搜索就能找到正确的子节点；
lock-subtree不需要了，因为在ascend到父节点中进行插入新的n'时，此时如果父节点也发生了分裂，导致进入了错误的父节点，那么只需要通过rightlink往右搜索就能找到正确的父节点；

B-link树允许插入和搜索只对一个page上（这里有个假设，所有的page直接从磁盘上读取到自己进程的local buffer中。PostgreSQL中B-link树的page读取到shared buffer中被所有进程共享，因此它需要锁住更多的页面。这是由具体的工程实现导致的，并非算法本身的要求）。

# 4. LY算法的存储模型和数据结构
database存储在磁盘上，多个进程并发的行为是：
1. 读取存储介质上的page到local buffer中；
2. 进程查找，修改；
3. 写入磁盘上；
page的读写是原子的。允许进程对磁盘的page上锁（可以在共享内存中实现一个page descriptor结构）。

## 符号
小写字母：标记内存中的变量，比如x, t；
大写字母：内存中的page，比如A, B, C；
lock(x)：对x指向的page上锁；
unlock(x)：对x指向的page释放锁；
A <- get(x)：读取x执行的page到内存A中；
put(A, x)：将内存中A的内容写入到x指向的page；

```
典型的修改page x的过程：
lock(x);
A <- get(x);
modify A;
put(A, x);
unlock(x);
```


## 数据结构
![2020-07-18-b+tree]({{ site.url }}/images/2020-07-18-btree-1-data-struct.png)

## highkey
每个节点额外增加一个highkey，代表该节点所有子树的upper bond。
原来2k个key不能表达upper bond吗？从上面的结构能够看出来，默认2k个key对应2k+1个子树，最右侧的子树它的upper bond并没有记录。

![2020-07-18-b+tree]({{ site.url }}/images/2020-07-18-btree-1-data-struct-highkey.png)

## 插入操作
1. 如果叶子节点的key entry少于2k个，直接插入；
2. 如果叶子节点已经有2k个key，那么需要把原来的节点拆成2个，key集合也要分成2个，然后再把新的key插入到左或右节点中。
	1. 左节点的highkey需要重新选出一个大概在1/2的位置；
	2. 新节点的highkey就是原来节点的highkey；
3. 对中间节点的插入过程类似，唯一不一样的是中间节点的指向的是其他索引节点而不是记录；

下图：插入'47'后，导致分裂。并且在父节点中插入了'51', '51'正好是左节点的highkey。
![2020-07-18-b+tree]({{ site.url }}/images/2020-07-18-btree-1-data-struct-split.png)

## 一个简单的并发场景

![2020-07-18-b+tree]({{ site.url }}/images/2020-07-18-btree-2-search15-split9.png)

在lock-coupling中提到的一个时序：

1. 进程1执行搜索15，在把x读取到了内存中，得到y的指针，暂停执行；
2. 进程2执行插入9，读取x，得到指针y，读取y，并分裂出了y'，并把y'指针插入到了父节点x中；
3. 进程1恢复执行，在读取y，找不到15；

出错的本质原因是：进程1通过x得到了指针y，然后读取y，在这连个操作之间进程2修改了y；

## 5. LY算法并发操作原理

### rightlink
rightlink的本质是提供一个除了左右指针之外的访问节点的途径。

**被split出来的两个node通过rightlink连接，在父节点加入对新节点的索引前，他们如同一个node一样。**

*加入了rightlink后，对于任意节点（除最左侧和root节点之外）都有2个指针指向它：一个是父节点，一个是左邻居节点。当一个新节点插入时，这两个指针中要有一个原子的指向它（减小上锁），最合适的指针当然是左邻居节点在分裂的时候顺便指向它（本来左邻居节点就是要更新它自己的内容）。
这样， 新节点没有父节点，只有一个左邻居节点指向它，此时的btree仍然是合法的搜索树，因为新节点里的键值能够通过左边节点找到它。另外，新节点应尽快的的在父节点中插入，以提高查询效率，否则通过左节点绕一圈需要多读取一次page。*


### highkey

如何识别出当前节点在搜索的过程中产生了分裂了呢，当然可以每次在搜索当前节点失败时，尽量的尝试在'right link'节点中搜索一次，这样需要多读取n次page，而且分裂对于搜索来说并非是常态。

**如果从父节点descend到子节点A的搜索key > A的highkey，则一定发生了分裂。**

*当进程1搜索父节点时，节点A发生了分裂，新分裂出来的节点B还没来得及插入到父节点中，进程1根据错误的'downlink‘（分裂之前节点A在父节点的highkey）进入到了老的A节点，而A节点的highkey在分裂时发生发生了变化，从downlink追随过来的highkey比节点A上看到的highkey要大，说明从父节点descend到子节点过程中一定发生了分裂。*



## search
该算法仅仅是一个并发search的说明，没有显示的上锁，是因为每次都从盘上读取page到自己私有的buffer中。而一个数据库中为了减少读取的次数，读取page到共享buffer中，因此需要对共享的buffer上一次读锁，仅此而已，无需对父节点上锁；

```
procedure search(u)
current <- root;
A <- get(current);
while current is not a leaf do
begin
	current <- scannode(u, A);
	A <- get(current) 
end;

while t <- scannode(u, A) = link ptr of A do
begin
	current <- t ;
	A <- get(current);
end;

if v is in A then done “success” else done “failure”
```

## insert
首先通过search(u)找到待插入的叶子节点，然后对这个节点上锁。在search的过程中需要记录从root到叶子节点的backtrack路径，因为插入叶子节点会导致分裂，需要在父节点插入新的highkey，继而又可能会导致父节点也发生了分裂，直到遇到了一个无需分裂的祖先节点，因此需要记录这条路径。

注意，在通过backtrack自底向上插入时，某个祖先节点也可能发生了分裂，导致backtrack中记录的节点已经不是原来的那个节点了，祖先节点是否发生分裂也可以通过比较highkey判断，如果发生了分裂，则一直往右边查找，直到找到了待插入的祖先节点。

![2020-07-18-b+tree]({{ site.url }}/images/2020-07-18-btree-5-data-struct-splitting.png)
如图：

1. 找到待分裂的节点a；
2. 新分配一个节点b'，b'指向原来a的rightlink；
3. 更新a的内容为a'（键值的个数接近原来的1/2，pg是按照长度来划分)，并且a'指向b'；
4. 更新父节点f'指向b‘；

```
procedure insert(u)
initialize stack;
current <- root;
A <- get(current);

while current is not a leaf do 
begin
	t <- current;
	current <- scannode( v, A);
	if new current was not link pointer in A then
		push(t);
	A <- get(current);
end;

lock(current); //找到了待插入的叶子节点
A <- get(current);
move.right;

if v is in A then stop “v already exists in tree”;
w <- pointer to pages allocated for record associated with v;

Doinsertion:
if A is safe then //无需分裂
begin
	A <- node.insert(A, w, v);
	put(A, current);
	unLock(current);
end else begin
	u<- allocate(1 new page for B);
	A, B <- rearrange old A, adding v and w, to make 2 nodes,
		where (link ptr of A, link ptr of B) <- (u, link ptr of old A);
	y <- highkey stored in new A; //节点A的highkey
	put(B, u); //先把新节点B写入磁盘
	put(A, current); // 第二步更新current节点
	oldnode <- current; // 开始插入父节点
	v <- y;
	w <- u;
	current <- pop(stack); // 从栈中取出父节点
	lock(current);
	A <- get(current);
	move.right; // 尝试向右移动找到正确的父节点
	unlock(oldnode); // 更新父节点前解锁子节点
	goto Doinsertion
end

```

**在发生分裂时，逻辑上是向右侧分裂。过程中新的page在左边，原来的page在右侧，这是为了插入父节点时，仅需插入<左侧节点的highkey, 左侧节点指针>， 无需操作右侧节点，因为它在父节点中本来的kv就是对的。**

当发生分裂时，最多对3个节点上锁：

1. 当前节点；
2. 	父节点；
3. 父节点的右邻居节点；


上锁的必要性：

1. 为什么在move.right时，需要对2个相邻节点上锁？从一个节点跳转到右边节点间隙不发生并发的分裂（如果分裂，那么通过左边节点得到右节点的指针就变成了并发当前的右节点，因为中间插入了新的节点）；
2. 为什么在找到正确的父节点前，需要对子节点上锁呢？同时，在从子节点进入父节点间隙中，其他进程可能对子节点再次进行了分裂，它的highkey就会发生变化；


# 6.正确性论证

## 没有deadlock

上锁的顺序：

1. 同一个层次，从左向右；
2. 跨层次，自底向上；


证明：只需要证明在这个树中所有节点间都有"<"的关系(全序关系)：

1. 不在同一个层上的两个节点a和b，"a < b"当且仅当level(a) < level(b)；
2. 在同一个层上的两个节点a和b，"a < b"当且仅当a在b的左边；

归纳法，假设t0时刻满足"a > b"，那么任意t > t0时刻始终满足 "a > b"。
由于分裂是向右侧进行，并且从节点x分裂出来x'和x''是紧跟在原来节点的后面，因此：

```
对于所有y，y < x，满足 y < x';
对于所有y，x < y，满足 x'' < y;
分裂之前小于x的还是小于，大于x的还是大于，因此节点之间仍然符合全序关系。
```

另外，插入过程中上锁顺序遵循全序关系：对节点A上锁了，就不会对它的子节点上锁，只会对父节点上锁；邻居节点的上锁也只对右节点上锁。

分裂的性质和插入时上锁的顺序，保证了：

1. 进程P1在t0时刻对(a,b)上锁；
2. t1时刻，其他进程上锁的顺序也是(a,b)，而不是(b,a)；

因此，不会产生死锁。

## insert的正确性
为了保证tree的结构在任何时刻都是一致的，对所有可能修改树的操作进行论证。实际上插入操作无论是否分裂，最终都是通过"put"写入磁盘，插入操作有3个地方调用了put:

1. "put(A, current)"， 对没有分裂的节点，直接写入磁盘；
2. "put(B, u)"，对于分类的节点，将新产生的节点写入磁盘；
3. "put(A, current)"，对于分类的节点，对左边的节点写入磁盘，实际上覆盖写，同时原子的修改了rightlink指向了步骤2中新产生的节点；

注意通过加锁，执行完步骤2立即执行步骤3，对于breee来说，这两次写可以规约到一次原子写。

```
LEMMA: 两次写磁盘操作"put(B, u), put(A, current)"，等价于对btree的一次修改。
```

证明过程也很显而易见，

1. 先分配新的节点B，同时B指向原来A的右节点；
2. 更新节点A内容时，同时指向了新的节点B，这是一个原子操作，既成功的修改了A，又把B引入了btree中；

因此，可以证明：

```
ThEOREM：作用在btree上的所有操作时刻维护btree的一致性
```

根据LEMMA的论证，分裂时的2次写磁盘对于btree来说等价于一次，同时，修改btree时上了一次锁，因此分裂不会破坏btree的一致性。


## insert时并发search的正确性

### Type1 中间节点没有分裂
1. 进程1在底层发生了分裂，在父节点插入新节点的kv，该父节点没有分离；
2. 进程2在进程1插入父节点前读取到了这个中间节点，它看不到新增的子节点，会找到左子节点，可以通过左子节点的rightlink找到新增的节点；

### Type2 叶子节点发生分裂
1. 进程1在底层发生了分裂，在父节点插入新节点的kv，该父节点也发生了分裂；
2. 进程2在进程1分裂父节点前读取到了这个中间节点，它可能在这个节点上搜索不到，需要往右移动到叔父节点，最终通过叔父节点找到了原来的左节点（成功的对叔父节点上锁，说明上一轮分裂已经完成），进入到下一层节点，该节点可能再次发生了分裂，因此仍然需要往右移动；

### Type3 backtrack
当子节点发生了split，而需要在父节点插入时，从stack中取出父节点，进行backtrack，此时该父节点可能已经发生了多次split，通过right pointer依次向右查找到真正需要插入的叔父节点；

在父节点分裂的同时，子节点分裂出来的靠右节点的key，也在父节点这一层逐步的往右移动；
而对父节点的插入是左子节点的high value，该值在父节点一系列的右指针中是可达的；

#### Type4 锁等待
进程P在search到要修改的节点后，进行lock时，会等待，因为进程I正在持有锁，并进行修改该node；等到进程I释放锁后，进程P得到锁，此时的node已经不是需要修改的node了（被进程I改过后进行了split），此时进程P需要move.right，找到需要修改的节点；

**每一次获得锁之后的第一件事情就是move.right；**

## 7. 活锁
某个插入进程P执行的比较慢，而其他进程执行的快，一直有右指针诞生，P一直在向右查找；
可以通过进程优先级解决cpu快慢问题；

# 8. DELETION
删除只发生在叶子节点上，删除过程也需要上锁，允许叶子节点的key个数少于k个。这对于insert远比delete大的场景是可以接收的。
如果delete操作也很频繁，可以通过锁住整个树，然后进行批量的delete操作。

# 9. LOCKING EFFICIENCY
```
LY算法中的锁：插入时至少一个锁，如果发生了分裂则3个锁。
```
3个锁分别是：

1. 当前被分裂的节点；
2. 在上一层中查找正确的父节点时，对父节点上锁；
3. 对父节点右邻居上锁；

# 10. 结束
LY算法从理论上设计了一个高并发的B-link-tree结构，最多只需要3个锁。
然而在实践中，仅有该算法还远远不够。比如在PostgreSQL中还需要考虑：

1. key可能是不唯一的；
2.  key的长度是变长的；
2. page在共享内存中，可以被多个进程看到，因此search的时候也需要上读锁；
3. 需要支持双向遍历（从右往左），因此需要维护rightlink和leftlink，由此会引入更复杂的锁管理；
4. root的分裂；




