书籍《函数式程序设计与证明》的Isabelle/HOL源码

https://www.yuque.com/zhaoyongwang/fpp/

请使用Isabelle 2021版本，每章节的代码对应关系如下：


第1章 函数式程序设计简介

1.3 函数式和指令式的排序算法

1_Intro/func_imp_compare.thy

第4章 Isabelle程序设计基础

4.1 Isabelle程序的基本结构

2_functionalprog/FirstExample.thy

4.2 基本类型

4.3 函数类型和函数定义

4.4 表达式

2_functionalprog/BasicDef.thy

第5章 类型构造

2_functionalprog/Types.thy

第6章 集合与关系

2_functionalprog/Set_Relation.thy

第7章 函数的特征与运算

2_functionalprog/Function.thy

第8章 递归函数

2_functionalprog/Recursion.thy

第9章 高阶函数

2_functionalprog/Highorder_Func.thy

第10章 函数式列表

2_functionalprog/Listprog.thy

第11章 模块化结构与复用

11.2 区域（Locale）

2_functionalprog/Locale.thy

11.3 类（Class）

2_functionalprog/Classes.thy

11.4 程序的引入

2_functionalprog/imports/*.thy

第12章 通用代数结构

2_functionalprog/AlgebraicStructure.thy

第15章 Isabelle证明方法和语言

3_Proof/Tutorial.thy

第17章 栈和队列

17.1 栈Stack

4_ds_algo/Stack_Queue/stack.thy

17.2 有界栈Bounded Stack

4_ds_algo/Stack_Queue/BoundedStack.thy

17.3 FIFO队列

4_ds_algo/Stack_Queue/Queue.thy

17.4 优先级队列Priority Queue

4_ds_algo/Stack_Queue/PriorityQueue.thy

第18章 多重集合

Isabelle2021\src\HOL\Library\Multiset.thy


第19章 排序

19.2 插入排序

4_ds_algo/Sorting/InsertSort.thy

19.3 快速排序

4_ds_algo/Sorting/Quicksort.thy

19.4 冒泡排序

4_ds_algo/Sorting/Bubblesort.thy

19.5 归并排序

4_ds_algo/Sorting/MergeSort.thy

第21章 二叉查找树

21.1 基本二叉树

4_ds_algo/bintree/Tree.thy

21.2 二叉查找树

4_ds_algo/bintree/Tree_Set.thy

第22章 AVL平衡二叉树

4_ds_algo/bintree/AVL_Set.thy

第23章 堆

4_ds_algo/bintree/Leftist_Heap.thy

第24章 图

24.1 图的定义与性质

https://www.isa-afp.org/entries/Graph_Theory.html

24.2 深度优先搜索

https://www.isa-afp.org/entries/Depth-First-Search.html

24.3 最短路径

https://www.isa-afp.org/entries/Dijkstra_Shortest_Path.html

第五部分 语言的设计与可信编译

5_IMP


