## 1. 分区表

### 1.1 概述

分区表（Partitioned Table）是数据库中的一种技术，用于将一张大表的数据按一定的规则拆分成多个较小的物理存储单元，这些物理存储单元被称为分区（Partition）。每个分区保存表的一部分数据（每个分区可以独立存储和操作）。

![image-20250512001137976](assets/image-20250512001137976.png)

逻辑上，分区表仍表现为一个完整的表进行访问，但数据根据指定的规则（分区键）分布在不同的分区中存储。

每个分区都有自己的名字并可以拥有不同的存储特性，例如可以将分区保存在不同的磁盘以上分散I/O，或者分散在不同的表空间。

![image-20250512142024363](assets/image-20250512142024363.png)

向分区表插入数据时，为了判断每条数据应该被分配至哪个分区，我们通常需要选择定义一个分区键（Partition Key）。根据每条数据分区键的值或者对其运算的结果来决定数据的分区归属，分区键可以由1或多个列组成（最多16个列）。

**分区表的优势：**

1. 性能优化

   - 分区剪裁（Partition Pruning）：查询时自动跳过无关分区，减少扫描的数据量。
   - 并行处理（Parallel Execution）：不同分区可并行操作，提升查询和DML效率。

2. 管理便捷性

   - 数据维护灵活：可单独对某个分区进行备份、恢复、索引重建等操作。
   - 生命周期管理：轻松归档或删除历史数据（如按月删除旧分区）。

3. 高可用性

   - 分区独立性：单个分区损坏不影响其他分区的可用性。

   

**小结：**

- 表分区：将一个表中的数据按照"规则"拆分到不同的分区表中存储。
  - 逻辑上统一、物理上拆分存储。

- 将表中数据拆分的规则就是`分区键`。就是根据分区键决定表中的数据行，属于哪一个分区的，在执行DML操作时，会根据分区键选择分区。



### 1.2 分区策略

根据不同的应用场景，可以为表选择不同的分区策略：

| 分区类型             | 描述                                 | 适用场景                                             |
| -------------------- | ------------------------------------ | ---------------------------------------------------- |
| 范围分区 (Range)     | 按分区键值的范围划分（如日期、数值） | 时间序列数据<br />例：订单表按月份分区）             |
| 列表分区 (List)      | 按分区键的离散值划分（如地区、状态） | 数据有明显分类<br />例：按国家、产品类型分区         |
| 哈希分区 (Hash)      | 通过哈希函数均匀分布数据             | 数据分布均匀，避免热点<br />例：无明确业务逻辑的分区 |
| 复合分区 (Composite) | 结合两种分区（如先范围再哈希）       | 多层次管理<br />例：按年分区后再按地区哈希分布       |



### 1.3 分区表的创建

#### 1.3.1 范围分区

范围分区：根据预先定义的范围来划分分区，范围分区最适合管理类似且有明显顺序的数据，根据数据的顺序可以很容易划定分区范围。范围分区最典型的应用场景就是按时间对数据进行分区，所以其经常使用时间类型的分区键。

语法： 分区表使用范围分区(Range Partitioning)

~~~plsql
-- 按日期范围分区
CREATE TABLE 表名 (
    字段名1  数据类型,
    字段名2  数据类型,
    ................
    字段名N  数据类型
)PARTITION BY RANGE(时间类型字段名) (
  PARTITION 分区名1 VALUES LESS THAN (TO_DATE('年-月-日','yyyy-mm-dd')),
  PARTITION 分区名2 VALUES LESS THAN ('年-月-日'),  
  PARTITION 分区名3 VALUES LESS THAN (MAXVALUE)  
);
~~~

- `PARTITION BY RANGE(分区字段)` 意思是按范围分区，以指定`分区字段`下的数据做为分区依据。
- `PARTITION 分区名` 指定当前分区的名字。
- `VALUES LESS THAN(...)` 当前分区下存储的数据是以小于`分区字段`下的`xxxx`值为依据规则 。
- `MAXVALUE` 所有超出已定义范围的数据都会自动落入这个分区，避免数据插入失败。
  - 本质上，`MAXVALUE` 是一个"兜底"分区，保证未明确划分的数据也有存储空间。

示例：创建范围分区表（按年份）

~~~postgresql
-- 按年份进行表分区
CREATE TABLE employee (
    empno bigint PRIMARY KEY,
    ename varchar2(20),
    job varchar2(20),
    hiredate date,
    sal number(11,2),
    comm number(11,2),
    deptno int
) PARTITION BY RANGE (hiredate) (
    partition p2023 values less than ('2024-01-01'),
    partition p2024 values less than ('2025-01-01'),
    partition pmax values less than (maxvalue)
);
~~~

- 解释说明：按照`hiredate`字段进行分区
  - 所有`hiredate`小于`2024-01-01`的数据(**不包含**)被分配到分区`p2023`中
  - 所有`hiredate`小于`2025-01-01`的数据(不包含)被分配到分区`p2024`中
  - 所有`hiredate`大于等于`2025-01-01`的数据被分配到分区`pmax`中
    - 如果没有`pmax`这个分区，那么插入的数据大于等于`2025-01-01`时，会因为没有合适的存储分区而报错

示例：创建范围分区表（按数值）

~~~plsql
create table employee(
    empno bigint PRIMARY KEY,
    ename varchar2(20),
    job varchar2(20),
    hiredate date,
    sal number(11,2),
    comm number(11,2),
    deptno int
) partition by range(deptno)(
    partition p1 values less than (2),
    partition p2 values less than (3),
    partition p3 values less than (4),
    partition pmax values less than (maxvalue)
);
~~~



#### 1.3.2 查询分区表

在GaussDB数据库中分区表创建好之后，可以通过数据库内置的系统表查看相关分区表信息。

- `pg_class` 和 `pg_partition` 均为 内置的系统表，用于存储数据库对象的元数据信息。

~~~plsql
-- pg_class   记录数据库中所有表、索引、视图、序列等关系型对象的结构信息
SELECT oid, relname, parttype FROM pg_class WHERE relname = 'employee';
~~~

- 执行结果：

  ![image-20250512195415253](assets/image-20250512195415253.png)

~~~plsql
-- pg_partition  记录分区表的分区定义、分区结构信息。
SELECT oid, relname, parttype, parentid FROM pg_partition WHERE parentid = 57433;
~~~

- 执行结果：

  ![image-20250512195517004](assets/image-20250512195517004.png)

- `parttype`取值及含义：

  - `r（Root Partition）`：根分区，表示这是一个分区表的顶层分区结构（即分区表本身）。
  - `p（Partition）` ：中间子分区，表示该分区是子分区表中的父节点。
  - `s（Leaf Partition）`：叶子分区，表示实际存储数据的分区。每个叶子分区对应一个物理存储单元。



#### 1.3.3 列表分区

列表分区的特点是某列的值只有几个，基于这样的特点我们可以采用列表分区。例如：按照地域来分类、按照职位来分类等。

列表分区表是通过`PARTITION BY LIST`子句来创建的，创建时需要为每个分区指定一个列表。

语法：

~~~plsql
CREATE TABLE 表名 (
    字段名1  数据类型,
    字段名2  数据类型,
    ................
    字段名N  数据类型
)PARTITION BY LIST (分区字段) (
  PARTITION 分区名1 VALUES ('分区字段下值1','分区字段下值3'),
  PARTITION 分区名2 VALUES ('分区字段下值2','分区字段下值4'),
  PARTITION 分区名3 VALUES ('分区字段下值5'),  
  PARTITION 分区名4 VALUES (DEFAULT)  -- 未匹配到的数据 
);
~~~

- 插入数据的分区键值不在列表范围内，且存在 `DEFAULT` 分区，则这些数据会被自动存入 `DEFAULT` 分区；**若没有 `DEFAULT` 分区，插入不存在于列表范围内的数据时会直接报错**。

示例：按照员工职位实现分区

~~~plsql
-- 按职位分区
CREATE TABLE employee(
    empno bigint PRIMARY KEY,
    ename varchar2(20),
    job varchar2(20),
    hiredate date,
    sal number(11,2),
    comm number(11,2),
    deptno int
) PARTITION BY LIST (job)(
    partition p_1 values ('CLERK','ANALYST'),
    partition p_2 values ('SALESMAN'),
    partition p_other values (default)
);
~~~



#### 1.3.4 哈希分区

哈希分区是对指定的分区键（Partition Key）运行哈希算法来决定数据存储在哪个分区。哈希分区会随机的将数据分配到各个分区中，并尽量平均，保证各个分区的大小差不多一致。

由于数据是随机分布，所以哈希分区并不适合管理有明显时间顺序的历史数据。它更适合需要将数据平均的分布到各个不同存储设备上的场景。同时在选用哈希分区时建议满足下列条件：

1. 选取分区键时尽量选取唯一列（Unique）或列中有大量唯一值（Almost Unique）的列。
2. 创建哈希分区时，分区的数量尽量是2的倍数，例如：2、4、8、16等。

哈希分区表是通过 `PARTITION BY HASH` 子句来创建的，创建时指定每个分区名称及所属表空间。

语法：

~~~plsql
CREATE TABLE 表名 (
    字段名1  数据类型,
    字段名2  数据类型,
    ................
    字段名N  数据类型
)PARTITION BY HASH (分区字段)(
    partition p1 [tablespace 表空间1] ,
    partition p2 [tablespace 表空间2]
);
~~~

示例：按照员工编号哈希分布存储数据到4个分区

~~~plsql
CREATE TABLE employee(
    empno bigint PRIMARY KEY,
    ename varchar2(20),
    job varchar2(20),
    hiredate date,
    sal number(11,2),
    comm number(11,2),
    deptno int
) PARTITION BY HASH (empno)(
    PARTITION p1,  -- 分区1
    PARTITION p2,  -- 分区2
    PARTITION p3,  -- 分区3
    PARTITION p4   -- 分区4
);
~~~



#### 1.3.5 复合分区

所谓复合分区其实就是在一个分区的基础上再次分区(子分区)。通过任意两种基础分区策略组合使用。

示例：

~~~postgresql
-- 先按年份范围分区，再按职位列表子分区
CREATE TABLE employee (
    empno bigint PRIMARY KEY,
    ename varchar2(20),
    job varchar2(20),
    hiredate date,
    sal number(11,2),
    comm number(11,2),
    deptno int
)
PARTITION BY RANGE (hiredate)  -- 先按照日期进行范围分区 
SUBPARTITION BY LIST (job)   -- 再按照职位进行列表分区
(
    PARTITION p_2023 VALUES LESS THAN (TO_DATE('2024-01-01', 'YYYY-MM-DD')) 
    (
        SUBPARTITION p_1 values ('CLERK','ANALYST'),
        SUBPARTITION p_2 values ('SALESMAN'),
        SUBPARTITION p_other values (default)
    ),
    PARTITION p_max VALUES LESS THAN (MAXVALUE)
);
~~~



小结：

分区表通过逻辑统一、物理分离的设计，显著提升大数据环境下的查询效率和管理灵活性。正确选择分区策略（如范围、列表、哈希等），结合分区剪裁和并行处理，可有效应对数据增长带来的性能挑战。合理设计分区键、控制分区数量，并配合本地索引使用，是发挥分区表优势的关键。





## 2. 电商销售分析系统

### 2.1 项目背景

在当今数字化时代，电商行业发展迅猛，某电商公司在市场中占据一定份额，业务规模不断扩大，销售渠道日益丰富，涵盖了自营网站、第三方电商平台等多个渠道。随着业务的增长，公司积累了大量的销售数据，这些数据分散在不同的系统和数据库中，包括订单系统、库存系统、客户关系管理系统（CRM）等。

公司管理层意识到数据对于业务决策的重要性，希望通过对销售数据的深入分析，了解销售趋势、客户行为、产品表现等信息，以便制定更精准的营销策略、优化产品库存管理、提升客户满意度和提高公司的整体竞争力。然而，由于数据的分散性和不一致性，以及不同系统之间的数据格式和结构差异，使得数据的整合和分析变得非常困难。

为了解决这些问题，公司决定建立一个基于Gauss数据库的纯数据库方式的 ETL 电商销售分析系统。



### 2.2 项目开发流程设计

![image-20250512230732494](assets/image-20250512230732494.png)

- ODS层原始数据

  ```properties
  名称: 操作型数据存储、源数据层、贴源层、数据暂存层、数据引入层
  
  功能: 此层数据无任何更改，直接沿用外围系统数据结构和数据，不对外开放；为临时存储层，是各个数据源数据的临时存储区域，为后一步的数据处理做准备。
  
  说明: 在大数据的数仓体系中，更多进行的是ELT的操作。因为数据源的数据不出意外几乎都是结构化的数据了，那么不妨首先将数据load加载至数仓，然后经过层层的转换。
  
  实际应用: ODS为数仓中的一个逻辑分层，比如专门创建一个database库，名字叫做ods.存储从各个数据源加载过来的数据，做临时存储。
  ```

- DWD数据仓库层

  ```properties
  名称: 数据仓库层
  
  功能: DW层的数据由ODS层数据加工而成,主要完成数据加工与整合。DW层的数据应该是一致的、准确的、干净的数据。
  
  说明: 实际应用中，为了更加清晰、明了、便捷的开展数据分析，会对DW层进行更加细化的分层。比如：数仓明细层DWD、数仓基础数据层DWB、数仓服务数据层DWS、数据集市层DM、维度数据层DIM
  ```

  - `明细层DWD（Data Warehouse Detail）`：存储明细数据，此数据是最细粒度的事实数据。该层一般保持和ODS层一样的数据粒度，并且提供一定的数据质量保证。同时，为了提高数据明细层的易用性，该层会采用一些维度退化手法，将维度退化至事实表中，减少事实表和维表的关联。
  - `业务层DWS（Data WareHouse Service）`：存储宽表数据，此层数据是针对某个业务领域的聚合数据，为了应用层的需要在这一层将业务相关的所有数据统一汇集起来进行存储，方便业务层获取。

- ADS数据应用层

  ```properties
  名称:数据应用层
  
  功能:面向最终用户，面向业务定制提供给产品和数据分析使用的数据。
  
  常见的数据应用:数据报表 数据可视化 数据挖掘  即席查询
  ```

分层的好处

1. 清晰数据结构
   每一个数据分层都有它的作用域，在使用表的时候能更方便地定位和理解。
2. 数据血缘追踪
   简单来说，我们最终给业务呈现的是一个能直接使用业务表，但是它的来源有很多，如果有一张来源表出问题了，我们希望能够快速准确地定位到问题，并清楚它的危害范围。
3. 减少重复开发
   规范数据分层，开发一些通用的中间层数据，能够减少极大的重复计算。
4. 把复杂问题简单化
   将一个复杂的任务分解成多个步骤来完成，每一层只处理单一的步骤，比较简单和容易理解。而且便于维护数据的准确性，当数据出现问题之后，可以不用修复所有的数据，只需要从有问题的步骤开始修复。
5. 屏蔽原始数据的异常
   屏蔽业务的影响，不必改一次业务就需要重新接入数据。



### 2.3 维度表和事实表

生活中的事例：

~~~properties
假设你开了一家网店，每天都会记一笔账："2025 年 5 月 12 日，小明买了 1 个手机，花了 3000 元，收货地址是杭州"。
~~~

- **事实表**：就像账本里的每一笔 "具体交易记录"，记录 "发生了什么"（买了什么、花了多少钱）。
- **维度表**：就像账本的 "分类标签"，记录 "这笔账的背景信息"（什么时候买的、谁买的、在哪里买的、买的什么东西）。

#### 2.3.1 事实表

**事实表的定义：**

用大白话来讲，就是记录一件事情发生时要存储的数据。这些数据通常是**"定量数据"**（可计算、可汇总的数据）。
比如电商场景中的 **订单事实表**，每一行记录一次交易，包含：

- 订单 ID（唯一标识每笔订单）
- 交易时间（对应时间维度的 ID，比如 "20250512"）
- 用户 ID（对应用户维度的 ID，比如 "用户 101"）
- 产品 ID（对应产品维度的 ID，比如 "产品 2001"）
- 购买数量（1 个）
- 交易金额（3000 元）
- 运费（10 元）

**事实表的特点：**

1. 事实表包含了与各维度表相关联的**外键**，可与维度表**关联**；
2. 表里没有存放实际的内容，是一堆主键的集合，这些主键ID分别能对应到**维度表**中的一条记录；
3. 事实表的度量（指标值）通常是数值类型；
4. 事实表记录数会不断增加，表数据规模迅速增长。

**事实表的作用：**

事实表是数据分析的 "核心"，用来回答 "到底发生了多少事"。
比如：

- 统计 "总销售额"= 所有事实表中的 "交易金额" 相加。
- 统计 "某产品的销量"= 按 "产品 ID" 分组，对 "购买数量" 求和。



#### 2.3.2 维度表

**维度表的定义：**

用大白话来讲，维度就是对所发生事情进行分析的角度。

维度表就是存储使用哪些角度对事情进行分析，通常存储的是"定性数据"（描述性、不适合计算的数据）。
比如：

- 时间维度：年、季、月、日、星期几（如 "2025 年 5 月是第 2 季度"）。
- 用户维度：用户 ID、姓名、年龄、地区、注册时间（如 "小明，25 岁，杭州用户"）。
- 产品维度：产品 ID、产品名称、类别（手机 / 衣服）、品牌、价格区间（如 "手机，华为，高端机"）。
- 地区维度：地区 ID、省、市、区、邮编（如 "浙江省，杭州市，西湖区"）。

> 维度表用来记录业务场景里面有关业务背景信息的表。

**维度表的特点：**

- 字段多是文本或时间：很少有数字（除了用来分类的 ID，比如 "产品 ID=1001"）。
- 数据量小且稳定：比如 "时间维度" 每年就 365 天，"产品维度" 里的品牌很少频繁变动。
- 用来 "筛选" 和 "分组"：比如分析 "2025 年 5 月杭州用户买了多少华为手机"，就需要用维度表来限定范围。

**维度表的作用：**

维度表就像给数据贴了很多 "标签"，让你能从不同角度（时间、用户、产品、地区）分析数据。例如：如果你想知道 "哪个地区的用户最爱买高端手机"，你需要用 "地区维度"（地区信息）和 "产品维度"（是否高端）来筛选和分组数据。



#### 2.3.3 区分维度表和事实表

为什么要区分维度表和事实表？

想象一下：如果所有数据都堆在一张表里（比如订单表直接存用户姓名、地址、产品名称），会有两个问题：

1. 数据重复浪费：比如 "小明" 买了 10 次东西，他的地址会重复存 10 次。
2. 分析效率低：每次筛选 "杭州用户" 都要扫描整个表，速度很慢。

而用维度表和事实表分开后：

- 维度表只存一次 "小明的地址是杭州"，事实表只存 "用户 ID=101"，节省空间。
- 分析时通过 ID 快速关联，就像查字典一样高效。



#### 2.3.4 维度表和事实表的配合

通过 "ID" 关联：

- 事实表里存的是维度表的 ID（比如 "用户 ID=101"），而不是具体的用户姓名、地区。

- 需要分析时，通过 ID 把事实表和维度表 "连起来"，比如：

  ~~~plsql
  事实表（订单） + 用户维度表 = 知道"用户101（小明）"买了什么  
  事实表（订单） + 产品维度表 = 知道"产品2001（华为手机）"卖了多少  
  ~~~

典型场景举例：

- 如果你想知道 "2025 年 5 月，杭州的用户买了多少金额的华为手机"，步骤是：
  1. 从时间维度表找到 "2025 年 5 月" 对应的时间 ID。
  2. 从用户维度表找到 "杭州" 对应的用户 ID 列表。
  3. 从产品维度表找到 "华为手机" 对应的产品 ID。
  4. 到事实表中，筛选出时间 ID、用户 ID、产品 ID 匹配的记录，把 "交易金额" 相加。



#### 2.3.5 小结

| **维度表**                           | **事实表**                                 |
| ------------------------------------ | ------------------------------------------ |
| 存 "背景信息"（标签、分类）          | 存 "具体事件"（可计算的数据）              |
| 字段是文本 / 时间（如 "杭州""手机"） | 字段是数字（如 "1 个""3000 元"）           |
| 数据量小，变化少（比如一年 365 天）  | 数据量大，每天新增（比如每天 10 万条订单） |
| 用来 "筛选" 和 "描述" 数据           | 用来 "计算" 和 "汇总" 数据                 |





### 2.4 数据表

省份表：`province`

~~~plsql
DROP TABLE IF EXISTS province;
CREATE TABLE province(
  prov_id number PRIMARY KEY,
  prov_name varchar2(20),    -- 城市名
  region varchar2(20)        -- 区域
);

-- 数据样本
INSERT INTO province(prov_id,prov_name,region) VALUES (1,'北京','华北');
INSERT INTO province(prov_id,prov_name,region) VALUES (2,'上海','华东');
INSERT INTO province(prov_id,prov_name,region) VALUES (3,'广州','华南');
INSERT INTO province(prov_id,prov_name,region) VALUES (4,'杭州','华东');
INSERT INTO province(prov_id,prov_name,region) VALUES (5,'成都','西南');
~~~

产品表：`product`

~~~plsql
DROP TABLE IF EXISTS product;
CREATE TABLE product(
    product_id      NUMBER PRIMARY KEY,  -- 产品ID
    product_name    VARCHAR2(100),  -- 产品名称
    category        VARCHAR2(50),   -- 分类名
    price           NUMBER(10,2),   -- 单价
    valid_from      DATE,     -- 起始有效期
    valid_to        DATE,     -- 截止有效期
    is_current      CHAR(1),  -- 是否上架
    create_time     DATE      -- 创建日期
);
~~~

用户表：`users`

~~~plsql
DROP TABLE IF EXISTS users;
CREATE TABLE users(
    user_id NUMBER PRIMARY KEY,
    user_name VARCHAR2(30),       -- 用户名
    mobile VARCHAR(11),           -- 手机号
    gender CHAR(3) CHECK(gender IN('男','女')),   -- 性别
    prov_id NUMBER,            -- 城市
    address VARCHAR(200),      -- 地址
    create_time DATE           -- 注册日期
);

-- 数据样本
INSERT INTO users(user_id,user_name,mobile,gender,prov_id,address,create_time) 
VALUES (1,'张三','13800138000','女',1,'北京市海淀区三里屯','2023-08-23');
INSERT INTO users(user_id,user_name,mobile,gender,prov_id,address,create_time) 
VALUES (2,'李四','13800138001','男',2,'上海市长宁区中山西路','2024-02-10');
INSERT INTO users(user_id,user_name,mobile,gender,prov_id,address,create_time) 
VALUES (3,'王五','13800138002','男',4,'杭州市钱塘区11号大街','2024-06-28');
~~~

订单表：`orders`

~~~plsql
DROP TABLE IF EXISTS orders;
CREATE TABLE orders (
    order_id        NUMBER(20) PRIMARY KEY,
    user_id         NUMBER,           -- 用户id
    product_id      NUMBER,           -- 产品id
    order_amount    NUMBER(10,2),    -- 订单金额
    order_status    VARCHAR2(20),    -- 订单状态
    province        VARCHAR2(50),    -- 城市
    create_time     DATE             -- 订单日期
)
~~~

编写PLSQL程序：向数据表插入测试数据

~~~plsql
-- 产品数据生成存储过程
CREATE OR REPLACE PROCEDURE generate_products IS
BEGIN
  FOR i IN 1..20 LOOP
    INSERT INTO product VALUES (
      i,
      '产品'||i,
      CASE MOD(i,4) WHEN 0 THEN '数码' WHEN 1 THEN '服饰' WHEN 2 THEN '食品' ELSE '家居' END,
      TRUNC(FLOOR(random() * 1500 + 50)), 
      SYSDATE - TRUNC(FLOOR(random() * 400 + 1)),
      NULL,
      'Y',
      SYSDATE - TRUNC(FLOOR(random() * 1000 + 1)) 
    );
  END LOOP;
  COMMIT;
END;


-- 生成测试订单数据
CREATE OR REPLACE PROCEDURE generate_orders(p_num NUMBER) IS
BEGIN
  FOR i IN 1..p_num LOOP
    INSERT INTO orders VALUES (
      i,
      TRUNC(FLOOR(random() * 50 + 1)),    -- 用户ID
      TRUNC(FLOOR(random() * 20 + 1)),    -- 产品ID
      ROUND(FLOOR(random() * 5000 + 50),2), -- 订单金额
      CASE TRUNC(FLOOR(random() * 4 + 1)) 
        WHEN 1 THEN 'paid' 
        WHEN 2 THEN 'shipped' 
        ELSE 'completed' END,
     CASE MOD(i,5) WHEN 0 THEN '上海' WHEN 1 THEN '北京' WHEN 2 THEN '杭州' WHEN 3 THEN '成都' ELSE '广州' END,
      SYSDATE - TRUNC(FLOOR(random() * 365 + 1))
    );
    IF MOD(i,10000)=0 THEN COMMIT; END IF;
  END LOOP;
  COMMIT;
END;
~~~



### 2.5 数仓实现

#### 2.5.1 ODS层

![image-20250512230732494](assets/image-20250512230732494.png)

##### 2.5.1.1 创建分区表

基于数据源中的基础表，生成ODS层的分区表，并把基础表中的数据导入到对应分区表。

订单表分区表：按照订单生成日期进行分区

~~~plsql
-- 原始订单表（分区表）
CREATE TABLE ods_orders (
    order_id        NUMBER(20) PRIMARY KEY,
    user_id         NUMBER(10),
    product_id      NUMBER(10),
    order_amount    NUMBER(10,2),
    order_status    VARCHAR2(20),
    province        VARCHAR2(50),
    create_time     DATE
)PARTITION BY RANGE (create_time)(
    partition p2024 values less than ('2025-01-01'),
    partition p2025 values less than ('2026-01-01'),
    partition pmax values less than (maxvalue)
);

-- 创建日期索引
CREATE INDEX idx_ods_createtime ON ods_orders(create_time) LOCAL;
~~~

用户分区表：按照用户注册日期分区

~~~plsql
CREATE TABLE ods_users(
    user_id NUMBER PRIMARY KEY,
    user_name VARCHAR2(30),
    mobile VARCHAR(11),
    gender CHAR(3) CHECK(gender IN('男','女')),
    address VARCHAR(200),
    create_time DATE
)PARTITION BY RANGE (create_time) (
    partition p_2023 values LESS THAN ('2024-01-01'),
    partition p_2024 values LESS THAN ('2025-01-01'), 
    partition p_2025 values LESS THAN ('2026-01-01'),
    partition p_max values LESS THAN (MAXVALUE)
);
~~~

产品表：

~~~plsql
CREATE TABLE ods_product(
    product_id      NUMBER PRIMARY KEY,  -- 产品ID
    product_name    VARCHAR2(100),  -- 产品名称
    category        VARCHAR2(50),   -- 分类名
    price           NUMBER(10,2),   -- 单价
    valid_from      DATE,     -- 起始有效期
    valid_to        DATE,     -- 截止有效期
    is_current      CHAR(1),  -- 是否上架
    create_time     DATE
);
~~~

省份表：

~~~plsql
CREATE TABLE ods_province(
  prov_id number PRIMARY KEY,
  prov_name varchar2(20),
  region varchar2(20)
);
~~~



##### 2.5.1.2 导入数据

把基础表中的数据导入到ODS层对应的数据表中

~~~postgresql
-- 编写存储过程 ： 实现全量数据导入
create or replace procedure proc_db_to_ods()
as 
begin
	-- 全量数据导入：订单表
	insert into ods.ods_orders(order_id,user_id,product_id,order_amount,order_status,province,create_time) 
	select order_id,user_id,product_id,order_amount,order_status,province,create_time
	from public.orders;
    -- 全量数据导入：用户表
    insert into ods.ods_users(user_id,user_name,mobile,gender,address,create_time) 
    select user_id,user_name,mobile,gender,address,create_time 
    from public.users;
    -- 全量数据导入：产品表
    insert into ods.ods_product (product_id,product_name,category,price,valid_from,valid_to,is_current,create_time) 
    select product_id,product_name,category,price,valid_from,valid_to,is_current,create_time 
    from public.product;  
    -- 全量数据导入：区域表
    insert into ods.ods_province (prov_id,prov_name,region) 
    select prov_id,prov_name,region 
    from public.province;
    
    -- 打印输出
    raise notice '向ODS层导入全量数据完成!';
end;


-- 调用存储过程
call proc_db_to_ods();
~~~





#### 2.5.2 DWD层

![image-20250512230732494](assets/image-20250512230732494.png)

DWD层称为：明细数据层。

- 主要功能：==数据清洗转换、提供质量保证==；==区分事实、维度==。

  - 事实表：包含与各维度表相关联的外键和业务过程有关的指标数据(如：数量、订单金额)
  - 维度表：细化指标，对事实数据进行分析的角度

- 表名规范

  - 事实表命名：dwd_fact_xxxxxx   

  - 维度表命名：dwd_dim_yyyyyy

##### 2.5.2.1 创建事实表和维度表

生成订单事实表：`dwd_fact_sales`

~~~plsql
-- 订单事实表
CREATE TABLE dwd_fact_sales (
    order_id        NUMBER(20) PRIMARY KEY,
    product_id      NUMBER,           -- 产品id（维度）
    prov_id         NUMBER,           -- 省份id（维度）
    user_id         NUMBER,           -- 用户id（维度）
    order_date      DATE,             -- 订单日期（分区字段）
    amount          NUMBER(10,2),     -- 订单金额（指标） 
    order_status    VARCHAR2(20)       
)PARTITION BY RANGE (order_date)(
    partition p2024 values less than ('2025-01-01'),
    partition p2025 values less than ('2026-01-01'),
    partition pmax values less than (maxvalue)
);
-- 创建日期索引
CREATE INDEX idx_dwd_orderdate ON dwd_fact_sales(order_date) LOCAL;
~~~

生成区域维度表：`dwd_dim_province`

~~~plsql
CREATE TABLE dwd_dim_province(
  prov_id number PRIMARY KEY,
  prov_name varchar2(20),    -- 城市名
  region varchar2(20)        -- 区域
);
~~~

生成产品维度表：`dwd_dim_product`

~~~plsql
CREATE TABLE dwd_dim_product(
    product_id      NUMBER PRIMARY KEY,  -- 产品ID
    product_name    VARCHAR2(100),  -- 产品名称
    category        VARCHAR2(50),   -- 分类名
    price           NUMBER(10,2),   -- 单价
    valid_from      DATE,     -- 起始有效期
    valid_to        DATE,     -- 截止有效期
    is_current      CHAR(1),  -- 是否上架
    create_time     DATE
);
~~~



##### 2.5.2.2 导入数据

基于`ODS`层向`DWD`层导入数据：

~~~postgresql
-- 编写存储过程
-- 自己写的......
create or replace procedure proc_ods_to_owd()
as 
begin
    -- 数据导入：订单事实表
    insert into dwd_fact_sales(order_id, user_id, product_id, prov_id, order_date, amount, order_status) 
    select oo.order_id,oo.user_id,oo.product_id,op.prov_id,oo.create_time,oo.order_amount,oo.order_status
    from ods_orders oo,ods_province op
    WHERE oo.province = op.prov_name;
    -- 全量数据导入：区域维度表
    insert into dwd_dim_province(prov_id,prov_name,region) 
    select prov_id,prov_name,region
    from ods_province;
    -- 全量数据导入：产品维度表
    insert into  dwd_dim_product(product_id,product_name,category,price,valid_from,valid_to,is_current,create_time) 
    select product_id,product_name,category,price,valid_from,valid_to,is_current,create_time
    from ods_product;  
    
    -- 打印输出
    raise notice '基于ODS层向DWD层导入数据完成!';
end;

call proc_ods_to_owd();
~~~





#### 2.5.3  DWS层聚合

![image-20250512230732494](assets/image-20250512230732494.png)

`DWS层`：存储宽表数据，此层数据是针对某个业务领域的聚合数据，为了应用层的需要在这一层将业务相关的所有数据统一汇集起来进行存储，方便业务层获取。

> ==【说明：后期降维形成宽表会在`DWB`层中实现，现当前案例中暂时放在`DWS`层中完成】==
>
> 注意：在`DWS`层聚合数据时所生成的宽表，为提高查询性能，会对维度表进行弱化(降维)。
>
> - 将各个维度表的核心字段数据汇总到事实表中
>
> 通过退化维度操作之后，带来的显著效果是
>
> - 整个数仓中表的个数减少了；
> - 业务相关联的数据（跟你分析相关的）数据字段聚在一起了，形成一张宽表。
> - 分析查询时的效率显著提高了：多表查询和单表查询的差异。
>
> 带来的坏处是
>
> - 数据大量冗余、宽表的概念已经不符合3范式设计要求了。
> - 但是数仓建模的核心追求是，只要有利于分析，能够加快数据分析，都可以做。

生成日销售汇总表：

~~~plsql
-- 创建销售汇总宽表
CREATE TABLE dws_sales (
    order_id        NUMBER(20),      -- 订单id
    sales_date      VARCHAR2(10),    -- 销售日期   2024-11-12
    user_name       VARCHAR2(30),    -- 用户名
    prov_name       VARCHAR2(20),    -- 城市名
    region          VARCHAR2(20),    -- 区域
    category        VARCHAR2(50),    -- 产品分类
    product_name    VARCHAR2(100),   -- 产品名称
    price           NUMBER(10,2),    -- 产品单价
    sales_amount    NUMBER(10,2)     -- 销售金额
)PARTITION BY RANGE (sales_date)(
    partition p2024 values less than ('2025-01-01'),
    partition p2025 values less than ('2026-01-01'),
    partition pmax values less than (maxvalue)
);

-- 创建日期索引
CREATE INDEX idx_dws_salesdate ON dws_sales(sales_date) LOCAL;
~~~

基于`DWD`层向`DWS`层导入数据：

~~~postgresql
-- 编写存储过程
-- 自己写的......
create or replace procedure proc_owd_to_dws()
as 
begin
    INSERT INTO dws_sales(order_id,sales_date,user_name,prov_name,region,category,product_name,price,sales_amount)
    SELECT dfs.order_id,TO_CHAR(dfs.order_date, 'YYYY-MM-DD'),ou.user_name,ddp.prov_name,ddp.region,ddpd.category,ddpd.product_name,ddpd.price,dfs.amount
    FROM dwd_fact_sales dfs, ods_users ou, dwd_dim_province ddp,dwd_dim_product ddpd
    WHERE dfs.user_id = ou.user_id
          and dfs.prov_id = ddp.prov_id
          and dfs.product_id = ddpd.product_id;
    -- 打印输出
    raise notice '基于DWD层向DWS层导入数据完成!';
end;

CALL proc_owd_to_dws();
~~~





#### 2.5.4  ADS层聚合

![image-20250512230732494](assets/image-20250512230732494.png)

`ADS 层`：是应用数据服务层，属于数据仓库体系中的最顶层，直接面向业务应用和数据分析需求。让业务人员无需关注底层数据细节，直接获取所需的分析结果。ADS层是以DWS层为基础，按照主题进行数据汇总，为各种统计报表提供数据支撑。

ADS 层的数据特点：

| **特点** | **说明**                                             |
| -------- | ---------------------------------------------------- |
| 高度聚合 | 通常存储汇总数据（如日活、月销售额），而非明细数据。 |
| 面向主题 | 按业务主题划分（如用户、商品、交易），而非技术维度。 |
| 灵活多变 | 根据业务需求快速调整，可能每天新增或修改报表。       |

生成月销售汇总表：

~~~plsql
-- 创建月销售汇总表
CREATE TABLE ads_monthly_sales (
    report_month    VARCHAR2(7),    -- 报告月份   2024-11
    region          VARCHAR2(20),   -- 区域
    category        VARCHAR2(50),   -- 产品分类
    total_sales     NUMBER(15,2),   -- 销售总金额
    avg_order_amt   NUMBER(10,2)    -- 销售平均金额
);
~~~

基于`DWS`层导入汇总数据：

~~~postgresql
-- 自己写的.....
create or replace procedure proc_dws_to_ads() as 
begin
    INSERT INTO ads_monthly_sales(report_month,region,category,total_sales,avg_order_amt)
    SELECT substr(sales_date,1,7) ssd,region,category, SUM(sales_amount), round(AVG(sales_amount),2)
    FROM dws_sales
    GROUP BY ssd,region,category;
    -- 打印输出
    raise notice '基于DWS层向ADS层导入数据完成!';
end;

call proc_dws_to_ads();
~~~





#### 2.5.5 数仓分层扩展

![image-20250513100840481](assets/image-20250513100840481.png)





### 2.6 销售分析报表

**大区销售趋势分析**

~~~plsql
-- 报表查询
-- 先对每个区域和月份进行聚合，计算每月的总销售额，再应用窗口函数统计
WITH monthly_sales AS (
  SELECT 
    report_month,
    region,
    SUM(total_sales) AS monthly_total
  FROM ads_monthly_sales
  WHERE report_month BETWEEN '2024-01' AND '2024-12'
  GROUP BY report_month, region
)
SELECT 
  report_month,
  region,
  SUM(monthly_total) OVER(PARTITION BY region ORDER BY report_month) AS cum_sales,
  RANK() OVER(ORDER BY monthly_total DESC) AS sales_rank
FROM monthly_sales;
~~~





回顾总结：

- 分区表

  - 什么是分区表？

    ~~~
    把一张海量数据的表，按照规则(分区键)把表中数据拆分为多个物理存储。
    分区表从逻辑上来讲还是一张完整的表，但表中数据进行拆分并物理存储。
    
    好处：提高性能（DQL和DML都会提高）
    ~~~

  - 分区策略

    ~~~
    范围分区 ： 适用于数据有规则性排序的提前下，按照分区键(时间、数值)进行数据拆分为，分别存储到不同的分区下。
    
    列表分区：  适用于低基数列的数据(状态、职位)，按照分区键把数据根据列表指定值，进行拆分存储
               partition 分区1 values (值1,值2,值3)
    
    哈希分区：  适用于高基数列的数据(手机号、姓名)，按照分区键把数据以哈希方式进行拆分并存储。
               哈希方式： 拿数据值结合哈希算法，计算出存储位置。当表中数据希望均匀分布存储时使用哈希分区。
               
    
    复合分区：  以上3种分区任意结合在一起，就是复合分区。
    ~~~

- 数仓分层

  1. ODS层

     ~~~
     做为数仓中原始数据的存储层。
     从不同的数据源中提取相关数据后，统一存储在ODS层下（会存在适当的：数据脱敏、数据校验）
     ~~~

  2. DWD层

     ~~~plsql
     DW层： 数据仓库层。 可细化为：DWD、DWS。
     DWD层：明细数据层。把ODS层里面表中的数据进行细粒度的拆分。 区分：事实表、维度表。
            在DWD层要基于ODS层中的表数据，分别创建：事实表、维度表。
     ~~~

     事实表：

     ~~~
     存储的都是主键列、外键列、可运用计算、统计的指标(度量值)。
     事实表，会随着每业务的运营，表中数据在进行增长（数量偏多， 进行表分区）。
     ~~~

     维度表：

     ~~~
     存储的是和业务背景相关的数据信息（通常多以"文本描述"性的数据为主，例：产品名、区域名）。
     维度表：通常数据量不会变更性过大（数据量偏小）。
     ~~~

  3. DWS层

     ~~~
     DWS层：数据服务层。 形成数据宽表（方便给ADS层的报表准备数据）。
     宽表的形成的依据：以"事实表"为主，按照"主题"把相关的数据全部聚合在一张宽表(字段多)中。
     宽表，不考虑数据冗余，不考虑数据范式。就是为了数据分析而设计。
     ~~~

  4. ADS层

     ~~~
     ADS层：数据应用层。以"主题"为核心生成报表数据。
            提供给应用程序(BI前端显示)使用。
     ~~~

     

  















