// 请利用穷举法、自顶向下的备忘录法、动态规划算法、回溯法、分支限界法、蒙特卡洛来求解0-1背包问题，
// 比较不同算法的时间复杂度和空间复杂度。关于0-1背包问题描述如下：
// 有一个包和n个物品，包的容量为m，每个物品都有各自的体积和价值，
// 问当从这n个物品中选择多个物品放在包里而物品体积总数不超过包的容量m时，
// 能够得到的最大价值是多少？[对于每个物品不可以取多次，最多只能取一次，之所以叫做01背包，0表示不取，1表示取]
// 实验细节：
// 语言不限，要求将6种算法实现为6个函数，并在测试时一次性全部输出结果；
// 测试数据在附件的压缩包中。
#define DATAIN 20
#include <stdio.h>
#include <iostream>
#include <ctime>
#include <chrono> //C11计时库
#include <math.h>
#include <bitset>
#include <stdlib.h>
#include <queue>
#define max(a, b) ((a) > (b) ? (a) : (b))
#define MONTECARLO 1e6 //蒙特卡洛算法超参数
using namespace std;
using namespace chrono;
typedef struct node
{
    double up; //结点的价值上界
    int v;     //结点对应的价值
    int w;     //结点对应的重量
    int level; //结点在数组中的位置
} Node;
Node node;

std::queue<Node> que;

//穷举
int overall(int number, int capacity, int weight[], int value[])
{
    int num, maxn = 0; //maxv为最大价值，maxn为选择序列
    int maxv = 0;
    int tempw, tempv;
    int k;

    for (num = 0; num < pow(2, number); num++) //每一个num对应一个解
    {
        k = num;
        tempw = tempv = 0;
        for (int i = 0; i < number; i++) //n位二进制
        {
            if (k % 2 == 1)
            { //如果相应的位等于1，则代表物体放进去，如果是0，就不用放了
                tempw += weight[i];
                tempv += value[i];
            }
            k = k / 2; //二进制右移一位
        }
        //循环结束后，一个解生成
        //判断是否超过了背包的容积
        if (tempw <= capacity)
        {
            if (tempv > maxv)
            { //如果没有超，判断当前解是否比最优解更好
                maxv = tempv;
                maxn = num;
            }
        }
    }
    // cout << "穷举法选择的序列" << bitset<sizeof(unsigned int) * 3>(maxn) << endl;//调试

    return maxv;
}

//备忘录（自顶向下动态规划）
int memo(int number, int capacity, int weight[], int value[])
{
    int **Arr = (int **)malloc(sizeof(int *) * number);
    for (int i = 0; i < number; i++)
    {
        Arr[i] = (int *)malloc(sizeof(int) * (capacity + 1));
    }
    for (int i = 0; i < number; i++)
    {
        for (int j = 0; j <= capacity; j++)
        {
            Arr[i][j] = 0;
        }
    }
    //以上定义备忘录（存储每次背包子问题返回值），并初始化

    for (int i = 0; i < number; i++)
    {
        for (int j = 1; j <= capacity; j++)
        {
            if (i == 0)
                Arr[i][j] = value[i];
            else
                Arr[i][j] = (weight[i] <= j) ? max(Arr[i - 1][j], Arr[i - 1][j - weight[i]] + value[i]) : Arr[i - 1][j];
        }
    }
    return Arr[number - 1][capacity];
}

//动态规划算法（自下向顶）
int dynamic(int number, int capacity, int weight[], int value[])
{
    int *Arr = (int *)malloc(sizeof(int) * (capacity + 1));
    for (int i = 0; i <= capacity; i++)
    {
        Arr[i] = 0;
    }

    for (int i = 0; i < number; i++)
    {
        for (int j = capacity; j > 0; j--)
        {
            if (weight[i] <= j)
                Arr[j] = max(Arr[j], Arr[j - weight[i]] + value[i]);
        }
    }

    return Arr[capacity];
}

//回溯法内部函数
int knapBacktrack_inner(int i, int cw, int cv, int bestv, int number, int capacity, int weight[], int value[])
{
    if (i >= number)
    {
        bestv = max(bestv, cv);
    }
    else
    {
        if (cw + weight[i] <= capacity) //还能装
        {
            cw += weight[i];
            cv += value[i];
            bestv = knapBacktrack_inner(i + 1, cw, cv, bestv, number, capacity, weight, value);
            cw -= weight[i];
            cv -= value[i];
        }
        bestv = knapBacktrack_inner(i + 1, cw, cv, bestv, number, capacity, weight, value);
    }
    return bestv;
}

//回溯法
int knapBacktrack(int number, int capacity, int weight[], int value[])
{
    int cw = 0, cv = 0, bestv = 0;
    bestv = knapBacktrack_inner(0, cw, cv, bestv, number, capacity, weight, value);
    return bestv;
}

//以下很大一部分为分支限界法
void addLiveNode(double up, int cp, int cw, int level, int number)
{
    node.up = up;
    node.v = cp;
    node.w = cw;
    node.level = level;
    if (level <= number)
        que.push(node);
}

//排序(降序)
void Sort(double *v_w, int *value, int *weight, int number) //n为数组a的元素个数
{
    //进行N-1轮选择
    for (int i = 0; i < number - 1; i++)
    {
        int max_index = i;
        //找出第i大的数所在的位置
        for (int j = i + 1; j < number; j++)
            if (v_w[j] > v_w[max_index])
                max_index = j;
        //将第i小的数，放在第i个位置；如果刚好，就不用交换
        if (i != max_index)
        {
            double tempv_w = v_w[i];
            int tempw = weight[i], tempv = value[i];
            v_w[i] = v_w[max_index];
            value[i] = value[max_index];
            weight[i] = weight[max_index];
            v_w[max_index] = tempv_w;
            value[max_index] = tempv;
            weight[max_index] = tempw;
        }
    }
}

//分支限界法内函数：计算结点所对应的价值的上界
double bound(int i, int cp, int cw, int *value, int *weight, int number, int capacity)
{
    int cleft = capacity - cw; //剩余空间
    double b = cp;             //价值上界
    while (i < number && weight[i] <= cleft)
    {
        cleft -= weight[i];
        b += value[i];
        i++;
    }
    //装不下时，用下一个物品的单位重量价值折算到剩余空间推测
    if (i < number)
        b += value[i] / weight[i] * cleft;
    return b;
}

//分支限界法
int knapsack(int number, int capacity, int weight[], int value[])
{
    //初始化
    int *tmp_weight = (int *)malloc(sizeof(int) * number);
    int *tmp_value = (int *)malloc(sizeof(int) * number);
    double *tmp_valuerate = (double *)malloc(sizeof(double) * number);
    for (int i = 0; i < number; i++)
        tmp_valuerate[i] = (double)value[i] / weight[i];
    for (int i = 0; i < number; i++)
        tmp_value[i] = value[i];
    for (int i = 0; i < number; i++)
        tmp_weight[i] = weight[i];
    Sort(tmp_valuerate, tmp_value, tmp_weight, number);
    int cw = 0, cp = 0, bestp = 0;
    //cw为当前装包重量，cp为当前装包价值，bestp为当前最优值
    int pos = 0, up = bound(pos, cp, cw, tmp_value, tmp_weight, number, capacity);
    //函数Bound(i)计算当前结点相应的价值上界
    while (pos != number) //非叶子结点
    {
        //首先检查当前扩展结点的左儿子结点为可行结点
        if (cw + tmp_weight[pos] <= capacity) //左孩子结点为可行结点
        {
            if (cp + tmp_value[pos] > bestp)
                bestp = cp + tmp_value[pos];
            addLiveNode(up, cp + tmp_value[pos], cw + tmp_weight[pos], pos + 1, number); //将左孩子结点插入到优先队列中
        }
        up = bound(pos + 1, cp, cw, tmp_value, tmp_weight, number, capacity);
        //检查当前扩展结点的右儿子结点
        if (up >= bestp)                              //右子树可能包含最优解
            addLiveNode(up, cp, cw, pos + 1, number); //将右孩子结点插入到优先队列中
        //从优先级队列（堆数据结构）中取下一个扩展结点N
        Node N = que.front(); //测试，可能是这个方法
        que.pop();
        // printf("%d\n",N.v);
        cw = N.w;
        cp = N.v;
        up = N.up;
        pos = N.level;
    }
    return bestp;
}

//蒙特卡罗算法
int MonteCarlo(int number, int capacity, int weight[], int value[])
{
    int k, tempw, tempv, maxn = 0;

    int bestp = 0;
    srand((unsigned)time(0));
    for (int i = 0; i < MONTECARLO; i++)
    {
        k = rand() % (1 << number);
        tempw = tempv = 0;
        for (int i = 0; i < number; i++) //n位二进制
        {
            if (k % 2 == 1)
            { //如果相应的位等于1，则代表物体放进去，如果是0，就不用放了
                tempw += weight[i];
                tempv += value[i];
            }
            k = k / 2; //二进制右移一位
        }
        //循环结束后，一个解生成
        //判断是否超过了背包的容积
        if (tempw <= capacity)
        {
            if (tempv > bestp)
            { //如果没有超，判断当前解是否比最优解更好
                bestp = tempv;
                maxn = k;
            }
        }
    }
    return bestp;
}

int main()
{

#if DATAIN == 4
    int number = 4;
    int capacity = 6;
    int weight[20] = {1, 2, 3, 2};
    int value[20] = { 4, 6, 12, 7};

#endif

#if DATAIN == 10
    int number = 10;
    int capacity = 30;
    int weight[20] = {1, 2, 3, 2, 8, 10, 8, 6, 1, 4};
    int value[20] = {4, 6, 12, 7, 2, 18, 2, 7, 9, 10};

#endif

#if DATAIN == 15
    int number = 15;
    int capacity = 30;
    int weight[20] = {1, 2, 3, 2, 8, 10, 8, 6, 1, 4, 3, 4, 3, 7, 8};
    int value[20] = {4, 6, 12, 7, 2, 18, 2, 7, 9, 10, 28, 12, 7, 2, 17};

#endif

#if DATAIN == 20
    int number = 20;
    int capacity = 50;
    int weight[20] = {1, 2, 3, 2, 8, 10, 8, 6, 1, 4, 3, 4, 3, 7, 8, 7, 14, 13, 3, 5};
    int value[20] = {4, 6, 12, 7, 2, 18, 2, 7, 9, 10, 28, 12, 7, 2, 17, 4, 17, 4, 8, 9};

#endif

    auto start = system_clock::now();
    printf("%d,", overall(number, capacity, weight, value));
    auto end = system_clock::now();
    auto duration = duration_cast<microseconds>(end - start);
    cout << "穷举法花费了"
         << double(duration.count()) * microseconds::period::num / microseconds::period::den
         << "秒" << endl;

    start = system_clock::now();
    printf("%d,", memo(number, capacity, weight, value));
    end = system_clock::now();
    duration = duration_cast<microseconds>(end - start);
    cout << "备忘录法花费了"
         << double(duration.count()) * microseconds::period::num / microseconds::period::den
         << "秒" << endl;

    start = system_clock::now();
    printf("%d,", dynamic(number, capacity, weight, value));
    end = system_clock::now();
    duration = duration_cast<microseconds>(end - start);
    cout << "动态规划花费了"
         << double(duration.count()) * microseconds::period::num / microseconds::period::den
         << "秒" << endl;

    start = system_clock::now();
    printf("%d,", knapBacktrack(number, capacity, weight, value));
    end = system_clock::now();
    duration = duration_cast<microseconds>(end - start);
    cout << "回溯法花费了"
         << double(duration.count()) * microseconds::period::num / microseconds::period::den
         << "秒" << endl;

    start = system_clock::now();
    printf("%d,", knapsack(number, capacity, weight, value));
    end = system_clock::now();
    duration = duration_cast<microseconds>(end - start);
    cout << "分支界限法花费了"
         << double(duration.count()) * microseconds::period::num / microseconds::period::den
         << "秒" << endl;

    start = system_clock::now();
    printf("%d,", MonteCarlo(number, capacity, weight, value));
    end = system_clock::now();
    duration = duration_cast<microseconds>(end - start);
    cout << "蒙特卡洛法花费了"
         << double(duration.count()) * microseconds::period::num / microseconds::period::den
         << "秒" << endl;

    return 0;
}