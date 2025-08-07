#pragma once
#include <vector>
class UnionFindSet
{
    std::vector<int> rank;
    std::vector<int> parent;

public:
    UnionFindSet(int n)
    {
        rank = std::vector<int>(n, 0);
        parent = std::vector<int>(n, 0);
        for (int i = 0; i < n; i++)
        {
            parent[i] = i;
        }
    }

    int find(int x) { return parent[x] == x ? x : parent[x] = find(parent[x]); }

    void unite(int x, int y)
    {
        int rootX = find(x);
        int rootY = find(y);
        if (rootX != rootY)
        {
            if (rank[rootX] > rank[rootY])
            {
                parent[rootY] = rootX;
            }
            else if (rank[rootX] < rank[rootY])
            {
                parent[rootX] = rootY;
            }
            else
            {
                parent[rootY] = rootX;
                rank[rootX]++;
            }
        }
    }
};