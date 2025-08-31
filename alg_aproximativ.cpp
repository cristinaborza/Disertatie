#include <bits/stdc++.h>

using namespace std;
using namespace std::chrono;

ifstream f("input.txt");
ofstream g("output.txt");

const int Dim = 1005;
const int Inf = 1e9;

int k;

// The struct that saves a restriction. It is composed from:
//      * an interval I = [a, b];
//      * a weight w;
//      * a vector r, where r[c] is the number
//        of times we want the color c appear in I;
struct Restriction {
    int a, b, w;
    vector<int> r;

    Restriction(int a, int b, int w) {
        this -> a = a;
        this -> b = b;
        this -> w = w;
        r.resize(k + 1, 0);
    }

    Restriction() {}

    bool operator <(const Restriction& other) {
        return a < other.a || (a == other.a && b < other.b);
    }
};

// It represent an element from the poset described in Lemma 12.
//      * vector<v>: is an element from Z^{k + 2};
//      * w: the weight of the element.
struct PosetElement {
    vector<int> v;
    int w;

    // We want map a restriction to an element in the poset.
    PosetElement(Restriction restr) {
        w = restr.w;

        v.resize(k + 3, 0);
        v[1] = -restr.a;
        v[2] = restr.b;
        for (int i = 1; i <= k; ++i) {
            v[i + 2] = restr.r[i];
        }
    }

    PosetElement() {}

    bool operator <(const PosetElement& other) {
        for (int i = 1; i <= k + 2; ++i) {
            if (v[i] > other.v[i])
                return false;
        }
        return true;
    }
};


Restriction restrictions[Dim];
PosetElement poset[Dim];

int n, m;
int degree[Dim], dpMaxIndepSet[Dim];
int w[Dim][Dim];

vector<int> G[Dim];
map<tuple<int, int, vector<int>>, int> staircaseDp;

vector<vector<int>> possibleRestrictions;
vector<int> currentRestriction;

void restrictionSetToPoset() {
    for (int i = 1; i <= m; ++i) {
        poset[i] = PosetElement(restrictions[i]);
    }
}

vector<int> sortInTopologicalOrder() {
    vector<int> answer;
    queue<int> coada;
    for(int i = 1; i <= m; ++i) {
        if(degree[i] == 0) {
            coada.push(i);
        }
    }

    while(!coada.empty()) {
        int node = coada.front();
        answer.push_back(node);
        coada.pop();

        for(vector<int> :: iterator it = G[node].begin(); it != G[node].end(); ++it) {
            --degree[*it];
            if(degree[*it] == 0) {
                coada.push(*it);
            }
        }
    }

    return answer;
}

// Finds the maximum weight in a poset.
// The idea is presented in Lemma 11. Basically it transforms the poset into a
// graph, and finds the maximum weight chain in that graph using dynamic programming.
int findMaximumWeightChainInPoset() {
    for (int i = 1; i <= m; ++i) {
        for (int j = 1; j <= m; ++j) {
            if (i != j && poset[i] < poset[j]) {
                G[i].push_back(j);
                ++degree[j];
            }
        }
    }

    vector<int> topologicalOrder = sortInTopologicalOrder();

    int maxWeightChain = 0;
    int d[m + 1];

    for (int i = 0; i < m; ++i) {
        int node = topologicalOrder[i];
        d[node] = poset[node].w;
        for (int j = 0; j < i; ++j) {
            int neighbor = topologicalOrder[j];
            if (poset[neighbor] < poset[node]) {
                d[node] = max(d[node], d[neighbor] + poset[node].w);
            }
        }
        maxWeightChain = max(maxWeightChain, d[node]);
    }

    return maxWeightChain;
}


// Checks if a <= b for two vectors of integers
bool vectorComp(const vector<int>& a, const vector<int>& b) {
    if (a.size() != b.size()) {
        return false;
    }

    for (size_t i = 0; i < a.size(); ++i) {
        if (a[i] > b[i]) {
            return false;
        }
    }
    return true;
}

vector<int> vectorDifference(const vector<int>& a, const vector<int>& b) {
    assert(a.size() == b.size());

    vector<int> ans;

    int len = a.size();
    for (int i = 0; i < len; ++i) {
        ans.push_back(a[i] - b[i]);
    }

    return ans;
}

void generatePossibleColorings(int k, int sum) {
    // If we generate all k positions
    if (k == 0) {
        // If the remaining sum is 0, we found a valid vector
        if (sum == 0) {
            possibleRestrictions.push_back(currentRestriction);
        }
        return;
    }

    for (int i = 0; i <= sum; ++i) {
        currentRestriction.push_back(i);
        generatePossibleColorings(k - 1, sum - i);
        currentRestriction.pop_back();
    }
}

int solveDp(vector<Restriction> intervals, int t, int p, vector<int> r) {
    tuple<int, int, vector<int>> state = make_tuple(t, p, r);

    if (staircaseDp.count(state))
        return staircaseDp[state];

    // The base case: when t = 1
    if (t == 0) {
        const auto& I1 = intervals[0];
        if (vectorComp(r, I1.r)) {
            staircaseDp[state] = I1.w;
        } else {
            staircaseDp[state] = -Inf;
        }

        return staircaseDp[state];
    }


    int ans = -Inf;
    for (int i = t - 1; i >= 0; --i) {
        if (intervals[i].a >= intervals[t].a && intervals[i].b <= intervals[t].b)
            continue;

        possibleRestrictions.clear();
        generatePossibleColorings(k, intervals[i].b - p + 1);

        for (auto restriction: possibleRestrictions) {
            if (restriction.size() == 0) {
                continue;
            }
            vector<int> v1 = vectorDifference(intervals[i].r, restriction);
            vector<int> v2 = vectorDifference(intervals[t].r, r);
            if (vectorComp(restriction, r) &&
                vectorComp(v2, v1)) {
                ans = max(ans, solveDp(intervals, i, p, restriction));
            }
        }
    }

    ans += intervals[t].w;
    staircaseDp[state] = ans;
    return ans;
}

int findMaximumStaircase(int u, int v, int s, int t) {
    // Preprocessing step: I remove all the intervals that are not
    // "compatible" with intervals[s] or intervals[t].

    if (s != t &&
        ((restrictions[s].a == restrictions[t].a) ||
        (restrictions[s].b == restrictions[t].b))) {
        return -Inf;
    }


    vector<Restriction> validIntervals;
    validIntervals.push_back(restrictions[s]);
    for (int i = s + 1; i < t; ++i) {
        if (restrictions[s].b >= restrictions[i].a &&
            restrictions[s].a < restrictions[i].a &&
            restrictions[t].a > restrictions[i].a &&
            restrictions[i].b < v &&
            restrictions[i].b < restrictions[s].a) {
            validIntervals.push_back(restrictions[i]);
        }
    }

    if (s != t) validIntervals.push_back(restrictions[t]);

    return solveDp(validIntervals, validIntervals.size() - 1, restrictions[t].a, restrictions[t].r);
}

int findMaximumStaircase(int u, int v) {
    int answer = -Inf;
    for (int i = 1; i <= m; ++i) {
        for (int j = i; j <= m; ++j) {
            if (restrictions[i].a == u && restrictions[j].b == v &&
                restrictions[i].b >= restrictions[j].a) {
                    staircaseDp.clear();
                answer = max(answer, findMaximumStaircase(u, v, i, j));
            }
        }
    }

    return answer;
}

int main() {
    auto start = high_resolution_clock::now();

    // Read the input data.
    //  - n = length of the vector
    //  - k = the number of colors
    //  - m = number of intervals
    f >> n >> k >> m;
    for (int i = 1; i <= m; ++i) {
        int a, b, w;
        f >> a >> b >> w;
        restrictions[i] = Restriction(a, b, w);
    }



    for (int i = 1; i <= m; ++i) {
        for (int j = 1; j <= k; ++j) {
            int c;
            f >> c;
            restrictions[i].r[j] = c;
        }
    }

    // STEP 1 : COMPUTE THE MAXIMUM WEIGH TOWER

    // First, we need to transform the set of restrictions
    // into a poset.
    restrictionSetToPoset();

    // Then, we find the maximum weight in the Poset, using Lemma 11.
    int maxWeightTower = findMaximumWeightChainInPoset();

    // STEP 2: For every u, v \in V, we compute the maximum weight staircase between u and v
    // using the algorithm described in Theorem 13.
    sort(restrictions + 1, restrictions + m + 1);

    currentRestriction.push_back(0);
    for (int i = 1; i <= n; ++i) {
        for (int j = i; j <= n; ++j) {
            w[i][j] = findMaximumStaircase(i, j);
        }
    }

    // STEP 3: The third step is to compute the maximum weight (with respect with the weight
    // we computed at step 2) independent set in I.

    for (int i = 1; i <= n; ++i) {
        dpMaxIndepSet[i] = -Inf;
        for (int j = i - 1; j >= 0; --j) {
            dpMaxIndepSet[i] = max(dpMaxIndepSet[i], dpMaxIndepSet[j] + w[j + 1][i]);
        }
        dpMaxIndepSet[i] = max(dpMaxIndepSet[i], dpMaxIndepSet[i - 1]);
    }

    int maxIndepStaircase = dpMaxIndepSet[n];
    int answer = max(maxIndepStaircase, maxWeightTower);

    cout << "Max weight tower: " << maxWeightTower << '\n';
    cout << "Max Indep set: " << maxIndepStaircase << '\n';

    g << answer << '\n';

    auto stop = high_resolution_clock::now();
    auto duration = duration_cast<milliseconds>(stop - start);

    cout << duration.count() << "\n";

    return 0;
}
