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
};

Restriction restrictions[Dim];
int n, m;

int culori[Dim];
int ans, dim;

pair<int, int> checkSolution() {
    int ans = 0;
    int nr = 0;
    for (int i = 1; i <= m; ++i) {
        vector<int> cnt(k + 1, 0);
        for (int j = restrictions[i].a; j <= restrictions[i].b; ++j) {
            ++cnt[culori[j]];
        }


        bool ok = true;
        for (int j = 1; j <= k; ++j) {
            if (cnt[j] != restrictions[i].r[j]) {
                ok = false;
                break;
            }
        }

        if (ok) ++nr;
        ans += ok * restrictions[i].w;
    }

    return make_pair(ans, nr);
}

void backtracking(int pos) {
    if (pos > n) {
        pair<int, int> sol = checkSolution();
        if (ans < sol.first) {
            ans = sol.first;
            dim = sol.second;
        } else if (ans == sol.first){
            dim = min(dim, sol.second);
        }
        return;
    }

    for(int i = 1; i <= k; ++i) {
        culori[pos] = i;
        backtracking(pos + 1);
    }
}

int main() {
    auto start = high_resolution_clock::now();

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

    backtracking(1);
    g << ans << '\n' << ans / (4 * sqrt(dim));

    auto stop = high_resolution_clock::now();
    auto duration = duration_cast<milliseconds>(stop - start);

    cout << duration.count() << "\n";
}
