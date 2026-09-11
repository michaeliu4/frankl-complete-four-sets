#include <bits/stdc++.h>
using namespace std;
using U = uint64_t;
int main(int argc, char **argv) {
    if (argc != 2)
        return 2;
    int index[128];
    fill(index, index + 128, -1);
    int count = 0;
    for (int a = 0; a < 128; a++)
        if (__builtin_popcount((unsigned)a) == 4)
            index[a] = count++;
    // Expand every verified negative representative under all coordinate
    // permutations, include the empty family, and deduplicate labelled masks.
    vector<vector<int>> reps;
    int m;
    while (cin >> m) {
        vector<int> A(m);
        for (int &a : A)
            cin >> a;
        reps.push_back(A);
    }
    vector<U> all{0};
    array<int, 7> p{0, 1, 2, 3, 4, 5, 6};
    do {
        int map[128] = {};
        for (int a = 1; a < 128; a++) {
            int i = __builtin_ctz((unsigned)a);
            map[a] = map[a ^ (1 << i)] | (1 << p[i]);
        }
        for (auto const &A : reps) {
            U f = 0;
            for (int a : A)
                f |= U(1) << index[map[a]];
            all.push_back(f);
        }
    } while (next_permutation(p.begin(), p.end()));
    sort(all.begin(), all.end());
    all.erase(unique(all.begin(), all.end()), all.end());
    ofstream out(argv[1], ios::binary);
    if (!out)
        return 3;
    long long counts[11] = {};
    for (U f : all) {
        out.write((char *)&f, sizeof(f));
        counts[__builtin_popcountll(f)]++;
    }
    cout << "labeled " << all.size() << "\n";
    for (int m = 0; m <= 10; m++)
        cout << m << " " << counts[m] << "\n";
    return 0;
}
