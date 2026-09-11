// Exhaustive hereditary filtering and explicit positive-pattern coverage.
// The independent proof treats retained boundary families as POSSIBLE Non-FC,
// not as certified negatives. Every removed family must have a positive proof.
#include <bits/stdc++.h>
using namespace std;
using U = uint64_t;
using W = __uint128_t;
struct Hash {
    size_t operator()(W k) const {
        return U(k) ^ (U(k >> 64) * 0x9e3779b97f4a7c15ULL);
    }
};
vector<int> E;
int ix[256];
unordered_map<W, W, Hash> cache;
W encode(vector<int> const &A) {
    W x = 0;
    for (int a : A) {
        if (a < 0 || a >= 256 || ix[a] < 0)
            throw runtime_error("invalid 4-set");
        x |= W(1) << ix[a];
    }
    if (__builtin_popcountll(U(x)) + __builtin_popcountll(U(x >> 64)) != (int)A.size())
        throw runtime_error("duplicate block");
    return x;
}
vector<int> decode(W x) {
    vector<int> A;
    for (int j = 0; j < 70; j++)
        if (x >> j & 1)
            A.push_back(E[j]);
    return A;
}
struct Canon {
    W key;
    array<int, 8> map;
};
// Isomorphisms preserve degree classes. Their exhaustive internal
// permutations give the canonical key and an explicit witnessing point map.
Canon canon_full(vector<int> const &A) {
    array<int, 8> d{};
    for (int a : A)
        for (int i = 0; i < 8; i++)
            d[i] += a >> i & 1;
    array<int, 8> order{0, 1, 2, 3, 4, 5, 6, 7};
    sort(order.begin(), order.end(),
         [&](int i, int j) { return make_pair(d[i], i) < make_pair(d[j], j); });
    vector<vector<int>> groups;
    vector<int> positions;
    for (int i = 0; i < 8;) {
        int j = i;
        vector<int> g;
        while (j < 8 && d[order[j]] == d[order[i]])
            g.push_back(order[j++]);
        sort(g.begin(), g.end());
        groups.push_back(g);
        positions.push_back(i);
        i = j;
    }
    Canon best{~W(0), {}};
    array<int, 8> p;
    function<void(int)> rec = [&](int k) {
        if (k < (int)groups.size()) {
            auto g = groups[k];
            do {
                for (int j = 0; j < (int)g.size(); j++)
                    p[g[j]] = positions[k] + j;
                rec(k + 1);
            } while (next_permutation(g.begin(), g.end()));
            return;
        }
        W mask = 0;
        for (int a : A) {
            int s = 0;
            for (int i = 0; i < 8; i++)
                if (a >> i & 1)
                    s |= 1 << p[i];
            mask |= W(1) << ix[s];
        }
        if (mask < best.key)
            best = {mask, p};
    };
    rec(0);
    return best;
}
W canonical(vector<int> const &A) {
    W x = encode(A);
    auto it = cache.find(x);
    if (it != cache.end())
        return it->second;
    W k = canon_full(A).key;
    cache.emplace(x, k);
    return k;
}
vector<vector<int>> read_raw(string path) {
    ifstream f(path);
    if (!f)
        throw runtime_error("missing raw input " + path);
    vector<vector<int>> out;
    string line;
    while (getline(f, line)) {
        if (line.empty())
            continue;
        istringstream s(line);
        U lo, hi;
        if (!(s >> lo >> hi))
            throw runtime_error("bad raw row");
        vector<int> A;
        int a;
        while (s >> a)
            A.push_back(a);
        if (encode(A) != (W(hi) << 64 | lo) || canonical(A) != encode(A))
            throw runtime_error("bad canonical raw row");
        out.push_back(A);
    }
    return out;
}
int main(int argc, char **argv) {
    try {
        if (argc != 4)
            throw runtime_error("expected raw-dir, certificates-list, output-dir");
        fill(begin(ix), end(ix), -1);
        for (int a = 0; a < 256; a++)
            if (__builtin_popcount((unsigned)a) == 4) {
                ix[a] = E.size();
                E.push_back(a);
            }
        array<unordered_set<W, Hash>, 12> positive, negative;
        array<unordered_map<W, string, Hash>, 12> ids;
        {
            ifstream f(argv[2]);
            string status, id;
            int m;
            while (f >> status >> id >> m) {
                vector<int> A(m);
                for (int &a : A)
                    if (!(f >> a))
                        throw runtime_error("truncated pattern");
                W k = canonical(A);
                if (status == "FC") {
                    positive[m].insert(k);
                    ids[m][k] = id;
                } else if (status == "NonFC")
                    negative[m].insert(k);
                else
                    throw runtime_error("bad status");
            }
        }
        unordered_set<W, Hash> previous;
        vector<vector<int>> remaining9;
        // Retained sets over-approximate the non-FC classes. A missing one-block
        // deletion or an exact positive certificate justifies removal; retention
        // alone does not assert that a candidate is non-FC.
        for (int m = 5; m <= 10; m++) {
            auto raw = read_raw(string(argv[1]) + "/raw" + to_string(m) + ".txt");
            unordered_set<W, Hash> remaining;
            int hereditary = 0, positive_removed = 0;
            for (auto const &A : raw) {
                bool ok = true;
                if (m > 5)
                    for (size_t j = 0; j < A.size(); j++) {
                        auto B = A;
                        B.erase(B.begin() + j);
                        if (!previous.count(canonical(B))) {
                            ok = false;
                            break;
                        }
                    }
                if (!ok)
                    continue;
                hereditary++;
                W k = encode(A);
                // Match the historical filtration: only size-5 and size-6 direct removals.
                if (m <= 6 && positive[m].count(k)) {
                    positive_removed++;
                    continue;
                }
                remaining.insert(k);
            }
            cout << "m " << m << " raw " << raw.size() << " hereditary " << hereditary
                 << " direct_removed " << positive_removed << " retained " << remaining.size()
                 << "\n"
                 << flush;
            ofstream out(string(argv[3]) + "/retained" + to_string(m) + ".txt");
            vector<W> sorted(remaining.begin(), remaining.end());
            sort(sorted.begin(), sorted.end());
            for (W k : sorted) {
                out << U(k) << ' ' << U(k >> 64);
                for (int a : decode(k))
                    out << ' ' << a;
                out << '\n';
            }
            if (m == 9)
                for (W k : sorted)
                    remaining9.push_back(decode(k));
            if (m == 10) {
                int pos = 0, neg = 0;
                for (W k : remaining) {
                    if (positive[10].count(k))
                        pos++;
                    else if (negative[10].count(k))
                        neg++;
                    else
                        throw runtime_error("unclassified ten-block candidate");
                }
                cout << "size10 positive " << pos << " residual " << neg << "\n";
                if (pos != 812 || neg != 13)
                    throw runtime_error("wrong ten boundary counts");
            }
            previous = move(remaining);
            // Avoid unbounded caching while keeping repeated deletions within each layer fast.
            cache.clear();
        }
        int covered = 0, pos = 0, neg = 0;
        ofstream cover(string(argv[3]) + "/coverage9.txt");
        for (auto const &A : remaining9) {
            W k = encode(A);
            bool found = false;
            for (int i = 0; i < 9 && !found; i++)
                for (int j = i + 1; j < 9 && !found; j++) {
                    vector<int> B;
                    for (int t = 0; t < 9; t++)
                        if (t != i && t != j)
                            B.push_back(A[t]);
                    W b = canonical(B);
                    if (positive[7].count(b)) {
                        auto C = canon_full(B);
                        cover << U(k) << ' ' << U(k >> 64) << ' ' << ids[7].at(b) << ' ' << i << ' '
                              << j;
                        for (int v : C.map)
                            cover << ' ' << v;
                        cover << '\n';
                        found = true;
                    }
                }
            if (found) {
                covered++;
                continue;
            }
            if (positive[9].count(k))
                pos++;
            else if (negative[9].count(k))
                neg++;
            else {
                cerr << "missing9 ";
                for (int a : A)
                    cerr << a << ' ';
                cerr << '\n';
                throw runtime_error("unclassified nine-block candidate");
            }
        }
        cout << "size9 covered " << covered << " direct_positive " << pos << " residual " << neg
             << "\n";
        if (covered != 4477 || pos != 308 || neg != 52)
            throw runtime_error("wrong nine boundary counts");
        cout << "PASS: boundary coverage reconstructed using positive certificates only.\n";
        return 0;
    } catch (exception const &e) {
        cerr << e.what() << '\n';
        return 1;
    }
}
