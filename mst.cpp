/**
 * 16:35:52 09/26/2025
 * MST.cpp
 */
// ./MST.cpp
#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
 
using namespace std;
using namespace __gnu_pbds;
#define int long long
#define uint unsigned int
#define ld long double
#define fast ios_base::sync_with_stdio(false);cin.tie(NULL);cout.tie(NULL);
#define nl '\n'
#define all(v) v.begin(), v.end()
#define allr(v) v.rbegin(), v.rend()
#define allt(v, i) v.begin(), v.begin() + i
#define alls(v, i) v.begin() + i, v.end()
#define allst(v, s, e) v.begin() + s, v.begin() + e
#define NO (cout << "IMPOSSIBLE" << nl);
#define YES (cout << "YES" << nl);
#define F first
#define S second
#define pb push_back
#define emb emplace_back
#define pr pair
#define pii pair<int, int>
#define pdd pair<ld, ld>
#define vec vector
#define sz(v) ((int)v.size())
#define LT int T; cin >> T; while (T--)
template<typename T>
using vec2d = vector<vector<T>>;
template<typename T>
using ordered_set = tree<T, null_type, less<>, rb_tree_tag, tree_order_statistics_node_update>;
using indexed_set = tree<int, null_type, less<>, rb_tree_tag, tree_order_statistics_node_update>;
const ld eps = 1e-9l, pi = acos(-1.0l);
const int mod = 1e9 + 7, inf = 1e18;
 
template<typename T, typename G>
istream &operator>>(istream &in, pair<T, G> &p) {
    return in >> p.F >> p.S;
}
 
template<typename T>
typename enable_if<!is_same<T, string>::value && !is_same<T, char>::value, istream &>::type
operator>>(istream &in, T &a) {
    for (auto &v : a) in >> v;
    return in;
}
 
namespace rs {
    // bias signed integers so radix order matches operator<
    template <class I>
    static inline make_unsigned_t<I> bias(I x) {
        using U = make_unsigned_t<I>;
        U u = static_cast<U>(x);
        if constexpr (is_signed_v<I>) {
            return u ^ (U(1) << (numeric_limits<U>::digits - 1));
        } else {
            return u;
        }
    }
 
    // Stable LSD radix sort by member `w`
    template <class It>
    void radix_sort_by_w(It first, It last) {
        using T  = remove_reference_t<decltype(*first)>;
        using W  = remove_cv_t<decltype(declval<T>().w)>;
        static_assert(is_integral_v<W>, "T::w must be an integral type");
        using U  = make_unsigned_t<W>;
 
        const size_t n = static_cast<size_t>(distance(first, last));
        if (n <= 1) return;
 
        // Snapshot elements
        vector<T> a; a.reserve(n);
        for (auto it = first; it != last; ++it) {
            if constexpr (is_move_constructible_v<T>) a.push_back(move(*it));
            else                                           a.push_back(*it);
        }
 
        // Keys and index permutation
        vector<U> keys(n);
        for (size_t i = 0; i < n; ++i) keys[i] = bias<W>(a[i].w);
        vector<size_t> idx(n), idx_out(n);
        for (size_t i = 0; i < n; ++i) idx[i] = i;
 
        constexpr unsigned BYTES = sizeof(U);
        for (unsigned pass = 0; pass < BYTES; ++pass) {
            array<size_t, 256> count{}; // zero-initialized
            const unsigned shift = pass * 8;
 
            // count
            for (size_t i = 0; i < n; ++i) {
                unsigned b = static_cast<unsigned>((keys[idx[i]] >> shift) & U(0xFF));
                ++count[b];
            }
            // prefix sums
            size_t sum = 0;
            for (unsigned c = 0; c < 256; ++c) { auto t = count[c]; count[c] = sum; sum += t; }
            // stable scatter of indices
            for (size_t i = 0; i < n; ++i) {
                unsigned b = static_cast<unsigned>((keys[idx[i]] >> shift) & U(0xFF));
                idx_out[count[b]++] = idx[i];
            }
            idx.swap(idx_out);
        }
 
        // write back in sorted order
        auto out = first;
        for (size_t i = 0; i < n; ++i, ++out) *out = move(a[idx[i]]);
    }
}
 
class Graph {
public:
    using ll = long long;
    using Pair = pair<ll, ll>;
 
    struct splitmix64_hash {
        static uint64_t splitmix64(uint64_t x) {
            x += 0x9e3779b97f4a7c15;
            x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9;
            x = (x ^ (x >> 27)) * 0x94d049bb133111eb;
            return x ^ (x >> 31);
        }
 
        size_t operator()(uint64_t x) const {
            static const uint64_t FIXED_RANDOM = chrono::steady_clock::now().time_since_epoch().count();
            return splitmix64(x + FIXED_RANDOM);
        }
    };
    struct PairHash {
        static inline uint64_t splitmix64(uint64_t x) noexcept {
            x += 0x9e3779b97f4a7c15ULL;
            x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ULL;
            x = (x ^ (x >> 27)) * 0x94D049BB133111EBULL;
            return x ^ (x >> 31);
        }
        size_t operator()(const Pair& p) const noexcept {
            uint64_t a = static_cast<uint64_t>(p.first);
            uint64_t b = static_cast<uint64_t>(p.second);
            uint64_t h1 = splitmix64(a);
            uint64_t h2 = splitmix64(b + 0x9e3779b97f4a7c15ULL);
            uint64_t mix = h1 ^ (h2 + 0x9e3779b97f4a7c15ULL + (h1 << 6) + (h1 >> 2));
            return static_cast<size_t>(mix);
        }
    };
 
    enum EdgeStatus { removed, unused, used };
 
    struct Edge {
        int w = 0, s = 0, t = 0;
        EdgeStatus status = unused;
        Edge(int w = 0, int s = 0, int t = 0) : w(w), s(s), t(t) {}
        bool operator<(const Edge& oth) const { return w < oth.w; }
    };
 
    struct Node {
        Graph* G{};
        int id = 0, n_cnt = 0, neighbor = 0;
        bool active = true;
 
        Node() = default;
        Node(Graph* g, int id, int n_cnt = 0, int neighbor = 0)
            : G(g), id(id), n_cnt(n_cnt), neighbor(neighbor) {
            if (id) G->active_nodes.insert(id);
        }
 
        void connect(Node& oth, int w) {
            n_cnt++;
            oth.n_cnt++;
            neighbor ^= oth.id;
            oth.neighbor ^= id;
            G->active_m++;
            G->set_eid(id, oth.id, static_cast<int>(G->edges.size()));
            G->edges.emplace_back(w, id, oth.id);
        }
 
        void disconnect(Node& oth, bool prune = false) {
            int p = G->get_eid(id, oth.id);
            G->edges[p].status = prune ? Graph::used : Graph::removed;
            if (prune) G->score += G->edges[p].w;
            n_cnt--;
            oth.n_cnt--;
            neighbor ^= oth.id;
            oth.neighbor ^= id;
            G->active_m--;
            if (n_cnt == 1) G->d.push_back(id);
            if (oth.n_cnt == 1) G->d.push_back(oth.id);
        }
 
        void prune() {
            if (n_cnt == 0) return;
            G->active_nodes.erase(id);
            G->active_n--;
            active = false;
            disconnect(G->nodes[neighbor], true);
        }
    };
 
    // State
    int n = 0, m = 0, active_m = 0, active_n = 0, score = 0;
    vector<Node> nodes;                 // 1-indexed
    vector<Edge> edges;
    unordered_map<Pair, int, PairHash> atom;
    unordered_set<int, splitmix64_hash> active_nodes;
    vector<int> d;
 
    explicit Graph(int n = 0) : n(n), active_n(n) {
        nodes.resize(n + 1);
        for (int i = 0; i <= n; ++i) nodes[i] = Node(this, i);
    }
 
    // API identical in effect to the original free functions
    int get_eid(int u, int v) {
        ll a = min<ll>(u, v), b = max<ll>(u, v);
        return atom[{a, b}];
    }
 
    void set_eid(int u, int v, int i) {
        ll a = min<ll>(u, v), b = max<ll>(u, v);
        atom[{a, b}] = i;
    }
 
    void remove_edge(Edge& e) {
        nodes[e.s].disconnect(nodes[e.t]);
    }
 
    void prune() {
        while (!d.empty()) {
            Node& node = nodes[d.back()];
            d.pop_back();
            node.prune();
        }
    }
 
    void initial_prune() {
        for (int i = 1; i <= n; i++) if (nodes[i].n_cnt == 1) d.push_back(i);
        prune();
    }
 
    void sort_edges() {
        rs::radix_sort_by_w(allr(edges));
        for (int i = 0; i < static_cast<int>(edges.size()); i++) {
            set_eid(edges[i].s, edges[i].t, i);
        }
    }
 
    int get_score() {
        if (active_n == 1) return 0;
        initial_prune();
        sort_edges();
 
        for (auto& e: edges) {
            // cout << e.s << ' ' << e.t << ' ' << e.w << nl;
            // continue;
            if (active_m <= 0) break;
            if (e.status != unused) continue;
            remove_edge(e);
            prune();
        }
        // if (active_n > 1) {
        //     print(cout) << "-------\n";
        //     reconstruct();
        //     print(cout) << "-------\n";
        //     return -1; 
        // }
        if (active_n > 1) {
            // diagnose(cout);
            reconstruct();
            // diagnose(cout);
            if (active_n > 1 and active_m == 0) {
                return -1;
            }
            return get_score(); // score automatically added from previous run
        } else {
            return score;
        }
    }
 
    void reconstruct() {
        if (active_n == 1) return;
 
        // 1) Validate: no unused edges allowed
        if (active_m != 0) throw runtime_error("reconstruct: graph still has UNUSED edges");
 
        // 2) Build adjacency over USED edges (include inactive nodes too)
        vec2d<int> adj(n + 1);
        for (const auto& e : edges) {
            if (e.status == used) {
                adj[e.s].push_back(e.t);
                adj[e.t].push_back(e.s);
            }
        }
 
        // 3) DFS to label components for every node 1..n
        vector<int> comp(n + 1, 0);
        int comps = 0;
        vector<int> st;
        st.reserve(n);
 
        for (int i = 1; i <= n; ++i) {
            if (comp[i] != 0) continue;
            ++comps;
            comp[i] = comps;
            st.clear();
            st.push_back(i);
            while (!st.empty()) {
                int u = st.back(); st.pop_back();
                for (int v : adj[u]) {
                    if (comp[v] == 0) {
                        comp[v] = comps;
                        st.push_back(v);
                    }
                }
            }
        }
 
        // 4) Map min-weight edges between components using REMOVED edges
        unordered_map<Pair, int, PairHash> min_between;
        min_between.reserve(edges.size() * 2 + 1);
 
        for (const auto& e : edges) {
            if (e.status != removed) continue;          // only removed edges connect components
            int a = comp[e.s], b = comp[e.t];
            if (a == b) continue;                       // ignore intra-component
            if (a > b) swap(a, b);
            Pair key{static_cast<ll>(a), static_cast<ll>(b)};
            auto it = min_between.find(key);
            if (it == min_between.end() || e.w < it->second) {
                min_between[key] = e.w;
            }
        }
 
        // 5) Rebuild graph as the component-quotient graph
        // Clear old state
        edges.clear();
        atom.clear();
        active_nodes.clear();
        d.clear();
        active_m = 0;
 
        // Rebuild nodes [1..comps]
        n = comps;
        active_n = comps;
        nodes.clear();
        nodes.resize(n + 1);
        for (int i = 0; i <= n; ++i) nodes[i] = Node(this, i);
 
        // Recreate edges: keep only the minimum between any two components
        for (const auto& kv : min_between) {
            int a = static_cast<int>(kv.first.first);
            int b = static_cast<int>(kv.first.second);
            int w = kv.second;
            nodes[a].connect(nodes[b], w);              // status defaults to 'unused'
        }
 
        m = static_cast<int>(edges.size());
    }
 
    ostream& print(ostream& out) const {
        out << active_n << ' ' << active_m << " -- " << sz(nodes) << ' ' << sz(edges) << '\n';
        out << "Active Nodes:\n";
        for (int id : active_nodes) out << id << ' ';
        out << "\n---\n";
        for (const auto& e : edges) {
            out << e.s << ' ' << e.t << ' ' << e.w << ' ' << static_cast<int>(e.status) << '\n';
        }
        return out;
    }
 
    ostream& diagnose(ostream& out) const {
        out << active_n << ' ' << active_m << " -- " << sz(nodes) << ' ' << sz(edges) << ' ' << sz(atom) << '\n';
        return out;
    }
 
    istream& read(istream& in) {
        in >> n >> m;
        atom = {}, 
        nodes = vec<Node>(n + 1), 
        edges = {}, 
        active_nodes = {}, 
        active_n = n, 
        active_m = 0, 
        score = 0;
 
        for (int i = 1; i <= n; i++) nodes[i] = {this, i};
 
        for (int i = 0; i < m; i++) {
            int s, t, w;
            in >> s >> t >> w;
            nodes[s].connect(nodes[t], w);
        }
        return in;
    }
};
 
istream& operator>>(istream& in, Graph& g) {
    return g.read(in);
}
 
ostream& operator<<(ostream& out, const Graph& g) {
    return g.print(out);
}
 
void solve() {
    Graph g;
    cin >> g;
    int s = g.get_score();
    if (s == -1) NO
    else cout << s << nl;
}
 
int32_t main() {
    fast
    solve();
    return 0;
}