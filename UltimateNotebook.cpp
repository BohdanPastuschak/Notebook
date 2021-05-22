#include <bits/stdc++.h>
using namespace std;

//#pragma GCC optimize("Ofast,unroll-loops")
//#pragma GCC target("avx,avx2,fma")

typedef long long LL;
typedef pair<int, int> PII;
typedef vector<int> VI;
typedef long double db;
#define MP make_pair
#define PB push_back
#define X first
#define Y second

#define FOR(i, a, b) for(int i = (a); i < (b); ++i)
#define RFOR(i, b, a) for(int i = (b) - 1; i >= (a); --i)
#define ALL(a) a.begin(), a.end()
#define SZ(a) (int)((a).size())
#define FILL(a, value) memset(a, value, sizeof(a))
#define debug(a) cerr << #a << " = " << a << endl;

template<typename T> void setmax(T& x, T y) {x = max(x, y);}
template<typename T> void setmin(T& x, T y) {x = min(x, y);}

template<typename T> void print(const T& a, ostream& out){	
	for(auto i: a) out << i << ' ';
	out << endl;
}

const double PI = acos(-1.0);
const LL INF = 1e9 + 47;
const LL LINF = INF * INF;
mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());

namespace Library{
	namespace IntModulo{
		const int mod = 1e9 + 7;

		inline int add(int x, int y, int m = mod){
			return x + y < m ? x + y : x + y - m;
		}

		inline int sub(int x, int y, int m = mod){
			return x >= y ? x - y : x - y + m;
		}

		inline int mult(int x, int y, int m = mod){
			return x * (LL) y % m;
		}

		inline int power(int x, LL y, int m = mod){
			int r = 1;
			while(y){
				if (y & 1) r = mult(r, x, m);
				x = mult(x, x, m);
				y >>= 1;
			}
			
			return r;
		}
		
		inline int inverse(int x, int m = mod){
			return power(x, m - 2, m);
		}

		inline void ADD(int& x, int y, int m = mod){
			x += y;
			if (x >= m) x -= m;
		}

		inline void SUB(int& x, int y, int m = mod){
			x -= y;
			if (x < 0) x += m;
		}

		inline void MULT(int& x, int y, int m = mod){
			x = (x * (LL) y) % m;
		}
	};

	namespace BerlekampMassey{
		using namespace IntModulo;
			
		inline vector<int> BM(vector<int> x){
			vector<int> ls, cur;
			int lf = 0, ld = 0;
			
			FOR(i, 0, SZ(x)){
				int t = 0;
				FOR(j, 0, SZ(cur))
					t = add(t, mult(x[i - j - 1], cur[j]));
					
				if (t == x[i])
					continue;
								
				if(!SZ(cur)){
					cur.resize(i + 1);
					lf = i;
					ld = sub(t, x[i]);
					continue;
				}
				
				int k = mult(sub(t, x[i]), inverse(ld));
				vector<int> c(i - lf - 1); 
				c.PB(k);
				
				FOR(j, 0, SZ(ls))
					c.PB(sub(0, mult(k, ls[j])));
					
				if (SZ(c) < SZ(cur))
					c.resize(SZ(cur));
					
				FOR(j, 0, SZ(cur))
					c[j] = add(c[j], cur[j]);
				
				if (i - lf + SZ(ls) >= SZ(cur)){
					ls = cur;
					lf = i;
					ld = sub(t, x[i]);
				}
				
				cur = c;
			}
		
			return cur;
		}
		
		inline void multiply(int m, vector<int>& p, vector<int>& q, vector<int>& v){
			vector<int> t(2 * m, 0);
			
			FOR(i, 0, m) 
				FOR(j, 0, m)			
					t[i + j] = add(t[i + j], mult(p[i], q[j]));
					
			RFOR(i, 2 * m, m)
				RFOR(j, m, 0)
					t[i - j - 1] = add(t[i - j - 1], mult(t[i], v[j]));
					
			FOR(i, 0, m)
				p[i] = t[i];
		}
		
		inline int solve(vector<int> x, LL n){
			if (n < SZ(x))
				return x[n];
			
			vector<int> v = BM(x);
			int m = v.size(); 
			if(!m)
				return 0;
			
			VI s(m + 1, 0);
			VI t(m + 1, 0);
			s[0] = 1; 	
			t[1] = 1;		
			if (m == 1)
				t[0] = v[0];
			
			while(n){
				if (n & 1) 
					multiply(m, s, t, v);
				multiply(m, t, t, v);
				n >>= 1;
			}
			
			int ans = 0;
			FOR(i, 0, m)
				ans = add(ans, mult(s[i], x[i]));
			return ans;
		}	
	};

	namespace MatrixExponentiation{
		using namespace IntModulo;
		
		struct matrix{
			int n;
			vector<vector<int>> a;
			matrix(){}
			matrix(int _n, bool zero = true){
				n = _n;
				a = vector<vector<int>>(n, vector<int>(n, 0));
				if (!zero){
					FOR(i, 0, n) a[i][i] = 1;
				}
			}

			matrix(const vector<vector<int>>& A){
				a = A;
				n = SZ(a);
			}

			matrix multiply(const matrix& o) const{
				matrix res(n);
				FOR(i, 0, n) FOR(j, 0, n) FOR(k, 0, n){
					ADD(res.a[i][j], mult(a[i][k], o.a[k][j]));	
				}
				
				return res;
			}

			matrix power(LL y) const {
				matrix res(n, false);
				matrix h(a);
				while(y){
					if (y & 1) res = res.multiply(h);
					h = h.multiply(h);
					y >>= 1;
				}

				return res;
			}
		};
	};

	namespace Combinatorics{
		using namespace IntModulo;
		
		vector<int> fact, inv, invFact;	
	
		inline int C(int n, int k){ // binomial C(n, k)
			return n < k ? 0 : mult(fact[n], mult(invFact[k], invFact[n - k]));
		}
		
		inline int C_k(int n, int k){ // binomial C(n, k) in O(k)
			k = min(k, n - k);
			int p = 1, q = 1;
			for(int i = 1; i <= k; ++i){
				MULT(q, i);
				MULT(p, n + 1 - i);
			}
						
			return mult(p, inverse(q));
		}
		
		inline int H(int n, int k){ // number of solution x1 + .. + xn = k
			return C(n + k - 1, k);
		}
		
		inline void init(int N){
			if (SZ(fact) >= N){
				return;
			}
			
			fact.resize(N);
			inv.resize(N);
			invFact.resize(N);
			
			inv[1] = 1;
			FOR(i, 2, N)
				inv[i] = mult(mod - mod / i, inv[mod % i]);
			
			invFact[0] = fact[0] = 1;
			FOR(i, 1, N){
				fact[i] = mult(i, fact[i - 1]);
				invFact[i] = mult(invFact[i - 1], inv[i]);
			}
		}	
	};

	namespace LagrangeInterpolation{
		using namespace Combinatorics;
		
		int solve(vector<int>& y, LL x){ //Polynomial on degree k passing through points 0, 1, 2, .., k
			int n = SZ(y);	
			if (x < n)
				return y[x];
				
				
			vector<int> pref(n);
			pref[0] = 1;
			FOR(i, 1, n)
				pref[i] = mult(pref[i - 1], (x - i) % mod);
			
			vector<int> suf(n + 1);
			suf[n] = 1;
			RFOR(i, n, 1)
				suf[i] = mult(suf[i + 1], (x - i) % mod);
			
			Combinatorics::init(n);
			
			int ans = 0;
			FOR(i, 1, n){
				int tut = mult(y[i], 
					mult(pref[i - 1], mult(suf[i + 1], 
					mult(invFact[i - 1], invFact[n - i - 1]))));
					
				if ((n - i) & 1)
					ans = add(ans, tut);
				else
					ans = sub(ans, tut);
			}
			
			return ans;		
		}  	

		int powerSum(int k, LL n) { // Sum(i, 1, n) i^k
			vector<int> y(k + 3, 0);
			FOR(i, 1, SZ(y))
				y[i] = add(y[i - 1], power(i, k));
			
			return solve(y, n);
		}
	};

	namespace MinCostMaxFlow{
		// Warning: when choosing flow_t and cost_t, make sure they can handle the sum of flows and costs, not just individual
		// flows and costs.
		template<typename flow_t, typename cost_t>
		struct min_cost_flow {
			const cost_t COST_INF = numeric_limits<cost_t>::max() / 2;
		 
			struct edge {
				int node, rev;
				flow_t capacity;
				cost_t cost;
		 
				edge() {}
		 
				edge(int _node, int _rev, flow_t _capacity, cost_t _cost)
					: node(_node), rev(_rev), capacity(_capacity), cost(_cost) {}
			};
		 
			int V = -1, E = 0;
			vector<vector<edge>> adj;
			vector<cost_t> dist;
			vector<int> prev;
			vector<edge*> prev_edge;
			bool too_many_bellman_ford_iterations = false;
		 
			min_cost_flow(int vertices = -1) {
				if (vertices >= 0)
					init(vertices);
			}
		 
			void init(int vertices) {
				V = vertices;
				E = 0;
				adj.assign(V, {});
				dist.resize(V);
				prev.resize(V);
				prev_edge.resize(V);
				too_many_bellman_ford_iterations = false;
			}
		 
			void add_directional_edge(int u, int v, flow_t capacity, cost_t cost) {
				assert(0 <= u && u < V && 0 <= v && v < V);
				edge uv_edge(v, adj[v].size() + (u == v ? 1 : 0), capacity, cost);
				edge vu_edge(u, adj[u].size(), 0, -cost);
				adj[u].push_back(uv_edge);
				adj[v].push_back(vu_edge);
				E++;
			}
		 
			edge &reverse_edge(const edge &e) {
				return adj[e.node][e.rev];
			}
		 
			bool bellman_ford(int source, int sink) {
				for (int i = 0; i < V; i++) {
					dist[i] = COST_INF;
					prev[i] = -1;
					prev_edge[i] = nullptr;
				}
		 
				long long work = 0;
				vector<int> last_seen(V, -1);
				vector<int> nodes = {source}, next_nodes;
				dist[source] = 0;
		 
				for (int iteration = 0; iteration < V; iteration++) {
					next_nodes.clear();
		 
					for (int node : nodes) {
						for (edge &e : adj[node])
							if (e.capacity > 0 && dist[node] + e.cost < dist[e.node]) {
								dist[e.node] = dist[node] + e.cost;
								prev[e.node] = node;
								prev_edge[e.node] = &e;
		 
								if (last_seen[e.node] != iteration) {
									last_seen[e.node] = iteration;
									next_nodes.push_back(e.node);
								}
							}
		 
						work += adj[node].size();
					}
		 
					swap(nodes, next_nodes);
				}
		 
				if (work > 1.75 * E * (32 - __builtin_clz(V)) + 100)
					too_many_bellman_ford_iterations = true;
		 
				return prev[sink] != -1;
			}
		 
			struct dijkstra_state {
				cost_t dist;
				int node;
		 
				dijkstra_state() {}
		 
				dijkstra_state(cost_t _dist, int _node) : dist(_dist), node(_node) {}
		 
				bool operator<(const dijkstra_state &other) const {
					return dist > other.dist;
				}
			};
		 
			void dijkstra_check(int node, cost_t potential_dist, int previous, edge *previous_edge,
								priority_queue<dijkstra_state> &pq) {
				if (potential_dist < dist[node]) {
					dist[node] = potential_dist;
					prev[node] = previous;
					prev_edge[node] = previous_edge;
					pq.emplace(dist[node], node);
				}
			}
		 
			bool dijkstra(int source, int sink) {
				dist.assign(V, COST_INF);
				prev.assign(V, -1);
				prev_edge.assign(V, nullptr);
		 
				priority_queue<dijkstra_state> pq;
				dijkstra_check(source, 0, -1, nullptr, pq);
		 
				while (!pq.empty()) {
					dijkstra_state top = pq.top();
					pq.pop();
		 
					if (top.dist > dist[top.node])
						continue;
		 
					for (edge &e : adj[top.node])
						if (e.capacity > 0)
							dijkstra_check(e.node, top.dist + e.cost, top.node, &e, pq);
				}
		 
				return prev[sink] != -1;
			}
		 
			void reduce_cost() {
				for (int i = 0; i < V; i++)
					for (edge &e : adj[i])
						if (dist[i] < COST_INF && dist[e.node] < COST_INF)
							e.cost += dist[i] - dist[e.node];
			}
		 
			vector<pair<flow_t, cost_t>> options;
		 
			pair<flow_t, cost_t> solve_min_cost_flow(int source, int sink, flow_t flow_goal = numeric_limits<flow_t>::max()) {
				assert(V >= 0);
				flow_t total_flow = 0;
				cost_t total_cost = 0;
		 
				while (total_flow < flow_goal && bellman_ford(source, sink)) {
					if (too_many_bellman_ford_iterations)
						break;
		 
					flow_t path_cap = flow_goal - total_flow;
					cost_t cost_sum = 0;
		 
					for (int node = sink; prev[node] != -1; node = prev[node])
						path_cap = min(path_cap, prev_edge[node]->capacity);
		 
					for (int node = sink; prev[node] != -1; node = prev[node]) {
						edge *e = prev_edge[node];
						e->capacity -= path_cap;
						reverse_edge(*e).capacity += path_cap;
						cost_sum += e->cost;
					}
		 
					total_flow += path_cap;
					total_cost += cost_sum * path_cap;
					options.emplace_back(total_flow, total_cost);
				}
		 
				if (too_many_bellman_ford_iterations) {
					cost_t reduce_sum = 0;
		 
					do {
						reduce_cost();
						reduce_sum += dist[sink];
						flow_t path_cap = flow_goal - total_flow;
		 
						for (int node = sink; prev[node] != -1; node = prev[node])
							path_cap = min(path_cap, prev_edge[node]->capacity);
		 
						for (int node = sink; prev[node] != -1; node = prev[node]) {
							edge *e = prev_edge[node];
							assert(e->cost == 0);
							e->capacity -= path_cap;
							reverse_edge(*e).capacity += path_cap;
						}
		 
						total_flow += path_cap;
						total_cost += reduce_sum * path_cap;
						options.emplace_back(total_flow, total_cost);
					} while (total_flow < flow_goal && dijkstra(source, sink));
				}
		 
				return make_pair(total_flow, total_cost);
			}
		};
	};
	
	namespace Hungarian{
		vector<int> solve(int n, int m, const vector<vector<int>>& a){
			vector<int> u(n + 1), v(m + 1), p(m + 1), way(m + 1);
			FOR(i, 1, n + 1){
				p[0] = i;
				int j0 = 0;
				vector<int> minv(m + 1, INF);
				vector<char> used(m + 1, false);
				do {
					used[j0] = true;
					int i0 = p[j0], delta = INF, j1;
					FOR(j, 1, m + 1) if (!used[j]){
							int cur = a[i0][j] - u[i0] - v[j];
							if (cur < minv[j])
								minv[j] = cur, way[j] = j0;
							if (minv[j] < delta)
								delta = minv[j], j1 = j;
					}
					
					FOR(j, 0, m + 1) if (used[j])
						u[p[j]] += delta, v[j] -= delta;
					else
						minv[j] -= delta;
					j0 = j1;
				} while (p[j0] != 0);
				do {
					int j1 = way[j0];
					p[j0] = p[j1];
					j0 = j1;
				} while (j0);
			}
		
			vector<int> ans(n + 1);
			FOR(j, 1, m + 1){
				ans[p[j]] = j;
			}
			
			return ans;
		}
	};

	namespace FFT{
		struct complex{
			double x, y;
			complex() { x = y = 0; }
			complex(double _x, double _y) : x(_x), y(_y) { }
		};

		inline complex operator+(complex a, complex b) { return complex(a.x + b.x, a.y + b.y); }
		inline complex operator-(complex a, complex b) { return complex(a.x - b.x, a.y - b.y); }
		inline complex operator*(complex a, complex b) { return complex(a.x * b.x - a.y * b.y, a.x * b.y + a.y * b.x); }
		inline complex conj(complex a) { return complex(a.x, -a.y); }

		int base = 1;
		vector<complex> roots = { { 0, 0 },{ 1, 0 } };
		vector<int> rev = { 0, 1 };

		void ensure_base(int nbase){
			if (nbase <= base)
				return;

			rev.resize(1 << nbase);
			FOR(i, 0, 1 << nbase)
				rev[i] = (rev[i >> 1] >> 1) + ((i & 1) << (nbase - 1));

			roots.resize(1 << nbase);
			while (base < nbase){
				double angle = 2.0 * PI / (1 << (base + 1));
				FOR(i, 1 << (base - 1), 1 << base){
					roots[i << 1] = roots[i];
					double angle_i = angle * (2 * i + 1 - (1 << base));
					roots[(i << 1) + 1] = complex(cos(angle_i), sin(angle_i));
				}

				base++;
			}
		}

		void fft(vector<complex>& a, int n = -1){
			if (n == -1)
				n = a.size();

			int zeros = __builtin_ctz(n);
			ensure_base(zeros);

			int shift = base - zeros;
			FOR(i, 0, n)
				if (i < (rev[i] >> shift))
					swap(a[i], a[rev[i] >> shift]);

			for (int k = 1; k < n; k <<= 1){
				for (int i = 0; i < n; i += 2 * k){
					FOR(j, 0, k){
						complex z = a[i + j + k] * roots[j + k];
						a[i + j + k] = a[i + j] - z;
						a[i + j] = a[i + j] + z;
					}
				}
			}
		}

		vector<complex> fa, fb;

		void multiply(VI&a, VI&b, VI& res){
			int need = SZ(a) + SZ(b) - 1;
			int nbase = 0;

			while ((1 << nbase) < need)
				nbase++;

			ensure_base(nbase);
			int sz = 1 << nbase;

			if (sz > SZ(fa))
				fa.resize(sz);

			FOR(i, 0, sz){
				int x = (i < SZ(a) ? a[i] : 0);
				int y = (i < SZ(b) ? b[i] : 0);
				fa[i] = complex(x, y);
			}

			fft(fa, sz);
			complex r(0, -0.25 / sz);
			FOR(i, 0, (sz >> 1) + 1){
				int j = (sz - i) & (sz - 1);
				complex z = (fa[j] * fa[j] - conj(fa[i] * fa[i])) * r;
				if (i != j)
					fa[j] = (fa[i] * fa[i] - conj(fa[j] * fa[j])) * r;

				fa[i] = z;
			}

			fft(fa, sz);
			res.resize(need);
			FOR(i, 0, need)
				if (fa[i].x > 0)
					res[i] = fa[i].x + 0.5;
				else
					res[i] = fa[i].x - 0.5;
		}
	};

	namespace FastNTT{
		const int MOD = 998244353;
		 
		struct mod_int {
			int val;
		 
			mod_int(long long v = 0) {
				if (v < 0) v = v % MOD + MOD;
				if (v >= MOD) v %= MOD;
				val = v;
			}
		 
			static int mod_inv(int a, int m = MOD) {
				// https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm#Example
				int g = m, r = a, x = 0, y = 1;
		 
				while (r != 0) {
					int q = g / r;
					g %= r; swap(g, r);
					x -= q * y; swap(x, y);
				}
		 
				return x < 0 ? x + m : x;
			}
		 
			explicit operator int() const {
				return val;
			}
		 
			mod_int& operator+=(const mod_int &other) {
				val += other.val;
				if (val >= MOD) val -= MOD;
				return *this;
			}
		 
			mod_int& operator-=(const mod_int &other) {
				val -= other.val;
				if (val < 0) val += MOD;
				return *this;
			}
		 
			static unsigned fast_mod(uint64_t x, unsigned m = MOD) {
		#if !defined(_WIN32) || defined(_WIN64)
				return x % m;
		#endif
				// Optimized mod for Codeforces 32-bit machines.
				// x must be less than 2^32 * m for this to work, so that x / m fits in a 32-bit integer.
				unsigned x_high = x >> 32, x_low = (unsigned) x;
				unsigned quot, rem;
				asm("divl %4\n"
					: "=a" (quot), "=d" (rem)
					: "d" (x_high), "a" (x_low), "r" (m));
				return rem;
			}
		 
			mod_int& operator*=(const mod_int &other) {
				val = fast_mod((uint64_t) val * other.val);
				return *this;
			}
		 
			mod_int& operator/=(const mod_int &other) {
				return *this *= other.inv();
			}
		 
			friend mod_int operator+(const mod_int &a, const mod_int &b) { return mod_int(a) += b; }
			friend mod_int operator-(const mod_int &a, const mod_int &b) { return mod_int(a) -= b; }
			friend mod_int operator*(const mod_int &a, const mod_int &b) { return mod_int(a) *= b; }
			friend mod_int operator/(const mod_int &a, const mod_int &b) { return mod_int(a) /= b; }
		 
			mod_int& operator++() {
				val = val == MOD - 1 ? 0 : val + 1;
				return *this;
			}
		 
			mod_int& operator--() {
				val = val == 0 ? MOD - 1 : val - 1;
				return *this;
			}
		 
			mod_int operator++(int) { mod_int before = *this; ++*this; return before; }
			mod_int operator--(int) { mod_int before = *this; --*this; return before; }
		 
			mod_int operator-() const {
				return val == 0 ? 0 : MOD - val;
			}
		 
			bool operator==(const mod_int &other) const { return val == other.val; }
			bool operator!=(const mod_int &other) const { return val != other.val; }
		 
			mod_int inv() const {
				return mod_inv(val);
			}
		 
			mod_int pow(long long p) const {
				assert(p >= 0);
				mod_int a = *this, result = 1;
		 
				while (p > 0) {
					if (p & 1)
						result *= a;
		 
					a *= a;
					p >>= 1;
				}
		 
				return result;
			}
		 
			friend ostream& operator<<(ostream &stream, const mod_int &m) {
				return stream << m.val;
			}
		};
		 
		namespace NTT {
			vector<mod_int> roots = {0, 1};
			vector<int> bit_reverse;
			int max_size = -1;
			mod_int root;
		 
			bool is_power_of_two(int n) {
				return (n & (n - 1)) == 0;
			}
		 
			int round_up_power_two(int n) {
				while (n & (n - 1))
					n = (n | (n - 1)) + 1;
		 
				return max(n, 1);
			}
		 
			// Given n (a power of two), finds k such that n == 1 << k.
			int get_length(int n) {
				assert(is_power_of_two(n));
				return __builtin_ctz(n);
			}
		 
			// Rearranges the indices to be sorted by lowest bit first, then second lowest, etc., rather than highest bit first.
			// This makes even-odd div-conquer much easier.
			void bit_reorder(int n, vector<mod_int> &values) {
				if ((int) bit_reverse.size() != n) {
					bit_reverse.assign(n, 0);
					int length = get_length(n);
		 
					for (int i = 0; i < n; i++)
						bit_reverse[i] = (bit_reverse[i >> 1] >> 1) + ((i & 1) << (length - 1));
				}
		 
				for (int i = 0; i < n; i++)
					if (i < bit_reverse[i])
						swap(values[i], values[bit_reverse[i]]);
			}
		 
			void find_root() {
				max_size = 1 << __builtin_ctz(MOD - 1);
				root = 2;
		 
				// Find a max_size-th primitive root of MOD.
				while (!(root.pow(max_size) == 1 && root.pow(max_size / 2) != 1))
					root++;
			}
		 
			void prepare_roots(int n) {
				if (max_size < 0)
					find_root();
		 
				assert(n <= max_size);
		 
				if ((int) roots.size() >= n)
					return;
		 
				int length = get_length(roots.size());
				roots.resize(n);
		 
				// The roots array is set up such that for a given power of two n >= 2, roots[n / 2] through roots[n - 1] are
				// the first half of the n-th primitive roots of MOD.
				while (1 << length < n) {
					// z is a 2^(length + 1)-th primitive root of MOD.
					mod_int z = root.pow(max_size >> (length + 1));
		 
					for (int i = 1 << (length - 1); i < 1 << length; i++) {
						roots[2 * i] = roots[i];
						roots[2 * i + 1] = roots[i] * z;
					}
		 
					length++;
				}
			}
		 
			void fft_iterative(int N, vector<mod_int> &values) {
				assert(is_power_of_two(N));
				prepare_roots(N);
				bit_reorder(N, values);
		 
				for (int n = 1; n < N; n *= 2)
					for (int start = 0; start < N; start += 2 * n)
						for (int i = 0; i < n; i++) {
							mod_int even = values[start + i];
							mod_int odd = values[start + n + i] * roots[n + i];
							values[start + n + i] = even - odd;
							values[start + i] = even + odd;
						}
			}
		 
			const int FFT_CUTOFF = 150;
		 
			vector<mod_int> mod_multiply(vector<mod_int> left, vector<mod_int> right) {
				int n = left.size();
				int m = right.size();
		 
				// Brute force when either n or m is small enough.
				if (min(n, m) < FFT_CUTOFF) {
					const uint64_t ULL_BOUND = numeric_limits<uint64_t>::max() - (uint64_t) MOD * MOD;
					vector<uint64_t> result(n + m - 1, 0);
		 
					for (int i = 0; i < n; i++)
						for (int j = 0; j < m; j++) {
							result[i + j] += (uint64_t) ((int) left[i]) * ((int) right[j]);
		 
							if (result[i + j] > ULL_BOUND)
								result[i + j] %= MOD;
						}
		 
					for (uint64_t &x : result)
						if (x >= MOD)
							x %= MOD;
		 
					return vector<mod_int>(result.begin(), result.end());
				}
		 
				int N = round_up_power_two(n + m - 1);
				left.resize(N);
				right.resize(N);
		 
				bool equal = left == right;
				fft_iterative(N, left);
		 
				if (equal)
					right = left;
				else
					fft_iterative(N, right);
		 
				mod_int inv_N = mod_int(N).inv();
		 
				for (int i = 0; i < N; i++)
					left[i] *= right[i] * inv_N;
		 
				reverse(left.begin() + 1, left.end());
				fft_iterative(N, left);
				left.resize(n + m - 1);
				return left;
			}
		 
			vector<mod_int> mod_power(const vector<mod_int> &v, int exponent) {
				assert(exponent >= 0);
				vector<mod_int> result = {1};
		 
				if (exponent == 0)
					return result;
		 
				for (int k = 31 - __builtin_clz(exponent); k >= 0; k--) {
					result = mod_multiply(result, result);
		 
					if (exponent >> k & 1)
						result = mod_multiply(result, v);
				}
		 
				return result;
			}
		 
			vector<mod_int> mod_multiply_all(const vector<vector<mod_int>> &polynomials) {
				if (polynomials.empty())
					return {1};
		 
				struct compare_size {
					bool operator()(const vector<mod_int> &x, const vector<mod_int> &y) {
						return x.size() > y.size();
					}
				};
		 
				priority_queue<vector<mod_int>, vector<vector<mod_int>>, compare_size> pq(polynomials.begin(), polynomials.end());
		 
				while (pq.size() > 1) {
					vector<mod_int> a = pq.top(); pq.pop();
					vector<mod_int> b = pq.top(); pq.pop();
					pq.push(mod_multiply(a, b));
				}
		 
				return pq.top();
			}
		};

	};
	
	namespace OrderedSet{
		/*
		#include <ext/pb_ds/assoc_container.hpp>
		#include <ext/pb_ds/tree_policy.hpp> 
		using namespace __gnu_pbds;
		typedef tree<
		int,
		null_type,
		less<int>,
		rb_tree_tag,
		tree_order_statistics_node_update>
		ordered_set;
		*/
		
		
		//find_by_order(k) -> iterator to kth element
		//order_of_key(k) -> number of elements < k
	};
	
	namespace Rope{
		//#include <ext/rope> //header with rope
		//using namespace __gnu_cxx; //namespace with rope and some additional stuff
	};
	
	namespace Treap
	{
		int mrand()
		{
			return abs((rand() << 16) ^ rand());
		}
		
		struct node
		{
			// children
			int l, r;
			// priority (should be random and different)
			int y;
			// size of subtree
			int cnt;
			// parent of the vertex
			int par;
			// value of the vertex
			int val;
			// reverse push
			int rev;
			// minimum of subtree
			int mn;
			// init with value
			void init(int _val)
			{
				l = r = -1;
				y = mrand();
				cnt = 1;
				par = -1;
				val = _val;
				mn = val;
				rev = 0;
			}
		};
		// Minimum on subtree + reverse
		struct Treap
		{
			const static int MAX = 1 << 18;
			node A[MAX];
			int sz;
			int getCnt(int x)
			{
				if (x == -1) return 0;
				return A[x].cnt;
			}
			int getMn(int x)
			{
				if (x == -1) return INF;
				return A[x].mn;
			}
			int newNode(int val)
			{
				A[sz].init(val);
				sz++;
				return sz - 1;
			}
			int PB(int root, int val)
			{
				return merge(root, newNode(val));
			}
			void upd(int x)
			{
				if (x == -1) return;
				A[x].cnt = getCnt(A[x].l) + getCnt(A[x].r) + 1;
				A[x].mn = min(A[x].val, min(getMn(A[x].l), getMn(A[x].r)));
			}
			void reverse(int x)
			{
				if (x == -1) return;
				swap(A[x].l, A[x].r);
				A[x].rev ^= 1;
			}
			void push(int x)
			{
				if (x == -1 || A[x].rev == 0) return;
				reverse(A[x].l);
				reverse(A[x].r);
				A[x].rev = 0;
			}
			PII split(int x, int cnt)
			{
				if (x == -1) return MP(-1, -1);
				if (cnt == 0) return MP(-1, x);
				push(x);
				int left = getCnt(A[x].l);
				PII res;
				if (left >= cnt)
				{
					if (A[x].l != -1) A[A[x].l].par = -1;
					res = split(A[x].l, cnt);
					A[x].l = res.second;
					if (res.second != -1) A[res.second].par = x;
					res.second = x;
				}
				else
				{
					if (A[x].r != -1) A[A[x].r].par = -1;
					res = split(A[x].r, cnt - left - 1);
					A[x].r = res.first;
					if (res.first != -1) A[res.first].par = x;
					res.first = x;
				}
				upd(x);
				return res;
			}
			int merge(int x, int y)
			{
				if (x == -1) return y;
				if (y == -1) return x;
				int res;
				//if (mrand() % (getCnt(x) + getCnt(y)) < getCnt(x))
				if (A[x].y > A[y].y)
				{
					push(x);
					if (A[x].r != -1) A[A[x].r].par = -1;
					res = merge(A[x].r, y);
					A[x].r = res;
					if (res != -1) A[res].par = x;
					res = x;
				}
				else
				{
					push(y);
					if (A[y].l != -1) A[A[y].l].par = -1;
					res = merge(x, A[y].l);
					A[y].l = res;
					if (res != -1) A[res].par = y;
					res = y;
				}
				upd(res);
				return res;
			}
		};
	}
	
	namespace GraphDataStructures{

		struct UndirectedGraph
		{
			int n;
			vector<vector<PII>> g;
			vector<char> used;
			int timer;
			vector<int> tin, fup;
			UndirectedGraph() {}
			UndirectedGraph(int _n): n(_n)
			{
				g.resize(n);
				used.resize(n);
				tin.resize(n);
				fup.resize(n);
			}
			void addEdge(int u, int v, int id)
			{
				g[u].push_back({v, id});
				g[v].push_back({u, id});
			}
			void dfsBridges(int v, int p, vector<int>& bridges)
			{
				used[v] = true;
				tin[v] = fup[v] = timer++;
				for(auto e: g[v])
				{
					int to = e.first, id = e.second;
					if(to != p)
					{
						if(used[to])
							setmin(fup[v], tin[to]);
						else
						{
							dfsBridges(to, v, bridges);
							setmin(fup[v], fup[to]);
							if(fup[to] > tin[v])
								bridges.push_back(id);
						}
					}
				}
			}
			vector<int> findBridges()
			{
				timer = 0;
				used.assign(n, 0);
				vector<int> bridges;
				FOR(i, 0, n)
					if(!used[i])
						dfsBridges(i, -1, bridges);
				return bridges;
			}
		};
		
		class DirectedGraph{
		public:
			int n;
			vector<vector<int>> g, gr;
			vector<char> used;
			vector<int> order, component;

			void dfs1(int v){
				used[v] = 1;
				for(auto i: g[v]){
					if (!used[i]){
						dfs1(i);
					}
				}
				
				order.PB(v);
			}

			void dfs2(int v){
				used[v] = 1;
				component.PB(v);
				for(auto i: gr[v]){
					if (!used[i]){
						dfs2(i);
					}
				}
			}
			
			DirectedGraph(){}
			DirectedGraph(const vector<vector<int>>& _g){
				g = _g;
				n = SZ(g);
				gr.resize(n);
				FOR(i, 0, n) for(auto j: g[i]) gr[j].PB(i);
			}
			DirectedGraph(int _n, const vector<pair<int, int>>& edges){
				n = _n;
				g.resize(n);
				for(auto i: edges){
					g[i.X].PB(i.Y);
					gr[i.Y].PB(i.X);
				}		
			}
			DirectedGraph(int _n){
				n = _n;
				g.resize(n);
				gr.resize(n);
			}

			void add_directional_edge(int u, int v){
				g[u].PB(v);
				gr[v].PB(u);
			}

			vector<vector<int>> SCC(){
				used.assign(n, 0);
				FOR(i, 0, n) if (!used[i]){
					dfs1(i);
				}
				
				used.assign(n, 0);
				vector<vector<int>> ans;
				reverse(ALL(order));
				for(auto v: order) if (!used[v]){
					dfs2(v);
					ans.PB(component);
					component.clear();
				}

				return ans;
			}
		};

		template<typename T, typename R>
		class WeightedGraph{
		public:
			int n;
			vector<vector<pair<int, T>>> g;
			const bool directed_graph = true;

			vector<int> get_path(int from, int to, const vector<int>& parent){
				vector<int> res;
				res.PB(to);
				do{
					to = parent[to];
					res.PB(to);
				}while(from != to);
				reverse(ALL(res));
				return res;	
			}
			
			vector<R> Dijkstra(int source, vector<int>& parent){
				parent.assign(n, -1);
				vector<R> dist(n, -1);
				dist[source] = 0;
				set<pair<R, int>> S;
				S.insert({0, source});
				while(SZ(S)){
					int v = S.begin()->Y;
					S.erase(S.begin());

					for(auto e: g[v]){
						int to = e.X;
						T len = e.Y;
						if (dist[to] == -1 || dist[to] > dist[v] + len){
							parent[to] = v;
							S.erase({dist[to], to});
							dist[to] = dist[v] + len;
							S.insert({dist[to], to});
						}
					}
				}
				
				return dist;
			}
			
			R findMSTPrim()
			{
				assert(!directed_graph);
				R res = 0;
				vector<T> dist(n, -1);
				dist[0] = 0;
				priority_queue<pair<T, int>> pq;
				pq.push({0, 0});
				while(!pq.empty())
				{
					int dv = pq.top().first, v = pq.top().second;
					pq.pop();
					if(-dv != dist[v])
						continue;
					dist[v] = 0;
					res -= dv;
					for(auto e: g[v])
					{
						int to = e.first, w = e.second;
						if(dist[to] == -1 || w < dist[to])
						{
							dist[to] = w;
							pq.push({-dist[to], to});
						}
					}
				}
				return res;
			}
				
			WeightedGraph(){}
			WeightedGraph(int _n){
				n = _n;
				g.resize(n);
				if (directed_graph){
					cerr << "DIRECTED GRAPH!" << endl;
				}else{
					cerr << "UNDIRECTED GRAPH!" << endl;
				}
			}

			void add_edge(int u, int v, T w){		
				g[u].PB({v, w});
				if (!directed_graph){
					g[v].PB({u, w});
				}
			}
		};

		class Tree{
		public:	
			int n, lg, root;
			vector<vector<int>> g;
			vector<int> parent;
			vector<int> sz;
			vector<int> dist;
			vector<int> tin, tout;
			vector<char> U;
			vector<vector<int>> dp;
			int timer;

			inline void dfs_dp(int v, int p){
				parent[v] = dp[v][0] = p;
				FOR(i, 1, lg) dp[v][i] = dp[dp[v][i - 1]][i - 1];
				sz[v] = 1;
				tin[v] = timer++;
				for(auto i: g[v]) if (i != p){
					dist[i] = dist[v] + 1;
					dfs_dp(i, v);
					sz[v] += sz[i];
				}
				
				tout[v] = timer - 1;
			}

			inline bool is_anc(int u, int v){
				return tin[u] <= tin[v] && tout[u] >= tout[v];
			}

			inline int lca(int u, int v){
				if (is_anc(u, v)) return u;
				if (is_anc(v, u)) return v;
				RFOR(i, lg, 0) if (!is_anc(dp[u][i], v)){
					u = dp[u][i];
				}
				
				return dp[u][0];
			}

			inline int get_distance(int u, int v){
				return dist[u] + dist[v] - 2 * dist[lca(u, v)];
			}
			
			//centroids
			void dfsSz(int v, int p)
			{
				sz[v] = 1;
				for(int to: g[v])
				{
					if (to != p && !U[to])
					{
						dfsSz(to, v);
						sz[v] += sz[to];
					}
				}
			}
			
			void go(int r)
			{
				dfsSz(r, -1);
				int v = r, p = -1;
				bool ok = false;
				while (!ok)
				{
					ok = true;
					for(int to: g[v])
					{
						if (to != p && !U[to] && (sz[to] << 1) > sz[r])
						{
							p = v;
							v = to;
							ok = false;
							break;
						}
					}
				}
				U[v] = true;
				for(int to: g[v])
					if (!U[to])
						go(to);
			}
			
			Tree(){}
			Tree(int _n){
				n = _n;
				lg = 0;
				root = 0;
				while((1 << lg) < n) lg++;
				
				timer = 0;
						
				g.resize(n);
				parent.assign(n, -1);
				sz.assign(n, 0);
				tin.assign(n, 0);
				tout.assign(n, 0);
				dp.assign(n, vector<int>(lg, 0));
				dist.assign(n, 0);
				U.assign(n, 0);
			}

			void build(){
				dfs_dp(0, 0);
			}
			
			void add_edge(int u, int v){
				g[u].PB(v);
				g[v].PB(u);
			}	
		};

		class DSU{
		public:
			int n;
			vector<int> p, sz;
			DSU(){}
			
			DSU(int _n){
				n = _n;
				sz.assign(n, 1);
				p.resize(n);
				iota(ALL(p), 0);
			}

			int find(int x){
				return p[x] = (x == p[x] ? x : find(p[x]));
			}

			bool unite(int u, int v){
				u = find(u);
				v = find(v);
				if (u == v){
					return false;
				}

				if (sz[u] < sz[v]) swap(u, v);
				sz[u] += sz[v];
				p[v] = u;
				return true;
			}
		};
	
		class BipartiteMatching {
		public:
			vector<vector<int>> g;
			vector<int> r, c, vis;
			BipartiteMatching(int h = 0, int w = 0) : g(h), r(h, -1), c(w, -1), vis(h) {}
			void add_edge(int i, int j) { g[i].push_back(j); }
			bool dfs(int i) {
				if (exchange(vis[i], true)) return false;
				for (int j : g[i]) if (c[j] == -1) return r[i] = j, c[j] = i, true;
				for (int j : g[i]) if (dfs(c[j])) return r[i] = j, c[j] = i, true;
				return false;
			}
			int run(){
				while (true) {
					fill(begin(vis), end(vis), false);
					bool updated = false;
					for (int i = 0; i < (int)r.size(); ++i) if (r[i] == -1) updated |= dfs(i);
					if (not updated) break;
				}
				return r.size() - count(begin(r), end(r), -1);
			}
		};
		
		namespace MaxMatching{
			struct Edmonds
			{
				vector<vector<int>> graph;
				vector<int> label, pre, parent, visited, matching;
				queue<int> q;
				int timer;
				int n;
				
				Edmonds(int _n)
				{
					n = _n + 1;
					graph.resize(n);
					label = pre = parent = matching = visited = vector<int>(n, 0);
					timer = 0;
					n--;
				}
				
				inline int find(int x)
				{
					return parent[x] = (parent[x] == x? x : find(parent[x]));
				}
		 
				inline void unite(int u, int v)
				{
					u = find(u);
					v = find(v);
					if(u != v)
						parent[u] = v;
				}
		 
				void add_edge(int u, int v)
				{
					graph[u].PB(v);
					graph[v].PB(u);
				}
		 
				int lca(int u, int v)
				{
					timer++;
					while(true)
					{
						if(u != -1)
						{
							u = find(u);
							if(visited[u] == timer)
								return u;
								
							visited[u] = timer;
							if(matching[u] == -1)
								u = -1;
							else
								u = pre[matching[u]];
						}
						
						swap(u,v);
					}
				}
		 
				void augmenting_path(int u, int v)
				{
					pre[v] = u;
					while(v != -1)
					{
						int x = pre[v];
						int mx = matching[x];
						matching[x] = v;
						matching[v] = x;
						v = mx;
					} 
				}
		 
				void shrink_path(int u , int v)
				{
					int x,y;
					while(u != v)
					{
						x = matching[u];
						y = pre[x];
						
						if(find(y) != v) pre[y] = x;
						if(label[x] == 1)
						{
							label[x] = 0;
							q.push(x);
						}
						
						if(label[y] == 1)
						{
							label[y] = 0;
							q.push(y);
						}
		 
						unite(u, x);
						unite(x, y);
						u = y;
					}
				}
		 
				void shrink_blossom(int u , int v)
				{
					int z = lca(u,v);
					if(find(u) != z) pre[u] = v; 
					if(find(v) != z) pre[v] = u;
					shrink_path(u, z);
					shrink_path(v, z);
				}
		 
				void extend_tree(int u , int v)
				{
					pre[v] = u;
					label[v] = 1;
					label[matching[v]] = 0;
					q.push(matching[v]);
				}
		 
				int alternating_tree(int s)
				{
					while(q.size())
						q.pop();
					FOR(i, 1, n + 1)
					{
						label[i] = -1;
						parent[i] = i;
						pre[i] = -1;
					}
					
					q.push(s);
					label[s] = 0;
					
					while(q.size() && matching[s] == -1)
					{
						auto u = q.front();
						q.pop();
						
						for(auto& v: graph[u])
						{
							if(matching[u] == v || find(v) == find(u)) continue;
								
							if(label[v] == -1)
							{
								if(matching[v] == -1)
								{
									augmenting_path(u,v);
									return 1;
								}
								else
									extend_tree(u,v);					
							}
							else if(label[v] == 0)
								shrink_blossom(u, v);
						}
					}
					
					return 0;
				}
		 
				int max_matching()
				{
					fill(matching.begin(), matching.end(), -1);
					int ans = 0;
					FOR(i, 1, n + 1)
						if(matching[i] == -1)
							ans += alternating_tree(i);				
					
					return ans;
				}
			};
		}; 
	};
	
	namespace ArrayDataStructures{
		template <typename T, typename R>
		class FenwickTree{
		public:
			int n;
			vector<R> t;

			FenwickTree(){}
			void init_t(){
				t.assign(n, (R)0);
			}
			
			FenwickTree(int _n){
				n = _n;
				init_t();
			}

			FenwickTree(const vector<T>& a){
				n = SZ(a);				
				init_t();
				FOR(i, 0, n) add(i, a[i]);
			}

			FenwickTree(int _n, const T* a){
				n = _n;				
				init_t();
				FOR(i, 0, n) add(i, a[i]);
			}
			
			inline void add(int pos, T val){
				for(; pos < n; pos |= pos + 1){
					t[pos] += val;
				}
			}

			inline R query(int r){
				R res = 0;
				for(; r >= 0; r = (r & (r + 1)) - 1){
					res += t[r];
				}

				return res;
			}

			inline R query(int l, int r){
				return query(r) - query(l - 1);
			}
		};

		template<typename T>
		class SparseTable{
		public:
			int n, lg;
			vector<vector<T>> table;
			vector<T> a;

			inline T operation(const T& l, const T& r){
				return min(l, r);
			}
			
			void build(){
				FOR(i, 0, n) table[i][0] = a[i];		
				FOR(len, 0, lg - 1) FOR(i, 0, n){
					table[i][len + 1] = i + (1 << len) >= n ? table[i][len] :
					operation(table[i][len], table[i + (1 << len)][len]);			
				}
			}

			T query(int l, int r){
				const int LOG = 31 - __builtin_clz(r - l + 1);
				return operation(table[l][LOG], table[r - (1 << LOG) + 1][LOG]);
			}

			void init(){
				lg = 1;
				while((1 << lg) <= n) lg++;

				table.resize(n);
				FOR(i, 0, n) table[i].resize(lg);
				
				build();
			}
			
			SparseTable(){}
			SparseTable(const vector<T>& A){
				n = SZ(A);
				a = A;
				init();
			}

			SparseTable(int _n, const T* A){
				n = _n;
				a.resize(n);
				FOR(i, 0, n) a[i] = A[i];
				init();
			}	
		};
		
		template<class T>
		struct SegTree{
		/* sum
			const T shit = 0;
			T op(T a, T b){
				return a + b;
			}*/
		/* min
			const T shit = INF;
			T op(T a, T b){
				return min(a, b);
			}
		*/
		/* max
			const T shit = -INF;
			T op(T a, T b){
				return max(a, b);
			}
		
		*/
		/* minLL
			const T shit = LINF;
			T op(T a, T b){
				return min(a, b);
			}
		*/
		/* maxLL
			const T shit = -LINF;
			T op(T a, T b){
				return max(a, b);
			}
		
		*/
		const T shit; //SEEEEEEET
		T op(T a, T b){
			//SEEEEEEET
		}
		
		int n;
		vector<T> t;
		SegTree(int _n):n(_n){
			int lg = 0;
			while((1 << lg) < n)
				lg++;
			lg++;
			t.resize((1 << lg), shit);
		}
		T sum(int v, int tl, int tr, int l, int r){
			if(l > r)
				return shit;
			if(tl == l && tr == r)
				return t[v];
			int tm = (tl + tr) / 2;
			return op(sum(2 * v, tl, tm, l, min(tm, r)),
			sum(2 * v + 1, tm + 1, tr, max(l, tm + 1), r));
		}
		T sum(int l, int r){ 
			return sum(1, 0, n - 1, l, r);
		}
		void upd_set(int v, int tl, int tr, int pos, T new_val){
			if(tl == tr)
			{
				t[v] = new_val;
				return;
			}
			int tm = (tl + tr) / 2;
			if(pos <= tm)
				upd_set(2 * v, tl, tm, pos, new_val);
			else
				upd_set(2 * v + 1, tm + 1, tr, pos, new_val);
			t[v] = op(t[2 * v], t[2 * v + 1]);
		} 
		void upd_set(int pos, T new_val){
			upd_set(1, 0, n - 1, pos, new_val);
		}
		void upd_add(int v, int tl, int tr, int pos, T new_val){
			if(tl == tr)
			{
				t[v] = op(t[v], new_val);
				return;
			}
			int tm = (tl + tr) / 2;
			if(pos <= tm)
				upd_add(2 * v, tl, tm, pos, new_val);
			else
				upd_add(2 * v + 1, tm + 1, tr, pos, new_val);
			t[v] = op(t[2 * v], t[2 * v + 1]);
		} 
		void upd_add(int pos, T new_val){
			upd_add(1, 0, n - 1, pos, new_val);
		}
	};
		
		template<class T>
		struct PerSegTree{
			const T shit = 0;
			struct node
			{
				T val;
				int l = -1, r = -1;
				node(T x): val(x) {}
				node() {}
				T operator+(const node& obj) const
				{
					return val + obj.val;
				}
			};
			vector<node> t; // array of size 4 * n + q * logn
			int sz = 0;
			int build(int tl, int tr, const vector<T>& A)
			{
				int V = sz++;
				t.PB(node());
				if(tl == tr)
				{
					t[V].val = A[tl];
					return V;
				}
				int tm = (tl + tr) / 2;
				t[V].l = build(tl, tm, A);
				t[V].r = build(tm + 1, tr, A);
				t[V].val = t[t[V].l] + t[t[V].r];
				return V;
			}
			int upd_add(int v, int tl, int tr, int pos, T val)
			{
				int V = sz++;
				t.PB(node());
				t[V] = t[v];
				
				if(tl == tr)
				{
					t[V].val += val;
					return V;
				}
				int tm = (tl + tr) / 2;
				if(pos <= tm)
					t[V].l = upd_add(t[v].l, tl, tm, pos, val);
				else
					t[V].r = upd_add(t[v].r, tm + 1, tr, pos, val);
				t[V].val = t[t[V].l] + t[t[V].r];
				return V;
			}
			T sum(int v, int tl, int tr, int l, int r)
			{
				if(l > r)
					return shit;
				if(tl == l && tr == r)
					return t[v].val;
				int tm = (tl + tr) / 2;
				return sum(t[v].l, tl, tm, l, min(r, tm)) + 
				sum(t[v].r, tm + 1, tr, max(l, tm + 1), r);
			}
		};

	};

	namespace TrieXor{
		const int BIT = 30;
		const int A = 2;	
		class Trie{
		public:	
			struct node{
				int cnt;
				int nxt[A];
				node(){
					cnt = 0;
					FILL(nxt, -1);
				}
			};

			vector<node> a;
			Trie(){
				a.PB(node());
			}	
				
			void add(int x){
				int v = 0;
				RFOR(i, BIT, 0){			
					bool tut = (x & (1 << i)) > 0;
					if (a[v].nxt[tut] == -1){
						a[v].nxt[tut] = SZ(a);
						a.PB(node());
					}

					v = a[v].nxt[tut];
					a[v].cnt++;
				}
			}

			void remove(int x){
				int v = 0;
				RFOR(i, BIT, 0){			
					bool tut = (x & (1 << i)) > 0;
					v = a[v].nxt[tut];
					a[v].cnt--;
				}
			}

			int query(int x){//min {x XOR w | w є S}
				int res = 0;
				int v = 0;
				RFOR(i, BIT, 0){
					bool tut = (x & (1 << i)) > 0;
					if (a[v].nxt[tut] != -1 && a[a[v].nxt[tut]].cnt > 0){
						v  = a[v].nxt[tut];
					}else{
						v = a[v].nxt[tut ^ 1];
						res |= 1 << i;
					}			
				}
				
				return res;
			}
		};
	};

	namespace ConvexHullTrick{
		struct Line {
			mutable LL k, m, p;
			bool operator<(const Line& o) const { return k < o.k; }
			bool operator<(LL x) const { return p < x; }
		};

		struct LineContainer : multiset<Line, less<>> {
			// (for doubles, use inf = 1/.0, div(a,b) = a/b)
			const LL inf = LLONG_MAX;
			LL div(LL a, LL b) {return a / b - ((a ^ b) < 0 && a % b); }
			bool isect(iterator x, iterator y) {
				if (y == end()) { x->p = inf; return false; }
				if (x->k == y->k) x->p = x->m > y->m ? inf : -inf;
				else x->p = div(y->m - x->m, x->k - y->k);
				return x->p >= y->p;
			}
			void add(LL k, LL m) {
				auto z = insert({k, m, 0}), y = z++, x = y;
				while (isect(y, z)) z = erase(z);
				if (x != begin() && isect(--x, y)) isect(x, y = erase(y));
				while ((y = x) != begin() && (--x)->p >= y->p)
					isect(x, erase(y));
			}
			LL query(LL x) {//for maximum
				assert(!empty());
				auto l = *lower_bound(x);
				return l.k * x + l.m;
			}
		};
	};
	
	namespace Algebra {
		//USAGE https://cp-algorithms.com/algebra/polynomial.html

		const int inf = 1e9;
		const int magic = 500; // threshold for sizes to run the naive algo
		
		namespace fft {
			const int maxn = 1 << 18;

			typedef double ftype;
			typedef complex<ftype> point;

			point w[maxn];
			const ftype pi = acos(-1);
			bool initiated = 0;
			void init() {
				if(!initiated) {
					for(int i = 1; i < maxn; i *= 2) {
						for(int j = 0; j < i; j++) {
							w[i + j] = polar(ftype(1), pi * j / i);
						}
					}
					initiated = 1;
				}
			}
			template<typename T>
			void fft(T *in, point *out, int n, int k = 1) {
				if(n == 1) {
					*out = *in;
				} else {
					n /= 2;
					fft(in, out, n, 2 * k);
					fft(in + k, out + n, n, 2 * k);
					for(int i = 0; i < n; i++) {
						auto t = out[i + n] * w[i + n];
						out[i + n] = out[i] - t;
						out[i] += t;
					}
				}
			}
			
			template<typename T>
			void mul_slow(vector<T> &a, const vector<T> &b) {
				vector<T> res(a.size() + b.size() - 1);
				for(size_t i = 0; i < a.size(); i++) {
					for(size_t j = 0; j < b.size(); j++) {
						res[i + j] += a[i] * b[j];
					}
				}
				a = res;
			}
			
			
			template<typename T>
			void mul(vector<T> &a, const vector<T> &b) {
				if(min(a.size(), b.size()) < magic) {
					mul_slow(a, b);
					return;
				}
				init();
				static const int shift = 15, mask = (1 << shift) - 1;
				size_t n = a.size() + b.size() - 1;
				while(__builtin_popcount(n) != 1) {
					n++;
				}
				a.resize(n);
				static point A[maxn], B[maxn];
				static point C[maxn], D[maxn];
				for(size_t i = 0; i < n; i++) {
					A[i] = point(a[i] & mask, a[i] >> shift);
					if(i < b.size()) {
						B[i] = point(b[i] & mask, b[i] >> shift);
					} else {
						B[i] = 0;
					}
				}
				fft(A, C, n); fft(B, D, n);
				for(size_t i = 0; i < n; i++) {
					point c0 = C[i] + conj(C[(n - i) % n]);
					point c1 = C[i] - conj(C[(n - i) % n]);
					point d0 = D[i] + conj(D[(n - i) % n]);
					point d1 = D[i] - conj(D[(n - i) % n]);
					A[i] = c0 * d0 - point(0, 1) * c1 * d1;
					B[i] = c0 * d1 + d0 * c1;
				}
				fft(A, C, n); fft(B, D, n);
				reverse(C + 1, C + n);
				reverse(D + 1, D + n);
				int t = 4 * n;
				for(size_t i = 0; i < n; i++) {
					int64_t A0 = llround(real(C[i]) / t);
					T A1 = llround(imag(D[i]) / t);
					T A2 = llround(imag(C[i]) / t);
					a[i] = A0 + (A1 << shift) + (A2 << 2 * shift);
				}
				return;
			}
		}
		template<typename T>
		T bpow(T x, size_t n) {
			return n ? n % 2 ? x * bpow(x, n - 1) : bpow(x * x, n / 2) : T(1);
		}
		template<typename T>
		T bpow(T x, size_t n, T m) {
			return n ? n % 2 ? x * bpow(x, n - 1, m) % m : bpow(x * x % m, n / 2, m) : T(1);
		}
		template<typename T>
		T gcd(const T &a, const T &b) {
			return b == T(0) ? a : gcd(b, a % b);
		}
		template<typename T>
		T nCr(T n, int r) { // runs in O(r)
			T res(1);
			for(int i = 0; i < r; i++) {
				res *= (n - T(i));
				res /= (i + 1);
			}
			return res;
		}

		template<int m>
		struct modular {
			int64_t r;
			modular() : r(0) {}
			modular(int64_t rr) : r(rr) {if(abs(r) >= m) r %= m; if(r < 0) r += m;}
			modular inv() const {return bpow(*this, m - 2);}
			modular operator * (const modular &t) const {return (r * t.r) % m;}
			modular operator / (const modular &t) const {return *this * t.inv();}
			modular operator += (const modular &t) {r += t.r; if(r >= m) r -= m; return *this;}
			modular operator -= (const modular &t) {r -= t.r; if(r < 0) r += m; return *this;}
			modular operator + (const modular &t) const {return modular(*this) += t;}
			modular operator - (const modular &t) const {return modular(*this) -= t;}
			modular operator *= (const modular &t) {return *this = *this * t;}
			modular operator /= (const modular &t) {return *this = *this / t;}
			
			bool operator == (const modular &t) const {return r == t.r;}
			bool operator != (const modular &t) const {return r != t.r;}
			
			operator int64_t() const {return r;}
		};
		template<int T>
		istream& operator >> (istream &in, modular<T> &x) {
			return in >> x.r;
		}
		
		
		template<typename T>
		struct poly {
			vector<T> a;
			
			void normalize() { // get rid of leading zeroes
				while(!a.empty() && a.back() == T(0)) {
					a.pop_back();
				}
			}
			
			poly(){}
			poly(T a0) : a{a0}{normalize();}
			poly(vector<T> t) : a(t){normalize();}
			
			poly operator += (const poly &t) {
				a.resize(max(a.size(), t.a.size()));
				for(size_t i = 0; i < t.a.size(); i++) {
					a[i] += t.a[i];
				}
				normalize();
				return *this;
			}
			poly operator -= (const poly &t) {
				a.resize(max(a.size(), t.a.size()));
				for(size_t i = 0; i < t.a.size(); i++) {
					a[i] -= t.a[i];
				}
				normalize();
				return *this;
			}
			poly operator + (const poly &t) const {return poly(*this) += t;}
			poly operator - (const poly &t) const {return poly(*this) -= t;}
			
			poly mod_xk(size_t k) const { // get same polynomial mod x^k
				k = min(k, a.size());
				return vector<T>(begin(a), begin(a) + k);
			}
			poly mul_xk(size_t k) const { // multiply by x^k
				poly res(*this);
				res.a.insert(begin(res.a), k, 0);
				return res;
			}
			poly div_xk(size_t k) const { // divide by x^k, dropping coefficients
				k = min(k, a.size());
				return vector<T>(begin(a) + k, end(a));
			}
			poly substr(size_t l, size_t r) const { // return mod_xk(r).div_xk(l)
				l = min(l, a.size());
				r = min(r, a.size());
				return vector<T>(begin(a) + l, begin(a) + r);
			}
			poly inv(size_t n) const { // get inverse series mod x^n
				assert(!is_zero());
				poly ans = a[0].inv();
				size_t A = 1;
				while(A < n) {
					poly C = (ans * mod_xk(2 * A)).substr(A, 2 * A);
					ans -= (ans * C).mod_xk(A).mul_xk(A);
					A *= 2;
				}
				return ans.mod_xk(n);
			}
			
			poly operator *= (const poly &t) {fft::mul(a, t.a); normalize(); return *this;}
			poly operator * (const poly &t) const {return poly(*this) *= t;}
			
			poly reverse(size_t n, bool rev = 0) const { // reverses and leaves only n terms
				poly res(*this);
				if(rev) { // If rev = 1 then tail goes to head
					res.a.resize(max(n, res.a.size()));
				}
				std::reverse(res.a.begin(), res.a.end());
				return res.mod_xk(n);
			}
			
			pair<poly, poly> divmod_slow(const poly &b) const { // when divisor or quotient is small
				vector<T> A(a);
				vector<T> res;
				while(A.size() >= b.a.size()) {
					res.push_back(A.back() / b.a.back());
					if(res.back() != T(0)) {
						for(size_t i = 0; i < b.a.size(); i++) {
							A[A.size() - i - 1] -= res.back() * b.a[b.a.size() - i - 1];
						}
					}
					A.pop_back();
				}
				std::reverse(begin(res), end(res));
				return {res, A};
			}
			
			pair<poly, poly> divmod(const poly &b) const { // returns quotiend and remainder of a mod b
				if(deg() < b.deg()) {
					return {poly{0}, *this};
				}
				int d = deg() - b.deg();
				if(min(d, b.deg()) < magic) {
					return divmod_slow(b);
				}
				poly D = (reverse(d + 1) * b.reverse(d + 1).inv(d + 1)).mod_xk(d + 1).reverse(d + 1, 1);
				return {D, *this - D * b};
			}
			
			poly operator / (const poly &t) const {return divmod(t).first;}
			poly operator % (const poly &t) const {return divmod(t).second;}
			poly operator /= (const poly &t) {return *this = divmod(t).first;}
			poly operator %= (const poly &t) {return *this = divmod(t).second;}
			poly operator *= (const T &x) {
				for(auto &it: a) {
					it *= x;
				}
				normalize();
				return *this;
			}
			poly operator /= (const T &x) {
				for(auto &it: a) {
					it /= x;
				}
				normalize();
				return *this;
			}
			poly operator * (const T &x) const {return poly(*this) *= x;}
			poly operator / (const T &x) const {return poly(*this) /= x;}
			
			void print() const {
				for(auto it: a) {
					cout << it << ' ';
				}
				cout << endl;
			}
			T eval(T x) const { // evaluates in single point x
				T res(0);
				for(int i = int(a.size()) - 1; i >= 0; i--) {
					res *= x;
					res += a[i];
				}
				return res;
			}
			
			T& lead() { // leading coefficient
				return a.back();
			}
			int deg() const { // degree
				return a.empty() ? -inf : a.size() - 1;
			}
			bool is_zero() const { // is polynomial zero
				return a.empty();
			}
			T operator [](int idx) const {
				return idx >= (int)a.size() || idx < 0 ? T(0) : a[idx];
			}
			
			T& coef(size_t idx) { // mutable reference at coefficient
				return a[idx];
			}
			bool operator == (const poly &t) const {return a == t.a;}
			bool operator != (const poly &t) const {return a != t.a;}
			
			poly deriv() { // calculate derivative
				vector<T> res;
				for(int i = 1; i <= deg(); i++) {
					res.push_back(T(i) * a[i]);
				}
				return res;
			}
			poly integr() { // calculate integral with C = 0
				vector<T> res = {0};
				for(int i = 0; i <= deg(); i++) {
					res.push_back(a[i] / T(i + 1));
				}
				return res;
			}
			size_t leading_xk() const { // Let p(x) = x^k * t(x), return k
				if(is_zero()) {
					return inf;
				}
				int res = 0;
				while(a[res] == T(0)) {
					res++;
				}
				return res;
			}
			poly log(size_t n) { // calculate log p(x) mod x^n
				assert(a[0] == T(1));
				return (deriv().mod_xk(n) * inv(n)).integr().mod_xk(n);
			}
			poly exp(size_t n) { // calculate exp p(x) mod x^n
				if(is_zero()) {
					return T(1);
				}
				assert(a[0] == T(0));
				poly ans = T(1);
				int A = 1;
				while(A < n) {
					poly C = ans.log(2 * a).div_xk(A) - substr(A, 2 * A);
					ans -= (ans * C).mod_xk(A).mul_xk(A);
					A *= 2;
				}
				return ans.mod_xk(n);
				
			}
			poly pow_slow(size_t k, size_t n) { // if k is small
				return k ? k % 2 ? (*this * pow_slow(k - 1, n)).mod_xk(n) : (*this * *this).mod_xk(n).pow_slow(k / 2, n) : T(1);
			}
			poly pow(size_t k, size_t n) { // calculate p^k(n) mod x^n
				if(is_zero()) {
					return *this;
				}
				if(k < magic) {
					return pow_slow(k, n);
				}
				int i = leading_xk();
				T j = a[i];
				poly t = div_xk(i) / j;
				return bpow(j, k) * (t.log(n) * T(k)).exp(n).mul_xk(i * k).mod_xk(n);
			}
			poly mulx(T x) { // component-wise multiplication with x^k
				T cur = 1;
				poly res(*this);
				for(int i = 0; i <= deg(); i++) {
					res.coef(i) *= cur;
					cur *= x;
				}
				return res;
			}
			poly mulx_sq(T x) { // component-wise multiplication with x^{k^2}
				T cur = x;
				T total = 1;
				T xx = x * x;
				poly res(*this);
				for(int i = 0; i <= deg(); i++) {
					res.coef(i) *= total;
					total *= cur;
					cur *= xx;
				}
				return res;
			}
			vector<T> chirpz_even(T z, int n) { // P(1), P(z^2), P(z^4), ..., P(z^2(n-1))
				int m = deg();
				if(is_zero()) {
					return vector<T>(n, 0);
				}
				vector<T> vv(m + n);
				T zi = z.inv();
				T zz = zi * zi;
				T cur = zi;
				T total = 1;
				for(int i = 0; i <= max(n - 1, m); i++) {
					if(i <= m) {vv[m - i] = total;}
					if(i < n) {vv[m + i] = total;}
					total *= cur;
					cur *= zz;
				}
				poly w = (mulx_sq(z) * vv).substr(m, m + n).mulx_sq(z);
				vector<T> res(n);
				for(int i = 0; i < n; i++) {
					res[i] = w[i];
				}
				return res;
			}
			vector<T> chirpz(T z, int n) { // P(1), P(z), P(z^2), ..., P(z^(n-1))
				auto even = chirpz_even(z, (n + 1) / 2);
				auto odd = mulx(z).chirpz_even(z, n / 2);
				vector<T> ans(n);
				for(int i = 0; i < n / 2; i++) {
					ans[2 * i] = even[i];
					ans[2 * i + 1] = odd[i];
				}
				if(n % 2 == 1) {
					ans[n - 1] = even.back();
				}
				return ans;
			}
			template<typename iter>
			vector<T> eval(vector<poly> &tree, int v, iter l, iter r) { // auxiliary evaluation function
				if(r - l == 1) {
					return {eval(*l)};
				} else {
					auto m = l + (r - l) / 2;
					auto A = (*this % tree[2 * v]).eval(tree, 2 * v, l, m);
					auto B = (*this % tree[2 * v + 1]).eval(tree, 2 * v + 1, m, r);
					A.insert(end(A), begin(B), end(B));
					return A;
				}
			}
			vector<T> eval(vector<T> x) { // evaluate polynomial in (x1, ..., xn)
				int n = x.size();
				if(is_zero()) {
					return vector<T>(n, T(0));
				}
				vector<poly> tree(4 * n);
				build(tree, 1, begin(x), end(x));
				return eval(tree, 1, begin(x), end(x));
			}
			template<typename iter>
			poly inter(vector<poly> &tree, int v, iter l, iter r, iter ly, iter ry) { // auxiliary interpolation function
				if(r - l == 1) {
					return {*ly / a[0]};
				} else {
					auto m = l + (r - l) / 2;
					auto my = ly + (ry - ly) / 2;
					auto A = (*this % tree[2 * v]).inter(tree, 2 * v, l, m, ly, my);
					auto B = (*this % tree[2 * v + 1]).inter(tree, 2 * v + 1, m, r, my, ry);
					return A * tree[2 * v + 1] + B * tree[2 * v];
				}
			}
		};
		template<typename T>
		poly<T> operator * (const T& a, const poly<T>& b) {
			return b * a;
		}
		
		template<typename T>
		poly<T> xk(int k) { // return x^k
			return poly<T>{1}.mul_xk(k);
		}

		template<typename T>
		T resultant(poly<T> a, poly<T> b) { // computes resultant of a and b
			if(b.is_zero()) {
				return 0;
			} else if(b.deg() == 0) {
				return bpow(b.lead(), a.deg());
			} else {
				int pw = a.deg();
				a %= b;
				pw -= a.deg();
				T mul = bpow(b.lead(), pw) * T((b.deg() & a.deg() & 1) ? -1 : 1);
				T ans = resultant(b, a);
				return ans * mul;
			}
		}
		template<typename iter>
		poly<typename iter::value_type> kmul(iter L, iter R) { // computes (x-a1)(x-a2)...(x-an) without building tree
			if(R - L == 1) {
				return vector<typename iter::value_type>{-*L, 1};
			} else {
				iter M = L + (R - L) / 2;
				return kmul(L, M) * kmul(M, R);
			}
		}
		template<typename T, typename iter>
		poly<T> build(vector<poly<T>> &res, int v, iter L, iter R) { // builds evaluation tree for (x-a1)(x-a2)...(x-an)
			if(R - L == 1) {
				return res[v] = vector<T>{-*L, 1};
			} else {
				iter M = L + (R - L) / 2;
				return res[v] = build(res, 2 * v, L, M) * build(res, 2 * v + 1, M, R);
			}
		}
		template<typename T>
		poly<T> inter(vector<T> x, vector<T> y) { // interpolates minimum polynomial from (xi, yi) pairs
			int n = x.size();
			vector<poly<T>> tree(4 * n);
			return build(tree, 1, begin(x), end(x)).deriv().inter(tree, 1, begin(x), end(x), begin(y), end(y));
		}
	};
	
	namespace FastFactorization{
		#warning ZABERY DEFINE __uint128_t uint64_t
		#define __uint128_t uint64_t
		namespace Internal{
			template<typename T> uint64_t trailing_zero_bits(const T& element)
			{
				return __builtin_ctzll(element);
			}

			struct Montgomery
			{
				uint64_t n;
				static uint64_t modulus, inverse, r2;

				Montgomery() : n{0}
				{
				}

				Montgomery(const uint64_t& x) : n{init(x)}
				{
				}

				static uint64_t init(const uint64_t& w)
				{
					return redc(__uint128_t(w) * r2);
				}

				static void set_modulus(const uint64_t& m)
				{
					modulus = inverse = m;
					for(int i{}; i < 5; i++)
					{ inverse *= 2 - inverse * m; }
					r2 = -__uint128_t(m) % m;
				}

				static uint64_t redc(const __uint128_t& x)
				{
					uint64_t y{uint64_t(x >> 64) - uint64_t((__uint128_t(uint64_t(x) * inverse) * modulus) >> 64)};
					return int64_t(y) < 0 ? y + modulus : y;
				}

				Montgomery& operator+=(const Montgomery& other)
				{
					n += other.n - modulus;
					if(int64_t(n) < 0)
					{ n += modulus; }
					return *this;
				}

				Montgomery& operator+(const Montgomery& other) const
				{
					return Montgomery(*this) += other;
				}

				Montgomery& operator*=(const Montgomery& other)
				{
					n = redc(__uint128_t(n) * other.n);
					return *this;
				}

				Montgomery& operator*(const Montgomery& other) const
				{
					return Montgomery(*this) *= other;
				}

				uint64_t value() const
				{
					return redc(n);
				}
			};

			uint64_t Montgomery::modulus, Montgomery::inverse, Montgomery::r2;

			namespace primality
			{

				template<typename T> Montgomery power(const Montgomery& base, T exponent)
				{
					Montgomery mBase = base, result(1);
					while(exponent)
					{
						if(exponent & 1)
						{ result *= mBase; }
						mBase *= mBase;
						exponent >>= 1;
					}
					return result;
				}

				constexpr array<uint_fast64_t, 7> A{2, 325, 9375, 28178, 450775, 9780504, 1795265022};

				template<typename T> bool miller_rabin(const T& n)
				{
					if(Montgomery::modulus != n)
					{ Montgomery::set_modulus(n); }
					T bits{trailing_zero_bits(n - 1)}, d{(n - 1) >> bits};
					Montgomery one{1}, negativeOne{n - 1};
					for(const T& a : A)
					{
						Montgomery mA{a};
						if(mA.n)
						{
							T i{};
							Montgomery x{power(mA, d)};
							if(x.n == one.n || x.n == negativeOne.n)
							{ continue; }
							for(; x.n != one.n && x.n != negativeOne.n && i < bits; ++i)
							{
								if(x.n == one.n)
								{ return false; }
								if(x.n == negativeOne.n)
								{ break; }
								x *= x;
							}
							if((i == bits) ^ (x.n == one.n))
							{ return false; }
						}
						else
						{ return true; }
					}
					return true;
				}
			}

			inline mt19937_64& getPRNG()
			{
				static mt19937_64 PRNG{static_cast<uint64_t>( chrono::duration_cast<chrono::nanoseconds>(chrono::steady_clock::now().time_since_epoch()).count())};
				return PRNG;
			}

			template<typename T1, typename T2> typename common_type<T1, T2>::type getUID(const T1& uLow, const T2& uHigh)
			{
				typename common_type<T1, T2>::type low{uLow}, high{uHigh};
				return uniform_int_distribution<typename common_type<T1, T2>::type>(low, high)(getPRNG());
			}

			template<typename T1, typename T2> constexpr typename common_type<T1, T2>::type steins_gcd(const T1& u_x, const T2& u_y)
			{
				typename common_type<T1, T2>::type x{u_x}, y{u_y};
				if(x == 0)
				{
					return y;
				}
				if(y == 0)
				{
					return x;
				}
				typename common_type<T1, T2>::type a{trailing_zero_bits(x)}, b{trailing_zero_bits(y)};
				x >>= a;
				y >>= b;
				while(true)
				{
					if(x < y)
					{
						swap(x, y);
					}
					x -= y;
					if(!x)
					{
						return y << min(a, b);
					}
					x >>= trailing_zero_bits(x);
				}
			}

			namespace factors
			{
				template<typename T> T optimized_rho(const T& n)
				{
					if(primality::miller_rabin(n))
					{ return n; }
					auto f{[](const Montgomery& x, const T& c) -> Montgomery
						   {
							   Montgomery result = x;
							   (result *= result) += c;
							   return result;
						   }};
					T factor, c{getUID<T>(1, n - 1)};
					Montgomery x{getUID<T>(1, n - 1)}, y{f(x, c)}, product{1};
					for(T trials{}; trials % 128 || (factor = steins_gcd(product.value(), n)) == 1; x = f(x, c), y = f(f(y, c), c))
					{
						if(x.n == y.n)
						{
							c = getUID<T>(1, n - 1);
							x = Montgomery(getUID<T>(1, n - 1));
							y = f(x, c);
						}
						Montgomery combined{product};
						combined *= (max(x.n, y.n) - min(x.n, y.n));
						if(combined.n && combined.n != product.n)
						{
							++trials;
							product = combined;
						}
					}
					return factor;
				}

				template<typename T> vector<T> optimized_rho_factorize(const T& n, const bool& checkBaseCases = true)
				{
					T factor = optimized_rho<T>(n);
					if(n == factor)
					{ return vector<T>{n}; }
					vector<T> original{optimized_rho_factorize(factor, false)}, divided{optimized_rho_factorize(n / factor, false)};
					move(begin(divided), end(divided), back_inserter(original));
					return original;
				}
				
				
			}
		};
		
		vector<uint_fast64_t> factorize(uint64_t n){//returns list of all prime divisors (possibly non-distinct)
			constexpr array<uint_fast16_t, 64> primes{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311};
			vector<uint_fast64_t> result;
			for(const auto& prime : primes){
				if(prime > n) break;
				while(n % prime == 0){
					result.push_back(prime);
					n /= prime;
				}
			}
			if(n == 1){
				return result;
			}
			else{
				auto rho = Internal::factors::optimized_rho_factorize<uint_fast64_t>(n);
				sort(begin(rho), end(rho));
				for(auto i: rho){
					result.PB(i);
				}
				
				return result;
			}
		}
	};
	
	namespace Other{
		template<typename T>
		T gcd (T a, T b, T& x, T& y) {
			if (a == 0) {
				x = 0; y = 1;
				return b;
			}
			
			T x1, y1;
			T d = gcd(b%a, a, x1, y1);
			x = y1 - (b / a) * x1;
			y = x1;
			return d;
		}
	};

	namespace Geometry{
		const double EPS = 1e-7;
		/*struct Point
		{
			double x, y;
			Point() {}
			Point(double _x, double _y) : x(_x), y(_y) {};
			Point operator-(const Point& p)const
			{
				return Point (x - p.x, y - p.y);
			}
			Point operator+(const Point& p)const
			{
				return Point (x + p.x, y + p.y);
			}
			double operator*(const Point & p) const
			{
				return x * p.y - y * p.x;
			}
			Point operator*(double k) const
			{
				return Point(k * x, k * y);
			}
			double d2() const
			{
				return x * x + y * y;
			}
			double len() const
			{
				return sqrt(d2());
			}
			bool operator==(const Point & p) const
			{
				return abs(x - p.x) < EPS && abs(y - p.y) < EPS;
			}
			bool operator<(const Point & p) const
			{
				if (abs(x - p.x) > EPS)return x < p.x;
				if (abs(y - p.y) > EPS)return y < p.y;
				return 0;
			}
			Point rotate(double cosx, double sinx) const //ccw
			{
				double xx = x * cosx - y * sinx;
				double yy = x * sinx + y * cosx;
				return Point(xx, yy);
			}
			Point rotate(double ang) const //ccw
			{
				return rotate(cos(ang), sin(ang));
			}
			Point scale(double l) const //assuming len of vector > 0
			{
				l /= len();
				return Point(l * x, l * y);
			}
			double dot(const Point& p) const
			{
				return x * p.x + y * p.y;
			}
			double polar() const // (-PI; PI]
			{
				double ang = atan2(y, x);
				if (ang < -EPS)ang += 2 * PI; // if need [0; 2 * PI)
				return ang;
			}
			int hp() const //halfpalne relative to X-axis
			{
				return y < -EPS || (abs(y) < EPS && x < -EPS);
			}
		};
		int sign(double x)
		{
			if (abs(x) < EPS)return 0;
			return x > 0 ? 1 : -1;
		}*/

		struct Point{
			LL x, y;
			Point() {}
			Point(LL _x, LL _y): x(_x), y(_y) {}
			Point operator-(const Point& p)const
			{
				return Point (x - p.x, y - p.y);
			}
			Point operator+(const Point& p)const
			{
				return Point (x + p.x, y + p.y);
			}
			LL operator*(const Point & p) const
			{
				return x * p.y - y * p.x;
			}
			LL d2() const
			{
				return x * x + y * y;
			}
			double len() const
			{
				return sqrt(d2());
			}
			bool operator==(const Point& p) const
			{
				return x == p.x && y == p.y;
			}
			bool operator<(const Point& p) const
			{
				return x == p.x ? y < p.y : x < p.x;
			}
			LL dot(const Point& p) const
			{
				return x * p.x + y * p.y;
			}
			int hp() const //halfpalne relative to X-axis
			{
				return y < 0 || (y == 0 && x < 0);
			}
		};

		int sign(LL x)
		{
			if (x == 0)
				return 0;
			return x > 0 ? 1 : -1;
		}

		bool cmpVec(const Point& a, const Point& b) //sort by polar angle [0; 2*PI)
		{
			if (a.hp() != b.hp())return a.hp() < b.hp();
			return a * b > EPS;
		}

		struct Line
		{
			Point n;
			double c;
			Line() {}
			Line(double a, double b, double _c): n(a, b), c(_c) {}
			Line(Point a, Point b) // assuming a != b
			{
				double A = b.y - a.y;
				double B = a.x - b.x;
				double C = -a.x * A - a.y * B;
				n = Point(A, B);
				c = C;
			}
			double dist(const Point & p) const //oriented
			{
				return (n.dot(p) + c) / n.len();
			}
			/*Point clothestPoint(const Point& p) const
			{
				return p + n.scale(-dist(p));
			}*/
			bool paralel(const Line& l) const
			{
				return abs(n * l.n) < EPS;
			}
			Point intersect(const Line &l) const
			{
				//assuming that Lines are not parallel
				double z = n * l.n;
				double x = - (c * l.n.y - n.y * l.c) / z;
				double y = - (n.x * l.c - c * l.n.x) / z;
				return Point(x, y);
			}
		};
		struct Segment
		{
			Point a, b;
			Segment() {}
			Segment(Point _a, Point _b): a(_a), b(_b) {}
			Line getLine() const
			{
				return Line(a, b);
			}
			bool contains(const Point& p) const
			{
				return abs((a - b).len() - (a - p).len() - (b - p).len()) < EPS;
			}
			bool intersect(const Segment& s) const
			{
				if (min(s.a.x, s.b.x) > max(a.x, b.x))return false;
				if (min(s.a.y, s.b.y) > max(a.y, b.y))return false;
				if (max(s.a.x, s.b.x) < min(a.x, b.x))return false;
				if (max(s.a.y, s.b.y) < min(a.y, b.y))return false;
				int s1 = sign((a - s.a) * (b - s.a));
				int s2 = sign((a - s.b) * (b - s.b));
				int s3 = sign((s.a - a) * (s.b - a));
				int s4 = sign((s.a - b) * (s.b - b));
				return s1 * s2 <= 0 && s3 * s4 <= 0;
			}
			/*double dist(const Point& p) const //not oriented
			{
				Point q = getLine().clothestPoint(p);
				if (contains(q))return (p-q).len();
				return min((a-p).len(), (b-p).len());
			}
			double dist(const Segment& s) const
			{
				if (intersect(s))return 0;
				double ans = min(dist(s.a), dist(s.b));
				ans = min(ans, s.dist(a));
				ans = min(ans, s.dist(b));
				return ans;
			}*/
		};
		bool triangleContains(const Point& a, const Point& b, const Point& c, const Point& p)
		{
			int s1 = sign((b - a) * (p - a));
			int s2 = sign((c - b) * (p - b));
			int s3 = sign((a - c) * (p - c));
			return (s1 >= 0 && s2 >= 0 && s3 >= 0) || (s1 <= 0 && s2 <= 0 && s3 <= 0);
		}
		struct Polygon
		{
			vector<Point> p;
			Polygon() {}
			Polygon(const vector<Point> &a)
			{
				p = a;
				if (SZ(a))p.PB(a[0]);
			}
			int sz() const
			{
				return max(SZ(p) - 1, 0);
			}
			Polygon convex() const //returns ccw-ordered
			{
				vector<Point> pp = p;
				if (SZ(pp))pp.pop_back();
				sort(ALL(pp));
				vector<Point> U, D;
				FOR(i, 0, SZ(pp))
				{
					while(SZ(D) > 1 && sign((D.back() - D[SZ(D) - 2]) * (pp[i] - D[SZ(D)
					- 2])) <= 0)D.pop_back();
					while(SZ(U) > 1 && sign((U.back() - U[SZ(U) - 2]) * (pp[i] - U[SZ(U)
					- 2])) >= 0)U.pop_back();
					U.PB(pp[i]);
					D.PB(pp[i]);
				}
				reverse(ALL(U));
				FOR(i, 1, SZ(U)-1)
				D.PB(U[i]);
				return Polygon(D);
			}
			//randomised, could be used for not convex Polygons
			/*bool contains(const Point& x) const
			{
				double MX = sqrt(3) * PI / 47.7 + 123.23424;
				double MY = sqrt(2) * acos(0.47747) + 4 * PI;
				Point v = Point(MX, MY).scale(1e8); //v should be strictly outside Polygon;
				Segment S = Segment(x, v);
				int cnt = 0;
				FOR(i, 0, SZ(p)-1)
				{
					Segment seg = Segment(p[i], p[i+1]);
					if (seg.contains(x))return 1;
					if (seg.intersect(S))cnt++;
				}
				return cnt % 2;
			}*/
			bool contains2(const Point& q) const
			{
				if (!sz())return false;
				if (sz() == 1)return p[0] == q;
				int l = 1, r = sz()-1;
				int s1 = sign((p[l] - p[0]) * (q - p[0]));
				int s2 = sign((p[r] - p[0]) * (q - p[0]));
				if (s1 == -1)return 0;
				if (s2 == 1)return 0;
				while(r - l > 1)
				{
					int m = (l + r) / 2;
					int s = sign((p[m] - p[0]) * (q - p[0]));
					if (s <= 0)r = m;
					else l = m;
				}
				return triangleContains(p[0], p[l], p[r], q);
			}
		};

		/*struct Circle
		{
			Point O;
			double r;
			Circle() {}
			Circle(Point _O, double _r): O(_O), r(_r) {}
			vector<Point> intersect(const Line& l) const
			{
				vector<Point> ans;
				double d = l.dist(O);
				if (abs(d) > r + EPS)return ans;
				double cosx = r < EPS ? 1.0 : -d/r;
				double sinx = sqrt(abs(1.0 - cosx * cosx));
				ans.PB(O + l.n.rotate(cosx, sinx).scale(r));
				if (abs(sinx) > EPS)ans.PB(O + l.n.rotate(cosx, -sinx).scale(r));
				return ans;
			}
			vector<Point> intersect(const Circle& c) const
			{
				Point v = c.O - O;
				double A = -2.0 * v.x;
				double B = -2.0 * v.y;
				double C = v.d2() + r * r - c.r * c.r;
				Line l = Line(A, B, C);
				vector<Point> ans = Circle(Point(0, 0), r).intersect(l);
				FOR(i, 0, SZ(ans))
				ans[i] = ans[i] + O;
				return ans;
			}
			vector<Line> tangents(const Point& p) const
			{
				Point v = p - O;
				vector<Line> ans;
				double d = v.len();
				if (d < r - EPS)return ans;
				if(abs(d - r) < EPS)
				{
					return {Line(v.x, v.y, -v.dot(p))};
				}
				double cosx = r/d;
				double sinx = sqrt(abs(1.0 - cosx * cosx));
				Point p1 = O + v.rotate(cosx, sinx).scale(r);
				Point p2 = O + v.rotate(cosx, -sinx).scale(r);
				ans.PB(Line(p, p1));
				if (!(p2 == p1))ans.PB(Line(p, p2));
				return ans;
			}
			void _add_tan(const Point& c, double r1, double r2, vector<Line>& res) const
			{
				double rr = r2 - r1;
				double z = c.d2();
				double d = z - rr * rr;
				if (d < -EPS)return ;
				d = sqrt(abs(d));
				double a = (c.x * rr + c.y * d) / z;
				double b = (c.y * rr - c.x * d) / z;
				res.PB(Line(a, b, r1 - a * O.x - b * O.y));
			}
			vector<Line> common_tangents(const Circle& C) const
			{
				vector<Line> ans;
				if (O == C.O)return ans;
				Point OO = C.O - O;
				_add_tan(OO, -r, -C.r, ans);
				_add_tan(OO, -r, C.r, ans);
				_add_tan(OO, r, -C.r, ans);
				_add_tan(OO, r, C.r, ans);
				return ans;
			}
			double distOnCircle(const Point& p1, const Point& p2) const
			{
				//assuming that both Points are on Circle
				double a1 = (p1 - O).polar();
				double a2 = (p2 - O).polar();
				if(a1 > a2) swap(a1,a2);
				return min(a2 - a1, 2 * PI - (a2 - a1)) * r;
			}
			bool contains(const Point& p) const
			{
				return (O-p).d2() < r * r + EPS;
			}
		};*/
	};

	namespace BlockCutTree{
		struct graph
		{
			int n;
			vector<vector<int>> adj;
		 
			graph(int _n) : n(_n), adj(_n) {}
		 
			void add_edge(int u, int v)
			{
				adj[u].push_back(v);
				adj[v].push_back(u);
			}
		 
			int add_node()
			{
				adj.push_back({});
				return n++;
			}
		 
			vector<int>& operator[](int u) { return adj[u]; }
		};
		 
		vector<vector<int>> biconnected_components(graph &adj)
		{
			int n = adj.n;
		 
			vector<int> num(n), low(n), art(n), stk;
			vector<vector<int>> comps;
		 
			function<void(int, int, int&)> dfs = [&](int u, int p, int &t)
			{
				num[u] = low[u] = ++t;
				stk.push_back(u);
		 
				for (int v : adj[u]) if (v != p)
				{
					if (!num[v])
					{
						dfs(v, u, t);
						low[u] = min(low[u], low[v]);
		 
						if (low[v] >= num[u])
						{
							art[u] = (num[u] > 1 || num[v] > 2);
		 
							comps.push_back({u});
							while (comps.back().back() != v)
								comps.back().push_back(stk.back()), stk.pop_back();
						}
					}
					else low[u] = min(low[u], num[v]);
				}
			};
		 
			for (int u = 0, t; u < n; ++u)
				if (!num[u]) dfs(u, -1, t = 0);
		 
			// build the block cut tree
			function<graph()> build_tree = [&]()
			{
				graph tree(0);
				vector<int> id(n);
		 
				for (int u = 0; u < n; ++u)
					if (art[u]) id[u] = tree.add_node();
		 
				for (auto &comp : comps)
				{
					int node = tree.add_node();
					for (int u : comp)
						if (!art[u]) id[u] = node;
						else tree.add_edge(node, id[u]);
				}
		 
				return tree;
			};
		 
			return comps;
		}
	};
	
	struct DominatorTree {
		vector<basic_string<int>> g, rg, bucket;
		vector<int> arr, par, rev, sdom, dom, dsu, label;
		int n, t;
		DominatorTree(int _n) : g(_n), rg(_n), bucket(_n), arr(_n, -1),
			par(_n), rev(_n), sdom(_n), dom(_n), dsu(_n), label(_n), n(_n), t(0) {}
		void add_edge(int u, int v) { g[u] += v; }
		void dfs(int u) {
			arr[u] = t;
			rev[t] = u;
			label[t] = sdom[t] = dsu[t] = t;
			t++;
			for (int w : g[u]) {
				if (arr[w] == -1) {
					dfs(w);
					par[arr[w]] = arr[u];
				}
				rg[arr[w]] += arr[u];
			}
		}
		int find(int u, int x = 0) {
			if (u == dsu[u])
				return x ? -1 : u;
			int v = find(dsu[u], x+1);
			if (v < 0)
				return u;
			if (sdom[label[dsu[u]]] < sdom[label[u]])
				label[u] = label[dsu[u]];
			dsu[u] = v;
			return x ? v : label[u];
		}
		vector<int> run(int root) { //for i != root: outside_dom[i] = i -> no dominator
			dfs(root);
			iota(dom.begin(), dom.end(), 0);
			for (int i=t-1; i>=0; i--) {
				for (int w : rg[i])
					sdom[i] = min(sdom[i], sdom[find(w)]);
				if (i)
					bucket[sdom[i]] += i;
				for (int w : bucket[i]) {
					int v = find(w);
					if (sdom[v] == sdom[w])
						dom[w] = sdom[w];
					else
						dom[w] = v;
				}
				if (i > 1)
					dsu[i] = par[i];
			}
			for (int i=1; i<t; i++) {
				if (dom[i] != sdom[i])
					dom[i] = dom[dom[i]];
			}
			vector<int> outside_dom(n);
			iota(begin(outside_dom), end(outside_dom), 0);
			for (int i=0; i<t; i++)
				outside_dom[rev[i]] = rev[dom[i]];
			return outside_dom;
		}
	};

	namespace Convolutions{
		using namespace IntModulo;
		//after inverse convolutions /(1<<k)
		void conv_xor(VI& a, int k){
			//assert(SZ(a) == (1 << k));
			FOR(i, 0, k)
				FOR(j, 0, 1 << k)
					if((j&(1<<i)) == 0)
					{
						int u = a[j];
						int v = a[j + (1 << i)];
						a[j] = add(u, v);
						a[j + (1 << i)] = sub(u, v);
					}  
		}
		VI mult_xor(VI a, VI b, int k){
			conv_xor(a, k);
			conv_xor(b, k);
			FOR(i, 0, 1 << k)
				a[i] = mult(a[i], b[i]);
			conv_xor(a, k);
			int inv = inverse(SZ(a));
			FOR(i, 0, 1 << k)
				a[i] = mult(a[i], inv);
			return a;
		}

		void conv_or(VI& a, int k){
			FOR(i, 0, k)
				FOR(j, 0, 1 << k)
					if((j&(1<<i))==0)
						a[j + (1 << i)] = add(a[j + (1 << i)], a[j]);
		}
		void inverse_or(VI& a, int k){
			FOR(i, 0, k)
				FOR(j, 0, 1 << k)
					if((j&(1<<i))==0)
						a[j + (1 << i)] = sub(a[j + (1 << i)], a[j]);
		}
		VI mult_or(VI a, VI b, int k){
			conv_or(a, k);
			conv_or(b, k);
			FOR(i, 0, 1 << k)
				a[i] = mult(a[i], b[i]);
			inverse_or(a, k);
			return a;
		}

		void conv_and(VI& a, int k){
			FOR(i, 0, k)
				FOR(j, 0, 1 << k)
					if((j&(1<<i))==0)
						a[j] = add(a[j], a[j + (1 << i)]);
		}
		void inverse_and(VI& a, int k){
			FOR(i, 0, k)
				FOR(j, 0, 1 << k)
					if((j&(1<<i))==0)
						a[j] = sub(a[j], a[j + (1 << i)]);
		}
		VI mult_and(VI a, VI b, int k){
			conv_and(a, k);
			conv_and(b, k);
			FOR(i, 0, 1 << k)
				a[i] = mult(a[i], b[i]);
			inverse_and(a, k);
			return a;
		}
	};

	namespace Strings{
		struct SuffixArray {
			string s;
			int n;
			vector<int> SA,rev;

			SuffixArray() {}
			SuffixArray(const string& s_) : s(s_), n(int(s.size())) {
				vector<int> s2(n);
				for (int i = 0; i < n; i++) {
					s2[i] = s[i];
				}
				SA = sa_is(s2, 255);
				rev.resize(n);
				for (int i = 0; i < n; i++) {
					rev[SA[i]] = i;
				}
			}

			int operator[](int i) const {
				assert(0 <= i and i < n);
				return SA[i];
			}

			bool lt_substr(const string& t, int si, int ti) {
				int tn = int(t.size());
				while(si < n && ti < tn) {
					if(s[si] < t[ti]) return 1;
					if(s[si] > t[ti]) return 0;
					si++; ti++;
				}
				return si == n && ti < tn;
			}

			int lower_bound(const string& t) {
				int l = -1, r = n;
				while(l + 1 < r) {
					int m = (l+r)>>1;
					if(lt_substr(t,SA[m],0)) l = m;
					else r = m;
				}
				return r;
			}

			int upper_bound(string& t) {
				t.back()++;
				int res=lower_bound(t);
				t.back()--;
				return res;
			}

			// O(|T|*log|S|)
			int count(string& t) {
				return upper_bound(t)-lower_bound(t);
			}

			private:
			vector<int> sa_naive(const vector<int>& s_) {
				int n_ = int(s_.size());
				vector<int> sa(n_);
				iota(sa.begin(), sa.end(), 0);
				sort(sa.begin(), sa.end(), [&](int l, int r) {
					if (l == r) return false;
					while (l < n_ && r < n_) {
						if (s_[l] != s_[r]) return s_[l] < s_[r];
						l++;
						r++;
					}
					return l == n_;
				});
				return sa;
			}

			vector<int> sa_doubling(const vector<int>& s_) {
				int n_ = int(s_.size());
				vector<int> sa(n_), rnk = s_, tmp(n_);
				iota(sa.begin(), sa.end(), 0);
				for (int k = 1; k < n_; k *= 2) {
					auto cmp = [&](int x, int y) {
						if (rnk[x] != rnk[y]) return rnk[x] < rnk[y];
						int rx = x + k < n_ ? rnk[x + k] : -1;
						int ry = y + k < n_ ? rnk[y + k] : -1;
						return rx < ry;
					};
					sort(sa.begin(), sa.end(), cmp);
					tmp[sa[0]] = 0;
					for (int i = 1; i < n_; i++) {
						tmp[sa[i]] = tmp[sa[i - 1]] + (cmp(sa[i - 1], sa[i]) ? 1 : 0);
					}
					swap(tmp, rnk);
				}
				return sa;
			}

			template <int THRESHOLD_NAIVE = 10, int THRESHOLD_DOUBLING = 40>
			vector<int> sa_is(const vector<int>& s_, int upper) {
				int n_ = int(s_.size());
				if (n_ == 0) return {};
				if (n_ == 1) return {0};
				if (n_ == 2) {
					if (s_[0] < s_[1]) {
						return {0, 1};
					} else {
						return {1, 0};
					}
				}
				if (n_ < THRESHOLD_NAIVE) {
					return sa_naive(s_);
				}
				if (n_ < THRESHOLD_DOUBLING) {
					return sa_doubling(s_);
				}

				vector<int> sa(n_);
				vector<bool> ls(n_);
				for (int i = n_ - 2; i >= 0; i--) {
					ls[i] = (s_[i] == s_[i + 1]) ? ls[i + 1] : (s_[i] < s_[i + 1]);
				}
				vector<int> sum_l(upper + 1), sum_s(upper + 1);
				for (int i = 0; i < n_; i++) {
					if (!ls[i]) {
						sum_s[s_[i]]++;
					} else {
						sum_l[s_[i] + 1]++;
					}
				}
				for (int i = 0; i <= upper; i++) {
					sum_s[i] += sum_l[i];
					if (i < upper) sum_l[i + 1] += sum_s[i];
				}

				auto induce = [&](const vector<int>& lms) {
					fill(sa.begin(), sa.end(), -1);
					vector<int> buf(upper + 1);
					copy(sum_s.begin(), sum_s.end(), buf.begin());
					for (auto d : lms) {
						if (d == n_) continue;
						sa[buf[s_[d]]++] = d;
					}
					copy(sum_l.begin(), sum_l.end(), buf.begin());
					sa[buf[s_[n_ - 1]]++] = n_ - 1;
					for (int i = 0; i < n_; i++) {
						int v = sa[i];
						if (v >= 1 && !ls[v - 1]) {
							sa[buf[s_[v - 1]]++] = v - 1;
						}
					}
					copy(sum_l.begin(), sum_l.end(), buf.begin());
					for (int i = n_ - 1; i >= 0; i--) {
						int v = sa[i];
						if (v >= 1 && ls[v - 1]) {
							sa[--buf[s_[v - 1] + 1]] = v - 1;
						}
					}
				};

				vector<int> lms_map(n_ + 1, -1);
				int m = 0;
				for (int i = 1; i < n_; i++) {
					if (!ls[i - 1] && ls[i]) {
						lms_map[i] = m++;
					}
				}
				vector<int> lms;
				lms.reserve(m);
				for (int i = 1; i < n_; i++) {
					if (!ls[i - 1] && ls[i]) {
						lms.push_back(i);
					}
				}

				induce(lms);

				if (m) {
					vector<int> sorted_lms;
					sorted_lms.reserve(m);
					for (int v : sa) {
						if (lms_map[v] != -1) sorted_lms.push_back(v);
					}
					vector<int> rec_s(m);
					int rec_upper = 0;
					rec_s[lms_map[sorted_lms[0]]] = 0;
					for (int i = 1; i < m; i++) {
						int l = sorted_lms[i - 1], r = sorted_lms[i];
						int end_l = (lms_map[l] + 1 < m) ? lms[lms_map[l] + 1] : n_;
						int end_r = (lms_map[r] + 1 < m) ? lms[lms_map[r] + 1] : n_;
						bool same = true;
						if (end_l - l != end_r - r) {
							same = false;
						} else {
							while (l < end_l) {
								if (s_[l] != s_[r]) {
									break;
								}
								l++;
								r++;
							}
							if (l == n_ || s_[l] != s_[r]) same = false;
						}	
						if (!same) rec_upper++;
						rec_s[lms_map[sorted_lms[i]]] = rec_upper;
					}

					auto rec_sa =
					sa_is<THRESHOLD_NAIVE, THRESHOLD_DOUBLING>(rec_s, rec_upper);

					for (int i = 0; i < m; i++) {
						sorted_lms[i] = lms[rec_sa[i]];
					}
					induce(sorted_lms);
				}
				return sa;
			}
		};
		
		struct LongestCommonPrefix {
			SuffixArray sa;
			vector<int> ht;
			vector<vector<int>> node;

			LongestCommonPrefix(const string& S) : sa(S) {
				int n = SZ(S);
				assert(n >= 1);

				vector<int> lcp(n-1);
				int h = 0;
				for (int i = 0; i < n; i++) {
					if (h > 0) h--;
					if (sa.rev[i] == 0) continue;
					int j = sa[sa.rev[i] - 1];
					for (; j + h < n && i + h < n; h++) {
						if (S[j + h] != S[i + h]) break;
					}
					lcp[sa.rev[i] - 1] = h;
				}

				h = 1;
				while ((1<<h) <= n-1) h++;
				node.assign(h, vector<int>(n-1,0));
				ht.assign((1<<h)+1,0);
				for (int j = 2; j < (1<<h)+1; j++) ht[j] = ht[j>>1] + 1;

				for (int j = 0; j < n-1; j++) node[0][j] = lcp[j];
				for (int i = 1; i < h; i++) {
					int s = 1 << i;
					for (int j = 0; j < n-1; j += s<<1) {
						int t = min(j+s, n-1);
						node[i][t-1] = lcp[t-1];
						for (int k = t-2; k >= j; k--) node[i][k] = min(lcp[k],node[i][k+1]);
						if (n-1 <= t) break;
						node[i][t] = lcp[t];
						int r = min(t+s,n-1);
						for (int k = t+1; k < r; k++) node[i][k] = min(node[i][k-1],lcp[k]);
					}
				}
			}

			// a, b are indices for suffix array
			int query(int a, int b) {
				assert(a != b);
				if(a > b) swap(a,b);
				if(a >= --b) return node[0][a];
				return min(node[ht[a^b]][a],node[ht[a^b]][b]);
			}    

			// a, b are indices for string
			int get_lcp(int a, int b) {
				return query(sa.rev[a],sa.rev[b]);
			}
		};
		
		namespace Automat{
			const int MAX = 1 << 19;
			struct node{
				int g[26];
				int link, len;
				void init(){
					FILL(g, -1);
					link = len = -1;
				}
			};
			struct automaton{
				node A[MAX * 2];
				int sz, head;
				void init(){
					sz = 1; head = 0;
					A[0].init();
				}
				void add(char x){
					int ch = x - 'a';
					int nhead = sz++;
					A[nhead].init();
					A[nhead].len = A[head].len + 1;
					int cur = head;
					head = nhead;
					while(cur != -1 && A[cur].g[ch] == -1)
					{
						A[cur].g[ch] = head;
						cur = A[cur].link;
					}
					if(cur == -1)
					{
						A[head].link = 0;
						return;
					}
					int p = A[cur].g[ch];
					if(A[p].len == A[cur].len + 1)
					{
						A[head].link = p;
						return;
					}
					int q = sz++;
					A[q] = A[p];
					A[q].len = A[cur].len + 1;
					A[p].link = A[head].link = q;
					while(cur != -1 && A[cur].g[ch] == p)
					{
						A[cur].g[ch] = q;
						cur = A[cur].link;
					}
				}
			};
		};
	 
		namespace Z_func{
			template <class T> std::vector<int> z_algorithm(const std::vector<T>& s) {
				int n = int(s.size());
				if (n == 0) return {};
				std::vector<int> z(n);
				z[0] = 0;
				for (int i = 1, j = 0; i < n; i++) {
					int& k = z[i];
					k = (j + z[j] <= i) ? 0 : std::min(j + z[j] - i, z[i - j]);
					while (i + k < n && s[k] == s[i + k]) k++;
					if (j + z[j] < i + z[i]) j = i;
				}
				z[0] = n;
				return z;
			}

			std::vector<int> z_algorithm(const std::string& s) {
				int n = int(s.size());
				std::vector<int> s2(n);
				for (int i = 0; i < n; i++) {
					s2[i] = s[i];
				}
				return z_algorithm(s2);
			}
		}

		namespace P_func{
			template <class T> std::vector<int> p_algorithm(const std::vector<T>& s) {
				int n = SZ(s);
				if (n == 0) return {};
				vector<int> pi (n);
				for (int i = 1; i < n; ++i) {
					int j = pi[i - 1];
					while (j > 0 && s[i] != s[j])
						j = pi[j - 1];
					if (s[i] == s[j])  ++j;
					pi[i] = j;
				}
				return pi;
			}

			std::vector<int> p_algorithm(const std::string& s) {
				int n = int(s.size());
				std::vector<int> s2(n);
				for (int i = 0; i < n; i++) {
					s2[i] = s[i];
				}
				return p_algorithm(s2);
			}
		}

		namespace Aho_Corasick{
			const int MAX = 1 << 17;
			const int AL = 30;
			struct node{
				int p;
				int c;
				int g[AL];
				int nxt[AL];
				int link;
				void init(){
					c = -1;
					p = -1;
					FILL(g,-1);
					FILL(nxt,-1);
					link = -1;
				}

			};

			struct AC{
				node A[MAX];
				int sz;
				void init(){
					A[0].init();
					sz = 1;
				}
				int AddStr(string & s) {//returns vertex number for string
					int x = 0;
					FOR(i, 0, SZ(s)){
						int c = s[i] - 'a';
						if(A[x].nxt[c] == -1){
							A[x].nxt[c] = sz;
							A[sz].init();
							A[sz].c = c;
							A[sz].p = x;
							sz++;
						}
						x = A[x].nxt[c];
					}
					return x;
				}
				int go(int x, int c){
					if(A[x].g[c] == -1)
					{
						if(A[x].nxt[c] != -1)
							A[x].g[c] = A[x].nxt[c];
						else if (x != 0)
							A[x].g[c] = go(getLink(x), c);
						else
							A[x].g[c] = 0;
					}
					return A[x].g[c];
				}
				int getLink(int x){
					if(A[x].link == -1)
					{
						if(x == 0 || A[x].p == 0) return 0;
						A[x].link = go(getLink(A[x].p), A[x].c);
					}
					return A[x].link;
				}

			};
		};
		
		struct Manacher {
			vector<int> p[2];
			// i | i + 1 -> p[0][i + 1]
			// i -> p[1][i]
			Manacher(const string &s) {
				int n = SZ(s);
				p[0].resize(n + 1); p[1].resize(n);

				for (int z = 0; z < 2; z++)
					for (int i = 0, l = 0, r = 0; i < n; i++) {
						int t = r - i + !z;
						if (i < r) p[z][i] = min(t, p[z][l + t]);
						int L = i - p[z][i], R = i + p[z][i] - !z;
						while (L >= 1 && (R + 1 < n) && s[L - 1] == s[R + 1])   p[z][i]++, L--, R++;
						if (R > r) l = L, r = R;
					}
			}

			bool ispalin(int l, int r) {
				int mid = (l + r + 1) / 2, sz = r - l + 1;
				return 2 * p[sz%2][mid] + sz%2 >= sz;
			}
		};

	};

	namespace GaussianModulo{
		using namespace IntModulo;
		struct Matrix
		{
			int n, m;
			vector<vector<int>> a;
			Matrix() {}
			// different for square and rectangular matrices
			void read()
			{
				cin >> n >> m;
				//m = n;
				a.resize(n);
				FOR(i, 0, n)
				{
					a[i].resize(m);
					for(int& x: a[i])
						cin >> x;
				}
			}
			
			// if n=m returns det
			// else returns some shit
			int eliminate()
			{
				int r = 0, res = 1;
				FOR(j, 0, m)
				{
					int nonZero = -1;
					FOR(i, r, n)
						if(a[i][j] != 0)
							nonZero = i;
					if(nonZero == -1)
						continue;
					if(nonZero != r)
					{
						swap(a[r], a[nonZero]);
						res *= -1;
					}
					int k = inverse(a[r][j]);
					FOR(i, r + 1, n)
					{
						int coef = mult(a[i][j], k);
						FOR(l, j, m)
							SUB(a[i][l], mult(coef, a[r][l]));
					}
					r++;
				}
				if(res == -1)
					res = mod - 1;
				if(n == m)
					FOR(i, 0, n)
						MULT(res, a[i][i]);
				return res;
			}
			
			// if there is no solution returns empty vector
			// else returns any of them
			vector<int> solveSystem(const vector<int>& b) const
			{
				Matrix matr = *this;
				assert(SZ(b) == n);
				matr.m++;
				FOR(i, 0, n)
					matr.a[i].push_back(b[i]);
				matr.eliminate();
				vector<int> x(m, 0);
				RFOR(i, n, 0)
				{
					int rhs = matr.a[i][m];
					int pos = -1;
					FOR(j, 0, m)
					{
						if(matr.a[i][j] != 0)
						{
							if(pos == -1)
								pos = j;
							else
								SUB(rhs, mult(matr.a[i][j], x[j]));
						}
					}
					if(pos == -1)
					{
						if(matr.a[i][m] != 0)
							return vector<int>();
					}
					else
						x[pos] = mult(rhs, inverse(matr.a[i][pos]));
				}
				return x;
			}
			
			vector<vector<int>> findBasis() const
			{
				Matrix matr = *this;
				matr.eliminate();
				vector<char> inBasis(matr.m, 0);
				FOR(i, 0, n)
					FOR(j, 0, m)
						if(matr.a[i][j] != 0)
						{
							inBasis[j] = true;
							break;
						}
				vector<vector<int>> res;
				FOR(k, 0, m)
				{
					if(!inBasis[k])
					{
						vector<int> x(m, 0);
						x[k] = 1;
						RFOR(i, n, 0)
						{
							int rhs = 0;
							int pos = -1;
							FOR(j, 0, m)
							{
								if(matr.a[i][j] != 0)
								{
									if(pos == -1)
										pos = j;
									else
										SUB(rhs, mult(matr.a[i][j], x[j]));
								}
							}
							if(pos != -1)
								x[pos] = mult(rhs, inverse(matr.a[i][pos]));
						}
						res.push_back(x);
					}
				}
				return res;
			}
		};
	};

	template<class S>
	struct HLD{
		ArrayDataStructures::SegTree<S> T;
		int n;
		vector<VI> g;
		VI sz, tin, tout, P, par;
		int t;
		HLD(int _n): T(2 * _n), n(_n), g(_n), sz(_n, 0), tin(sz), tout(sz), P(_n), par(_n), t(0) {}
		void add_edge(int u, int v){
			g[u].PB(v);
			g[v].PB(u);
		}
		int dfs_sz(int v, int p){
			sz[v] = 1;
			for(int to : g[v])
				if(to != p)
					sz[v] += dfs_sz(to, v);
			FOR(i, 0, SZ(g[v]) - 1)
				if(g[v][i] == p)
					swap(g[v][i], g[v][i + 1]);		
			if(v != p){
				assert(g[v].back() == p);
				g[v].pop_back();
			}
			sort(ALL(g[v]), [&](int i, int j){return sz[i] > sz[j];});
			par[v] = p;
			return sz[v];
		}
		void dfs(int v, int last){
			P[v] = last;
			tin[v] = t++;
			FOR(i, 0, SZ(g[v]))
			{
				int to = g[v][i];
				dfs(to, (i ? to : last));
			}
			tout[v] = t;
		}
		void run(int root){
			dfs_sz(root, root);
			dfs(root, root);
		}
		bool is_par(int v, int p){
			return tin[p] <= tin[v] && tout[v] <= tout[p];
		}
		void upd_vert(int v, S val){
			//T.upd_add(1, 0, n - 1, tin[v], val);
		}
		void upd_path(int v, int u, S val){
			FOR(i, 0, 2){
				while(!is_par(v, P[u])){
					//T.upd(1, 0, t, tin[P[u]], tin[u], val);
					//update on path P[u] - u
					u = par[P[u]];
				}
				swap(u, v);
			}
			if(is_par(v, u))
				swap(u, v);
			assert(is_par(u, v));
			//T.upd(1, 0, t, tin[v], tin[u], val);	
			//update on path v - u
		
		}
		S sum(int v, int u){
			S ans = T.shit;
			FOR(i, 0, 2){
				while(!is_par(v, P[u])){
					//ans = ans + T.sum(1, 0, t, tin[P[u]], tin[u]);
					// sum on path P[u] - u
					u = par[P[u]];
				}
				swap(u, v);
			}
			if(is_par(v, u))
				swap(u, v);
			assert(is_par(u, v));
			//ans += T.sum(1, 0, t, tin[v], tin[u]);
			// sum on path v - u
			return ans;
		}
	};
};

namespace AtcoderLibrary{
	namespace MaxFlow{
		
		namespace atcoder {

		namespace internal {

		template <class T> struct simple_queue {
			std::vector<T> payload;
			int pos = 0;
			void reserve(int n) { payload.reserve(n); }
			int size() const { return int(payload.size()) - pos; }
			bool empty() const { return pos == int(payload.size()); }
			void push(const T& t) { payload.push_back(t); }
			T& front() { return payload[pos]; }
			void clear() {
				payload.clear();
				pos = 0;
			}
			void pop() { pos++; }
		};

		}  // namespace internal

		}  // namespace atcoder


		namespace atcoder {

		template <class Cap> struct mf_graph {
		  public:
			mf_graph() : _n(0) {}
			explicit mf_graph(int n) : _n(n), g(n) {}

			int add_edge(int from, int to, Cap cap) {
				assert(0 <= from && from < _n);
				assert(0 <= to && to < _n);
				assert(0 <= cap);
				int m = int(pos.size());
				pos.push_back({from, int(g[from].size())});
				int from_id = int(g[from].size());
				int to_id = int(g[to].size());
				if (from == to) to_id++;
				g[from].push_back(_edge{to, to_id, cap});
				g[to].push_back(_edge{from, from_id, 0});
				return m;
			}

			struct edge {
				int from, to;
				Cap cap, flow;
			};

			edge get_edge(int i) {
				int m = int(pos.size());
				assert(0 <= i && i < m);
				auto _e = g[pos[i].first][pos[i].second];
				auto _re = g[_e.to][_e.rev];
				return edge{pos[i].first, _e.to, _e.cap + _re.cap, _re.cap};
			}
			std::vector<edge> edges() {
				int m = int(pos.size());
				std::vector<edge> result;
				for (int i = 0; i < m; i++) {
					result.push_back(get_edge(i));
				}
				return result;
			}
			void change_edge(int i, Cap new_cap, Cap new_flow) {
				int m = int(pos.size());
				assert(0 <= i && i < m);
				assert(0 <= new_flow && new_flow <= new_cap);
				auto& _e = g[pos[i].first][pos[i].second];
				auto& _re = g[_e.to][_e.rev];
				_e.cap = new_cap - new_flow;
				_re.cap = new_flow;
			}

			Cap flow(int s, int t) {
				return flow(s, t, std::numeric_limits<Cap>::max());
			}
			Cap flow(int s, int t, Cap flow_limit) {
				assert(0 <= s && s < _n);
				assert(0 <= t && t < _n);
				assert(s != t);

				std::vector<int> level(_n), iter(_n);
				internal::simple_queue<int> que;

				auto bfs = [&]() {
					std::fill(level.begin(), level.end(), -1);
					level[s] = 0;
					que.clear();
					que.push(s);
					while (!que.empty()) {
						int v = que.front();
						que.pop();
						for (auto e : g[v]) {
							if (e.cap == 0 || level[e.to] >= 0) continue;
							level[e.to] = level[v] + 1;
							if (e.to == t) return;
							que.push(e.to);
						}
					}
				};
				auto dfs = [&](auto self, int v, Cap up) {
					if (v == s) return up;
					Cap res = 0;
					int level_v = level[v];
					for (int& i = iter[v]; i < int(g[v].size()); i++) {
						_edge& e = g[v][i];
						if (level_v <= level[e.to] || g[e.to][e.rev].cap == 0) continue;
						Cap d =
							self(self, e.to, std::min(up - res, g[e.to][e.rev].cap));
						if (d <= 0) continue;
						g[v][i].cap += d;
						g[e.to][e.rev].cap -= d;
						res += d;
						if (res == up) return res;
					}
					level[v] = _n;
					return res;
				};

				Cap flow = 0;
				while (flow < flow_limit) {
					bfs();
					if (level[t] == -1) break;
					std::fill(iter.begin(), iter.end(), 0);
					Cap f = dfs(dfs, t, flow_limit - flow);
					if (!f) break;
					flow += f;
				}
				return flow;
			}

			std::vector<bool> min_cut(int s) {
				std::vector<bool> visited(_n);
				internal::simple_queue<int> que;
				que.push(s);
				while (!que.empty()) {
					int p = que.front();
					que.pop();
					visited[p] = true;
					for (auto e : g[p]) {
						if (e.cap && !visited[e.to]) {
							visited[e.to] = true;
							que.push(e.to);
						}
					}
				}
				return visited;
			}

		  private:
			int _n;
			struct _edge {
				int to, rev;
				Cap cap;
			};
			std::vector<std::pair<int, int>> pos;
			std::vector<std::vector<_edge>> g;
		};

		}  // namespace atcoder
	};

	namespace SCC{
		
		namespace atcoder {
		namespace internal {

		template <class E> struct csr {
			std::vector<int> start;
			std::vector<E> elist;
			explicit csr(int n, const std::vector<std::pair<int, E>>& edges)
				: start(n + 1), elist(edges.size()) {
				for (auto e : edges) {
					start[e.first + 1]++;
				}
				for (int i = 1; i <= n; i++) {
					start[i] += start[i - 1];
				}
				auto counter = start;
				for (auto e : edges) {
					elist[counter[e.first]++] = e.second;
				}
			}
		};

		}  // namespace internal

		}  // namespace atcoder


		namespace atcoder {
		namespace internal {

		struct scc_graph {
		  public:
			explicit scc_graph(int n) : _n(n) {}

			int num_vertices() { return _n; }

			void add_edge(int from, int to) { edges.push_back({from, {to}}); }

			std::pair<int, std::vector<int>> scc_ids() {
				auto g = csr<edge>(_n, edges);
				int now_ord = 0, group_num = 0;
				std::vector<int> visited, low(_n), ord(_n, -1), ids(_n);
				visited.reserve(_n);
				auto dfs = [&](auto self, int v) -> void {
					low[v] = ord[v] = now_ord++;
					visited.push_back(v);
					for (int i = g.start[v]; i < g.start[v + 1]; i++) {
						auto to = g.elist[i].to;
						if (ord[to] == -1) {
							self(self, to);
							low[v] = std::min(low[v], low[to]);
						} else {
							low[v] = std::min(low[v], ord[to]);
						}
					}
					if (low[v] == ord[v]) {
						while (true) {
							int u = visited.back();
							visited.pop_back();
							ord[u] = _n;
							ids[u] = group_num;
							if (u == v) break;
						}
						group_num++;
					}
				};
				for (int i = 0; i < _n; i++) {
					if (ord[i] == -1) dfs(dfs, i);
				}
				for (auto& x : ids) {
					x = group_num - 1 - x;
				}
				return {group_num, ids};
			}

			std::vector<std::vector<int>> scc() {
				auto ids = scc_ids();
				int group_num = ids.first;
				std::vector<int> counts(group_num);
				for (auto x : ids.second) counts[x]++;
				std::vector<std::vector<int>> groups(ids.first);
				for (int i = 0; i < group_num; i++) {
					groups[i].reserve(counts[i]);
				}
				for (int i = 0; i < _n; i++) {
					groups[ids.second[i]].push_back(i);
				}
				return groups;
			}

		  private:
			int _n;
			struct edge {
				int to;
			};
			std::vector<std::pair<int, edge>> edges;
		};

		}  // namespace internal

		}  // namespace atcoder


		namespace atcoder {

		struct scc_graph {
		  public:
			scc_graph() : internal(0) {}
			explicit scc_graph(int n) : internal(n) {}

			void add_edge(int from, int to) {
				int n = internal.num_vertices();
				assert(0 <= from && from < n);
				assert(0 <= to && to < n);
				internal.add_edge(from, to);
			}

			std::vector<std::vector<int>> scc() { return internal.scc(); }

		  private:
			internal::scc_graph internal;
		};

		}  // namespace atcoder


	};

	namespace TwoSAT{
		using namespace SCC::atcoder;
		
		namespace atcoder {

			struct two_sat {
			  public:
				two_sat() : _n(0), scc(0) {}
				explicit two_sat(int n) : _n(n), _answer(n), scc(2 * n) {}

				void add_clause(int i, bool f, int j, bool g) {
					assert(0 <= i && i < _n);
					assert(0 <= j && j < _n);
					scc.add_edge(2 * i + (f ? 0 : 1), 2 * j + (g ? 1 : 0));
					scc.add_edge(2 * j + (g ? 0 : 1), 2 * i + (f ? 1 : 0));
				}
				bool satisfiable() {
					auto id = scc.scc_ids().second;
					for (int i = 0; i < _n; i++) {
						if (id[2 * i] == id[2 * i + 1]) return false;
						_answer[i] = id[2 * i] < id[2 * i + 1];
					}
					return true;
				}
				std::vector<bool> answer() { return _answer; }

			  private:
				int _n;
				std::vector<bool> _answer;
				internal::scc_graph scc;
			};

			}  // namespace atcoder
	};
	
	namespace Math{
		namespace atcoder {

		namespace internal {

		constexpr long long safe_mod(long long x, long long m) {
			x %= m;
			if (x < 0) x += m;
			return x;
		}

		struct barrett {
			
			#warning ZABERY DEFINE __int128 long long
			#define __int128 long long

			unsigned int _m;
			unsigned long long im;

			explicit barrett(unsigned int m) : _m(m), im((unsigned long long)(-1) / m + 1) {}

			unsigned int umod() const { return _m; }

			unsigned int mul(unsigned int a, unsigned int b) const {

				unsigned long long z = a;
				z *= b;
		#ifdef _MSC_VER
				unsigned long long x;
				_umul128(z, im, &x);
		#else
				unsigned long long x =
					(unsigned long long)(((unsigned __int128)(z)*im) >> 64);
		#endif
				unsigned int v = (unsigned int)(z - x * _m);
				if (_m <= v) v += _m;
				return v;
			}
		};

		constexpr long long pow_mod_constexpr(long long x, long long n, int m) {
			if (m == 1) return 0;
			unsigned int _m = (unsigned int)(m);
			unsigned long long r = 1;
			unsigned long long y = safe_mod(x, m);
			while (n) {
				if (n & 1) r = (r * y) % _m;
				y = (y * y) % _m;
				n >>= 1;
			}
			return r;
		}

		constexpr bool is_prime_constexpr(int n) {
			if (n <= 1) return false;
			if (n == 2 || n == 7 || n == 61) return true;
			if (n % 2 == 0) return false;
			long long d = n - 1;
			while (d % 2 == 0) d /= 2;
			constexpr long long bases[3] = {2, 7, 61};
			for (long long a : bases) {
				long long t = d;
				long long y = pow_mod_constexpr(a, t, n);
				while (t != n - 1 && y != 1 && y != n - 1) {
					y = y * y % n;
					t <<= 1;
				}
				if (y != n - 1 && t % 2 == 0) {
					return false;
				}
			}
			return true;
		}
		template <int n> constexpr bool is_prime = is_prime_constexpr(n);

		constexpr std::pair<long long, long long> inv_gcd(long long a, long long b) {
			a = safe_mod(a, b);
			if (a == 0) return {b, 0};

			long long s = b, t = a;
			long long m0 = 0, m1 = 1;

			while (t) {
				long long u = s / t;
				s -= t * u;
				m0 -= m1 * u;  // |m1 * u| <= |m1| * s <= b


				auto tmp = s;
				s = t;
				t = tmp;
				tmp = m0;
				m0 = m1;
				m1 = tmp;
			}
			if (m0 < 0) m0 += b / s;
			return {s, m0};
		}

		constexpr int primitive_root_constexpr(int m) {
			if (m == 2) return 1;
			if (m == 167772161) return 3;
			if (m == 469762049) return 3;
			if (m == 754974721) return 11;
			if (m == 998244353) return 3;
			int divs[20] = {};
			divs[0] = 2;
			int cnt = 1;
			int x = (m - 1) / 2;
			while (x % 2 == 0) x /= 2;
			for (int i = 3; (long long)(i)*i <= x; i += 2) {
				if (x % i == 0) {
					divs[cnt++] = i;
					while (x % i == 0) {
						x /= i;
					}
				}
			}
			if (x > 1) {
				divs[cnt++] = x;
			}
			for (int g = 2;; g++) {
				bool ok = true;
				for (int i = 0; i < cnt; i++) {
					if (pow_mod_constexpr(g, (m - 1) / divs[i], m) == 1) {
						ok = false;
						break;
					}
				}
				if (ok) return g;
			}
		}
		template <int m> constexpr int primitive_root = primitive_root_constexpr(m);

		unsigned long long floor_sum_unsigned(unsigned long long n,
											  unsigned long long m,
											  unsigned long long a,
											  unsigned long long b) {
			unsigned long long ans = 0;
			while (true) {
				if (a >= m) {
					ans += n * (n - 1) / 2 * (a / m);
					a %= m;
				}
				if (b >= m) {
					ans += n * (b / m);
					b %= m;
				}

				unsigned long long y_max = a * n + b;
				if (y_max < m) break;
				n = (unsigned long long)(y_max / m);
				b = (unsigned long long)(y_max % m);
				std::swap(m, a);
			}
			return ans;
		}

		}  // namespace internal

		}  // namespace atcoder

		namespace atcoder {

		long long pow_mod(long long x, long long n, int m) {
			assert(0 <= n && 1 <= m);
			if (m == 1) return 0;
			internal::barrett bt((unsigned int)(m));
			unsigned int r = 1, y = (unsigned int)(internal::safe_mod(x, m));
			while (n) {
				if (n & 1) r = bt.mul(r, y);
				y = bt.mul(y, y);
				n >>= 1;
			}
			return r;
		}

		long long inv_mod(long long x, long long m) {
			assert(1 <= m);
			auto z = internal::inv_gcd(x, m);
			assert(z.first == 1);
			return z.second;
		}

		std::pair<long long, long long> crt(const std::vector<long long>& r,
											const std::vector<long long>& m) {
			assert(r.size() == m.size());
			int n = int(r.size());
			long long r0 = 0, m0 = 1;
			for (int i = 0; i < n; i++) {
				assert(1 <= m[i]);
				long long r1 = internal::safe_mod(r[i], m[i]), m1 = m[i];
				if (m0 < m1) {
					std::swap(r0, r1);
					std::swap(m0, m1);
				}
				if (m0 % m1 == 0) {
					if (r0 % m1 != r1) return {0, 0};
					continue;
				}


				long long g, im;
				std::tie(g, im) = internal::inv_gcd(m0, m1);

				long long u1 = (m1 / g);
				if ((r1 - r0) % g) return {0, 0};

				long long x = (r1 - r0) / g % u1 * im % u1;

				r0 += x * m0;
				m0 *= u1;  // -> lcm(m0, m1)
				if (r0 < 0) r0 += m0;
			}
			return {r0, m0};
		}

		long long floor_sum(long long n, long long m, long long a, long long b) {
			assert(0 <= n && n < (1LL << 32));
			assert(1 <= m && m < (1LL << 32));
			unsigned long long ans = 0;
			if (a < 0) {
				unsigned long long a2 = internal::safe_mod(a, m);
				ans -= 1ULL * n * (n - 1) / 2 * ((a2 - a) / m);
				a = a2;
			}
			if (b < 0) {
				unsigned long long b2 = internal::safe_mod(b, m);
				ans -= 1ULL * n * ((b2 - b) / m);
				b = b2;
			}
			return ans + internal::floor_sum_unsigned(n, m, a, b);
		}

		}  // namespace atcoder
	};
};

int main()
{
	ios_base::sync_with_stdio(0), cin.tie(0), cout.tie(0);
	
	
	cerr << "Time elapsed: " << clock() / (double)CLOCKS_PER_SEC << endl;
	return 0;
}
