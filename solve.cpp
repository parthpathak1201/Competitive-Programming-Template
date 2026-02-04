#include <bits/stdc++.h>

using namespace std;

using ll = long long;
using db = long double;
using str = string;

using pi = pair<int, int>;
using pl = pair<ll, ll>;
using pd = pair<db, db>;
#define mp make_pair
#define ff first
#define ss second

#define tcT template <class T
#define tcTU tcT, class U
tcT > using V = vector<T>;
tcT, size_t SZ > using AR = array<T, SZ>;
using vi = V<int>;
using vb = V<bool>;
using vl = V<ll>;
using vd = V<db>;
using vs = V<str>;
using vpi = V<pi>;
using vpl = V<pl>;
using vpd = V<pd>;

#define sz(x) int(size(x))
#define bg(x) begin(x)
#define all(x) bg(x), end(x)
#define rall(x) rbegin(x), rend(x)
#define sor(x) sort(all(x))
#define rsz resize
#define ins insert
#define pb push_back
#define eb emplace_back
#define ft front()
#define bk back()
#define YN(b) ps((b) ? "YES" : "NO")

#define lb lower_bound
#define ub upper_bound
tcT > int lwb(const V<T> &a, const T &b) { return int(lb(all(a), b) - bg(a)); }
tcT > int upb(const V<T> &a, const T &b) { return int(ub(all(a), b) - bg(a)); }

#define FOR(i, a, b) for (int i = (a); i < (b); ++i)
#define F0R(i, a) FOR(i, 0, a)
#define ROF(i, a, b) for (int i = (b) - 1; i >= (a); --i)
#define R0F(i, a) ROF(i, 0, a)
#define rep(a) F0R(_, a)
#define each(a, x) for (auto &a : x)

const int MOD = 998244353;
const int MX = (int)2e5 + 5;
const ll BIG = 1e18;
const db PI = acos((db)-1);
const int dx[4]{1, 0, -1, 0}, dy[4]{0, 1, 0, -1};
mt19937 rng((uint32_t)chrono::steady_clock::now().time_since_epoch().count());
template <class T>
using pqg = priority_queue<T, vector<T>, greater<T>>;

constexpr int pct(int x) { return __builtin_popcount(x); }
constexpr int bits(int x) { return x == 0 ? 0 : 31 - __builtin_clz(x); }
constexpr int p2(int x) { return 1 << x; }
constexpr int msk2(int x) { return p2(x) - 1; }

ll cdiv(ll a, ll b) { return a / b + ((a ^ b) > 0 && a % b); }
ll fdiv(ll a, ll b) { return a / b - ((a ^ b) < 0 && a % b); }

tcT > bool ckmin(T &a, const T &b) { return b < a ? a = b, 1 : 0; }
tcT > bool ckmax(T &a, const T &b) { return a < b ? a = b, 1 : 0; }

tcTU > T fstTrue(T lo, T hi, U f)
{
	++hi;
	assert(lo <= hi);
	while (lo < hi)
	{
		T mid = lo + (hi - lo) / 2;
		f(mid) ? hi = mid : lo = mid + 1;
	}
	return lo;
}
tcTU > T lstTrue(T lo, T hi, U f)
{
	--lo;
	assert(lo <= hi);
	while (lo < hi)
	{
		T mid = lo + (hi - lo + 1) / 2;
		f(mid) ? lo = mid : hi = mid - 1;
	}
	return lo;
}
tcT > void remDup(vector<T> &v)
{
	sort(all(v));
	v.erase(unique(all(v)), end(v));
}
tcTU > void safeErase(T &t, const U &u)
{
	auto it = t.find(u);
	assert(it != end(t));
	t.erase(it);
}

inline namespace IO
{
#define SFINAE(x, ...)                                     \
	template <class, class = void>                         \
	struct x : std::false_type                             \
	{                                                      \
	};                                                     \
	template <class T>                                     \
	struct x<T, std::void_t<__VA_ARGS__>> : std::true_type \
	{                                                      \
	}

	SFINAE(DefaultI, decltype(std::cin >> std::declval<T &>()));
	SFINAE(DefaultO, decltype(std::cout << std::declval<T &>()));
	SFINAE(IsTuple, typename std::tuple_size<T>::type);
	SFINAE(Iterable, decltype(std::begin(std::declval<T>())));

	template <auto &is>
	struct Reader
	{
		template <class T>
		void Impl(T &t)
		{
			if constexpr (DefaultI<T>::value)
				is >> t;
			else if constexpr (Iterable<T>::value)
			{
				for (auto &x : t)
					Impl(x);
			}
			else if constexpr (IsTuple<T>::value)
			{
				std::apply([this](auto &...args)
						   { (Impl(args), ...); }, t);
			}
		}
		template <class... Ts>
		void read(Ts &...ts) { ((Impl(ts)), ...); }
	};

	template <class... Ts>
	void re(Ts &...ts) { Reader<cin>{}.read(ts...); }
#define def(t, args...) \
	t args;             \
	re(args);

	template <auto &os, bool debug, bool print_nd>
	struct Writer
	{
		string comma() const { return debug ? "," : ""; }
		template <class T>
		constexpr char Space(const T &) const
		{
			return print_nd && (Iterable<T>::value or IsTuple<T>::value) ? '\n' : ' ';
		}
		template <class T>
		void Impl(T const &t) const
		{
			if constexpr (DefaultO<T>::value)
				os << t;
			else if constexpr (Iterable<T>::value)
			{
				if (debug)
					os << '{';
				int i = 0;
				for (auto &&x : t)
					((i++) ? (os << comma() << Space(x), Impl(x)) : Impl(x));
				if (debug)
					os << '}';
			}
			else if constexpr (IsTuple<T>::value)
			{
				if (debug)
					os << '(';
				std::apply(
					[this](auto const &...args)
					{
						int i = 0;
						(((i++) ? (os << comma() << " ", Impl(args)) : Impl(args)),
						 ...);
					},
					t);
				if (debug)
					os << ')';
			}
		}
		template <class T>
		void ImplWrapper(T const &t) const
		{
			if (debug)
				os << "\033[0;31m";
			Impl(t);
			if (debug)
				os << "\033[0m";
		}
		template <class... Ts>
		void print(Ts const &...ts) const { ((Impl(ts)), ...); }
		template <class F, class... Ts>
		void print_with_sep(const std::string &sep, F const &f, Ts const &...ts) const
		{
			ImplWrapper(f), ((os << sep, ImplWrapper(ts)), ...), os << '\n';
		}
		void print_with_sep(const std::string &) const { os << '\n'; }
	};

	template <class... Ts>
	void pr(Ts const &...ts) { Writer<cout, false, true>{}.print(ts...); }
	template <class... Ts>
	void ps(Ts const &...ts) { Writer<cout, false, true>{}.print_with_sep(" ", ts...); }
}

inline namespace Debug
{
	template <typename... Args>
	void err(Args... args) { Writer<cerr, true, false>{}.print_with_sep(" | ", args...); }
	template <typename... Args>
	void errn(Args... args) { Writer<cerr, true, true>{}.print_with_sep(" | ", args...); }

	void err_prefix(str func, int line, string args)
	{
		cerr << "\033[0;31m\u001b[1mDEBUG\033[0m" << " | " << "\u001b[34m" << func << "\033[0m" << ":" << "\u001b[34m" << line << "\033[0m" << " - " << "[" << args << "] = ";
	}

#ifdef LOCAL
#define dbg(args...) err_prefix(__FUNCTION__, __LINE__, #args), err(args)
#define dbgn(args...) err_prefix(__FUNCTION__, __LINE__, #args), errn(args)
#else
#define dbg(...)
#define dbgn(args...)
#endif

	const auto beg_time = std::chrono::high_resolution_clock::now();
	double time_elapsed()
	{
		return chrono::duration<double>(std::chrono::high_resolution_clock::now() - beg_time).count();
	}
}

inline namespace FileIO
{
	void setIn(str s) { freopen(s.c_str(), "r", stdin); }
	void setOut(str s) { freopen(s.c_str(), "w", stdout); }
	void setIO(str s = "")
	{
		cin.tie(0)->sync_with_stdio(0);
		cout << fixed << setprecision(12);
		if (sz(s))
			setIn(s + ".in"), setOut(s + ".out");
	}
}

vb sieve(int n)
{
	vb is_prime(n + 1, true);
	is_prime[0] = is_prime[1] = false;
	for (int i = 2; i * i <= n; i++)
	{
		if (is_prime[i])
		{
			for (int j = i * i; j <= n; j += i)
				is_prime[j] = false;
		}
	}
	return is_prime;
}

vi linear_sieve(int n)
{
	vi primes;
	vi min_prime(n + 1, 0);
	FOR(i, 2, n + 1)
	{
		if (min_prime[i] == 0)
		{
			min_prime[i] = i;
			primes.pb(i);
		}
		for (int p : primes)
		{
			if (p > min_prime[i] || i * p > n)
				break;
			min_prime[i * p] = p;
		}
	}
	return primes;
}

bool isPrime(uint64_t n)
{
	if (n < 2)
		return false;
	if (n % 2 == 0 || n % 3 == 0)
		return n == 2 || n == 3;

	uint64_t d = n - 1;
	int s = 0;
	while (d % 2 == 0)
	{
		d /= 2;
		s++;
	}

	static const uint64_t bases[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};

	for (uint64_t a : bases)
	{
		if (n <= a)
			break;

		__uint128_t x = 1;
		__uint128_t base = a % n;
		uint64_t exp = d;
		while (exp > 0)
		{
			if (exp % 2 == 1)
				x = (x * base) % n;
			base = (base * base) % n;
			exp /= 2;
		}

		if (x == 1 || x == n - 1)
			continue;

		bool composite = true;
		for (int r = 1; r < s; r++)
		{
			x = (x * x) % n;
			if (x == n - 1)
			{
				composite = false;
				break;
			}
		}
		if (composite)
			return false;
	}
	return true;
}

tcT > T gcd(T a, T b) { return b == 0 ? a : gcd(b, a % b); }
tcT > T lcm(T a, T b) { return (a / gcd(a, b)) * b; }

ll binpow(ll a, ll b, ll m)
{
	a %= m;
	ll res = 1;
	while (b > 0)
	{
		if (b & 1)
			res = res * a % m;
		a = a * a % m;
		b >>= 1;
	}
	return res;
}

ll inv(ll a, ll m) { return binpow(a, m - 2, m); }

bool isRBS(const string &str)
{
	int balance = 0;
	for (char a : str)
	{
		if (a == '(')
		{
			balance++;
		}
		else
		{
			balance--;
		}
		if (balance < 0)
			return false;
	}
	return balance == 0;
}

bool is_palin(const vi &v, int x)
{
	int l = 0, r = sz(v) - 1;
	while (l < r)
	{
		if (v[l] == x)
		{
			l++;
			continue;
		}
		if (v[r] == x)
		{
			r--;
			continue;
		}
		if (v[l] != v[r])
			return false;
		l++;
		r--;
	}
	return true;
}

ll manhattan(ll x1, ll y1, ll x2, ll y2)
{
	return llabs(x1 - x2) + llabs(y1 - y2);
}

void rec(int n, int s, int& val) {
	
	return;
}


void solve() {
    
}

int main()
{
	setIO();
	int TC = 1;
	re(TC);
	while (TC--)
		solve();
}
