#include <iostream>
#include <fstream>
#include <algorithm>
#include <cmath>
#include <vector>
#include <map>
#include <unordered_map>
#include <set>
#include <cstring>
#include <chrono>
#include <cassert>
#include <bitset>
#include <stack>
#include <queue>
#include <iomanip>
#include <random>

#ifdef _MSC_VER
#  include <intrin.h>
#  define __builtin_popcount __popcnt
#  define __builtin_popcountll __popcnt64
#endif

//#pragma GCC optimize("Ofast")
#pragma GCC optimize("Ofast,unroll-loops")
//#pragma GCC target("sse,sse2,sse3,ssse3,sse4,popcnt,abm,mmx,avx,tune=native")
#define x first
#define y second
#define ld long double
#define ll long long
#define ull unsigned long long
#define us unsigned short
#define lsb(x) ((x) & (-(x)))
#define pii pair <int, int>
#define pll pair <ll, ll>

using namespace std;

mt19937 gen(time(0));
uniform_int_distribution <uint32_t> rng;

const int MOD = 998244353;

// the following namespace includes many useful things
// for solving linear recurrences

namespace recurrences {
    // binary exponentiation
    template <int MOD>
    int lgput(int n, int p) {
        int ans = 1, x = n;

        while (p) {
            if (p & 1)
                ans = 1LL * ans * x % MOD;
            x = 1LL * x * x % MOD;
            p >>= 1;
        }

        return ans;
    }

    // modular integer class
    template <int MOD>
    struct Int {
        int x;

        Int() {
            x = 0;
        }

        Int(int _x) {
            if (_x < 0)
                _x += MOD;
            if (_x >= MOD)
                _x -= MOD;
            x = _x;
        }

        friend ostream& operator << (ostream& os, const Int& X) {
            os << (false ? X.x - MOD : X.x);
            return os;
        }

        Int operator + (const Int& other) const {
            int val = x + other.x;

            return (val >= MOD ? val - MOD : val);
        }

        Int operator += (const Int& other) {
            return *this = *this + other;
        }

        Int operator - (const Int& other) const {
            int val = x - other.x;

            return (val < 0 ? val + MOD : val);
        }
        Int operator -= (const Int& other) {
            return *this = *this - other;
        }

        Int operator * (const Int& other) const {
            return 1LL * x * other.x % MOD;
        }

        Int operator *= (const Int& other) {
            return *this = *this * other;
        }

        Int operator / (const Int& other) const {
            return 1LL * x * other.inv() % MOD;
        }

        bool operator == (const Int& other) const {
            return x == other.x;
        }

        bool operator != (const Int& other) const {
            return x != other.x;
        }

        int pow(int p) const {
            return lgput<MOD>(x, p);
        }

        int inv() const {
            return lgput<MOD>(x, MOD - 2);
        }
    };

    const bool slow_mult = false;
    bool calcPrimitve = true;
    int root;

    int primitive_root(int p) {
        if (!calcPrimitve) {
            return root;
        }

        vector<int> fact;
        int phi = p - 1, n = phi;
        for (int i = 2; i * i <= n; ++i)
            if (n % i == 0) {
                fact.push_back(i);
                while (n % i == 0)
                    n /= i;
            }
        if (n > 1)
            fact.push_back(n);

        for (int res = 2; res <= p; ++res) {
            bool ok = true;
            for (size_t i = 0; i < fact.size() && ok; ++i)
                ok &= lgput<MOD>(res, phi / fact[i]) != 1;
            if (ok) {
                root = res;
                return res;
            }
        }
        return -1;
    }

    int get_smallest_power(int n) {
        int p = 1;
        while (p < n)
            p <<= 1;
        return p;
    }

    bool calcW = true;

    Int<MOD> valw[30], invvalw[30];

    // modular 
    template <typename T>
    struct Poly {
        vector <T> p;

        Poly() {
            p.clear();
        }

        Poly(vector <T> values) {
            p = values;
        }

        Poly(int val) {
            p = { val };
        }

        T& operator [] (int index) {
            assert(index < (int)p.size());
            return p[index];
        }

        void setDegree(int deg) {
            p.resize(deg + 1);
        }

        int deg() const {
            return p.size() - 1;
        }

        friend ostream& operator << (ostream& os, const Poly& P) {
            for (auto& i : P.p)
                os << i << " ";
            return os;
        }

        bool operator == (const Poly& other) const {
            if (deg() != other.deg())
                return 0;

            for (int i = 0; i <= deg(); i++) {
                if (p[i] != other.p[i])
                    return 0;
            }

            return 1;
        }

        Poly operator + (const Poly& other) const {
            Poly sum(p);

            sum.setDegree(max(deg(), other.deg()));

            for (int i = 0; i <= other.deg(); i++)
                sum[i] += other.p[i];

            return sum;
        }

        // add
        Poly operator += (const Poly& other) {
            return *this = *this + other;
        }

        Poly operator - (const Poly& other) const {
            Poly dif(p);

            dif.setDegree(max(deg(), other.deg()));

            for (int i = 0; i <= other.deg(); i++)
                dif[i] -= other.p[i];

            return dif;
        }

        // substract
        Poly operator -= (const Poly& other) {
            return *this = *this - other;
        }

        // scalar multiplication
        Poly operator * (const T& other) const {
            Poly mult(*this);

            for (auto& i : mult.p)
                i *= other;

            return mult;
        }
        // scalar multiplication
        Poly operator *= (const T& other) {
            return *this = *this * other;
        }

        // scalar division
        Poly operator / (const T& other) const {
            Poly mult(*this);
            Int<MOD> val = other.inv();

            for (auto& i : mult.p)
                i *= val;

            return mult;
        }

        // scalar division
        Poly operator /= (const T& other) {
            return *this = *this / other;
        }

        Poly fft(bool invert) {
            Poly Ans(p);

            Int<MOD> root(primitive_root(MOD));

            if (calcW) {
                calcW = false;

                for (int i = 0; i < 30; i++) {
                    valw[i] = root.pow((MOD - 1) >> (i + 1));
                    invvalw[i] = valw[i].inv();
                }
            }

            int ind = 0, n = deg();
            for (int i = 1; i < n; i++) {
                int b;
                for (b = n / 2; ind & b; b >>= 1)
                    ind ^= b;
                ind ^= b;

                if (i < ind)
                    swap(Ans[i], Ans[ind]);
            }

            for (int l = 2, p = 0; l <= n; l <<= 1, p++) {
                Int<MOD> bw(!invert ? valw[p] : invvalw[p]);

                for (int i = 0; i < n; i += l) {
                    Int<MOD> w(1);

                    for (int j = 0; j < l / 2; j++) {
                        int i1 = i + j, i2 = i + j + l / 2;
                        Int<MOD> val1(Ans[i1]), val2(Ans[i2] * w);
                        Ans[i1] = val1 + val2;
                        Ans[i2] = val1 - val2;
                        w *= bw;
                    }
                }
            }

            if (invert) {
                Int<MOD> inv = Int<MOD>(n).inv();

                for (int i = 0; i < n; i++)
                    Ans[i] *= inv;
            }

            return Ans;
        }

        // multiplies 2 polynomials
        Poly operator * (const Poly& other) const {
            if (!root) { // for small sizes, use naive multiplication
                Poly mult;
                mult.setDegree(deg() + other.deg());

                for (int i = 0; i <= deg(); i++) {
                    for (int j = 0; j <= other.deg(); j++)
                        mult[i + j] += p[i] * other.p[j];
                }

                return mult;
            }
            Poly A(p), B(other.p);

            int sz = max(get_smallest_power(A.deg() + 1), get_smallest_power(B.deg() + 1)) * 2;

            A.setDegree(sz), B.setDegree(sz);

            A = A.fft(0);
            B = B.fft(0);

            for (int i = 0; i < sz; i++)
                A[i] *= B[i];

            A = A.fft(1);

            A.setDegree(deg() + other.deg());

            return A;
        }

        // p mod q
        Poly operator % (const Poly& other) const {
            int d = deg() - other.deg();

            if (d < 0)
                return *this;

            if (false) {
                Poly R2(p);
                for (int i = deg(); i >= other.deg(); i--) {
                    R2 -= (other * R2[i] / other.p[other.deg()]).shift(i - other.deg());
                }

                R2.setDegree(other.deg() - 1);

                //return R;
            }

            Poly A, B = other;

            for (int i = 0; i <= d; i++) {
                A.p.push_back(p[deg() - i]);
            }

            for (int i = 0; i <= B.deg() / 2; i++)
                swap(B[i], B[B.deg() - i]);

            Poly C = A * B.inverse(d);

            C.setDegree(d);

            for (int i = 0; i <= d / 2; i++)
                swap(C[i], C[d - i]);

            Poly R = *this - other * C;

            R.setDegree(other.deg() - 1);

            return R;
        }

        // *x^n
        Poly shift(int index) {
            Poly q = p;
            q.setDegree(deg() + index);
            for (int i = deg(); i >= 0; i--)
                q[i + index] = q[i];
            for (int i = index - 1; i >= 0; i--)
                q[i] = T(0);
            return q;
        }

        // derivate of P
        Poly derivative() {
            Poly D;

            D.setDegree(deg() - 1);

            for (int i = 1; i <= deg(); i++)
                D[i - 1] = T(i) * p[i];

            return D;
        }

        // integral of P
        Poly integral() {
            Poly I;

            I.setDegree(deg() + 1);

            for (int i = 0; i <= deg(); i++)
                I[i + 1] = p[i] / T(i + 1);

            return I;
        }

        // P^-1 mod x^n
        Poly inverse(int n) {
            Poly Inv(p[0].inv()), two(2);

            int power = 1;

            while ((power / 2) <= n) {
                Poly A;
                for (int i = 0; i <= power; i++)
                    A.p.push_back((i <= deg() ? p[i] : 0));

                Inv = Inv * (two - A * Inv);
                Inv.setDegree(power);

                power <<= 1;
            }

            Inv.setDegree(n);

            return Inv;
        }

        // log(P) mod x^n
        Poly log(int n) {
            Poly Log(derivative());

            Log = Log * this->inverse(n);

            return Log.integral();
        }

        // e^P mod x^n
        Poly exp(int n) {
            Poly Exp(1);

            int power = 1;

            while ((power / 2) <= n) {
                Poly A(p);
                A.setDegree(power);
                Exp += Exp * A - Exp * Exp.log(power);
                Exp.setDegree(power);
                power <<= 1;
            }

            Exp.setDegree(n);
            return Exp;
        }

        // p^power mod mod, where mod is a polynomial
        Poly pow(uint64_t power, Poly mod) {
            Poly Pow(1), X(p);

            while (power) {
                if (power & 1)
                    Pow = Pow * X % mod;
                X = X * X % mod;
                power >>= 1;
            }

            return Pow;
        }
    };

    // berlekamp-massey algorithm
    template <int MOD>
    Poly<Int<MOD>> berlekamp_massey(vector <Int<MOD>> values) {
        Poly<Int<MOD>> P(values), B, C, Pol(-1);
        int n = values.size(), lst = -1;
        Int<MOD> lstError;

        for (int i = 0; i < n; i++) {
            Int<MOD> error = P[i];

            for (int j = 1; j <= C.deg() + 1; j++)
                error -= C[j - 1] * P[i - j];

            if (error == Int<MOD>(0))
                continue;

            if (lst == -1) {
                C = C.shift(i + 1);
                lst = i;
                lstError = P[i];
                continue;
            }

            Poly<Int<MOD>> D = (Pol * error / lstError);
            Poly<Int<MOD>> t = C;

            // instead of shifting D with i - lst - 1 positions
            // do the substraction on the last D.deg() coeficients
            if (i - lst - 1 + D.deg() > C.deg())
                C.setDegree(i - lst - 1 + D.deg());

            for (int j = 0; j <= D.deg(); j++)
                C[j + i - lst - 1] -= D[j];

            if (i - t.deg() > lst - B.deg()) {
                B = t;
                Pol = B;
                Pol = Pol.shift(1);
                Pol[0] = Int<MOD>(-1);
                lst = i;
                lstError = error;
            }

            //C -= D;
        }

        return C;
    }

    // find kth term based on terms of recurrence
    // assuming first term has index 1
    template <int MOD>
    Int<MOD> kth_term(vector <Int<MOD>> v, uint64_t k) {
        vector <Int<MOD>> x = { Int<MOD>(0), Int<MOD>(1) };
        Poly<Int<MOD>> CP = berlekamp_massey<MOD>(v);
        Poly<Int<MOD>> X(x);

        /*CP.setDegree(100000);
        for (int i = 0; i <= 100000; i++)
            CP[i] = Int<MOD>(rng(gen));*/

            // characteristic polynomial is of form
            // x^n - sigma(i = 1..n, c[i] * x^(n-i))
            // that's why we need to reverse the recurrence
            // from berlekamp-massey

        CP *= Int<MOD>(-1);
        CP = CP.shift(1);
        for (int i = 0; i <= CP.deg() / 2; i++)
            swap(CP[i], CP[CP.deg() - i]);
        CP[CP.deg()] = 1;

        X = X.pow(k - 1, CP);

        Int<MOD> term(0);

        for (int i = 0; i <= X.deg(); i++)
            term += X[i] * v[i];

        return term;
    }

    template <int MOD>
    void berlekamp_massey_test() {
        int n;
        vector<Int<MOD>> v;

        cin >> n;
        for (int i = 0; i < n; i++) {
            int x;
            cin >> x;
            v.push_back(x);
        }

        Poly<Int<MOD>> rec = berlekamp_massey<MOD>(v);

        // sanity check

        for (int k = rec.deg() + 2; k <= 30; k++) {
            Int<MOD> val(0);

            for (int i = k - rec.deg() - 1; i < k; i++)
                val += v[i - 1] * rec[k - 1 - i];

            assert(val == kth_term(v, k));
            if (k > n)
                v.push_back(val);
        }

        uint64_t k;
        cin >> k;
        cout << kth_term<MOD>(v, k) << "\n";
    }

    template <int MOD>
    void berlekamp_massey_speed_test() {
        int n;
        vector<Int<MOD>> v;

        n = 1000;
        for (int i = 0; i < n; i++) {
            int x;
            //cin >> x;
            x = rng(gen);
            v.push_back(x);
        }

        ld t1 = clock();

        for (int k = 1; k <= 200; k++)
            kth_term<MOD>(v, k);

        ld t2 = clock();

        cout << (t2 - t1) / CLOCKS_PER_SEC << "s\n";
    }

    template <int MOD>
    void inverse_test() {
        int n;
        cin >> n;

        vector <Int<MOD>> v;
        for (int i = 1; i <= n; i++) {
            int x;
            cin >> x;

            v.push_back(Int<MOD>(x));
        }

        Poly<Int<MOD>> P(v), Inv, Exp, Log;
        int deg = 10;

        Inv = P.inverse(deg);

        cout << "Inverse: " << Inv << "\n";

        Exp = P.exp(deg);

        cout << "Exponential: " << Exp << "\n";

        Log = P.log(deg);

        cout << "Logarithm: " << Log << '\n';
    }
};

void solve() {
    //recurrences::berlekamp_massey_test<MOD>();
    //recurrences::berlekamp_massey_speed_test<MOD>();
    //recurrences::inverse_test<MOD>();
}

int main() {
    ios_base::sync_with_stdio(false); cin.tie(0); cout.tie(0);
    srand(time(0));

    int T = 1;

    //cin >> T;

    while (T--) {
        solve();
    }

    return 0;
}