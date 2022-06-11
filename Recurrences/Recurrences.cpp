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

const int MOD = (int)1e9 + 7;

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

ll gcd(ll a, ll b) {
    if (!b)
        return a;
    return gcd(b, a % b);
}

// the following namespace includes many useful things
// for solving linear recurrences

namespace recurrences {

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

        friend ostream& operator << (ostream& os, const Int &X) {
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

        int inv() const {
            return lgput<MOD>(x, MOD - 2);
        }
    };

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

        T &operator [] (int index) {
            assert(index < p.size());
            return p[index];
        }

        void setDegree(int deg) {
            p.resize(deg + 1);
        }

        int deg() const {
            return p.size() - 1;
        }

        friend ostream& operator << (ostream &os, const Poly &P) {
            for (auto& i : P.p)
                os << i << " ";
            return os;
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
            return *this * other.inv();
        }

        // scalar division
        Poly operator /= (const T& other) {
            return *this = *this / other;
        }

        // multiplicates 2 polynomials
        Poly operator * (const Poly& other) const {
            Poly mult;

            mult.setDegree(deg() + other.deg());

            for (int i = 0; i <= deg(); i++) {
                for (int j = 0; j <= other.deg(); j++)
                    mult[i + j] += p[i] * other.p[j];
            }

            return mult;
        }

        // p mod q
        Poly operator % (const Poly& other) const {
            Poly R(p);

            for (int i = deg(); i >= other.deg(); i--) {
                R -= (other * R[i] / other.p[other.deg()]).shift(i - other.deg());
            }

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
            vector <Int<MOD>> v = { p[0].inv() };
            Poly Inv(v);

            int power = 1;

            while ((power / 2) <= n) {
                Poly A(p);

                A.setDegree(power);
                Inv = Inv * Int<MOD>(2) - A * Inv * Inv;
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
            vector <Int<MOD>> v = { Int<MOD>(1) };
            Poly Exp(v);

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
            vector <Int<MOD>> v = { Int<MOD>(1) };
            Poly Pow(v), X(p);

            while (power) {
                if (power & 1)
                    Pow = Pow * X % mod;
                X = X * X % mod;
                power >>= 1;
            }

            return Pow;
        }
    };

    template <int MOD>
    Poly<Int<MOD>> berlekamp_massey(vector <Int<MOD>> values) {
        vector <Int<MOD>> v = { Int<MOD>(1) };
        Poly<Int<MOD>> P(values), B, C;
        int n = values.size();
        int length = 0, lst = -1;
        Int<MOD> zero(0);

        for (int i = 0; i < n; i++) {
            Int<MOD> error = P[i];

            for (int j = 1; j <= C.deg() + 1; j++)
                error -= C[j - 1] * P[i - j];

            if (error == zero)
                continue;

            if (lst == -1) {
                C = C.shift(i + 1);
                lst = i;
                continue;
            }

            Int<MOD> newError = P[lst];
            Poly<Int<MOD>> Temp = B;

            for (int j = 1; j <= Temp.deg() + 1; j++)
                newError -= Temp[j - 1] * P[lst - j];

            Temp = Temp.shift(1);
            Temp[0] = Int<MOD>(-1);

            Poly<Int<MOD>> D = (Temp * error / newError).shift(i - lst - 1);

            if (i - C.deg() > lst - B.deg()) {
                B = C;
                lst = i;
            }

            C -= D;
        }

        return C;
    }
    
    // find kth term based on terms of recurrence
    // assuming first term has index 1
    Int<MOD> kth_term(vector <Int<MOD>> v, uint64_t k) { 
        vector <Int<MOD>> x = { Int<MOD>(0), Int<MOD>(1) };
        Poly<Int<MOD>> CP = berlekamp_massey<MOD>(v);
        Poly<Int<MOD>> X(x);

        // characteristic polynomial is of form
        // x^n - sigma(i = 1..n, c[i] * x^(n-i))
        // that's why we need to reverse the recurrence
        // from berlekamp-massey

        CP *= Int<MOD>(-1);
        for (int i = 0; i <= CP.deg() / 2; i++)
            swap(CP[i], CP[CP.deg() - i]);
        CP.setDegree(CP.deg() + 1);
        CP[CP.deg()] = 1;

        X = X.pow(k - 1, CP);

        Int<MOD> term(0);

        for (int i = 0; i <= X.deg(); i++)
            term += X[i] * v[i];

        return term;
    }

    void berlekamp_massey_test() {
        int n;
        vector<Int<MOD>> v;

        cin >> n;
        for (int i = 0; i < n; i++) {
            int x;
            cin >> x;
            v.push_back(x);
        }

        Poly<Int<MOD>> p = berlekamp_massey<MOD>(v);

        cout << "x(n) = ";

        for (int i = 0; i <= p.deg(); i++)
            cout << "x(n-" << i + 1 << ") * " << p[i] << (i == p.deg() ? "" : " + ");
        cout << "\n";

        for (int i = p.deg() + 1; i < v.size(); i++) {
            Int<MOD> ans(0);

            for (int j = i - p.deg() - 1; j < i; j++) {
                ans += p[i - j - 1] * v[j];
            }

            assert(ans == v[i]);
        }

        uint64_t k;
        cin >> k;

        cout << kth_term(v, k) << "\n";
    }

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
    recurrences::berlekamp_massey_test();
    //recurrences::inverse_test();
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