#ifndef EXTENSIONRINGSMALL_HPP_
#define EXTENSIONRINGSMALL_HPP_

#include <NTL/lzz_pX.h>
#include "Math/gf2n.cpp"
#include "Tools/octetStream.h"
#include "Tools/random.h"
#include "Tools/performance.h"

using namespace NTL;
using namespace std;

/*
    Only works in Z_{2^k}[X] / f(X) with k < 60
*/

template <int L, int LM>
class ExtensionRingSmall {

public:

    zz_pX f, modulus;
    static zz_pContext pc2;
    static zz_pContext pcl;

    ExtensionRingSmall();
    ExtensionRingSmall(const ExtensionRingSmall<L, LM> &other) { *this = other; }
    ExtensionRingSmall(zz_pX _f);
    ExtensionRingSmall(zz_pX _f, zz_pX _modulus);
    ExtensionRingSmall(long a);

    template <class U>
    ExtensionRingSmall(gf2n_<U> a);

    template <int K>
    ExtensionRingSmall(Z2<K> a);

    static void init(int l = L) {
        zz_p::init(1ull << l);
        ExtensionRingSmall<L, LM>::pc2 = zz_pContext(2);
        ExtensionRingSmall<L, LM>::pcl = zz_pContext(1ull << L);
    }

    inline int getL();
    inline zz_pX get();
    inline zz_pX get_modulus();

    void random(int size = L);

    ExtensionRingSmall invert();

    ExtensionRingSmall<L, LM>& operator=(const ExtensionRingSmall<L, LM>& other);

    template <int K>
    ExtensionRingSmall<L, LM>& operator=(const Z2<K>& other);

    ExtensionRingSmall<L, LM>& operator=(const long& other);

    template <class U>
    ExtensionRingSmall<L, LM>& operator=(const gf2n_<U>& other);

    operator bool() const {
        return IsZero(f);
    }

    void pack(octetStream &os);
    void unpack(octetStream &os);

    static ExtensionRingSmall<L, LM> conv_from_int(unsigned int x);

    void assign_zero() { f = zz_pX::zero(); }
    void assign_one() { 
        // zz_p::init(1ull << L);
        // zz_pPush push;
        // pcl.restore();
        f = to_zz_pX(1); 
    }

    bool is_zero() { return NTL::IsZero(f); }

    void randomize(PRNG& g);

    inline void reduce();

};

template <>
zz_pContext ExtensionRingSmall<59, 47>::pc2 = zz_pContext(2);

template <>
zz_pContext ExtensionRingSmall<59, 47>::pcl = zz_pContext(1ull << 59);

void copy(zz_pX& rhs, const zz_pX lhs, zz_pContext ctx);
void store_zz_pX(zz_pX f, octetStream &os);

inline zz_pX reduce_zz_pX(zz_pX f);



template <int L, int LM>
ExtensionRingSmall<L, LM> inner_product(ExtensionRingSmall<L, LM>* a, ExtensionRingSmall<L, LM>* b, size_t size);

template <int L, int LM>
ExtensionRingSmall<L, LM> inner_product(ExtensionRingSmall<L, LM>** a, ExtensionRingSmall<L, LM>** b, size_t rows, size_t cols);

template <int L, int LM>
ExtensionRingSmall<L, LM> inner_product(ExtensionRingSmall<L, LM>** a, ExtensionRingSmall<L, LM>* b, size_t rows, size_t cols);

template <int L, int LM>
ExtensionRingSmall<L, LM> inner_product(ExtensionRingSmall<L, LM>* a, vector<ExtensionRingSmall<L, LM>> b, size_t size);


// assignment

template <int L, int LM>
ExtensionRingSmall<L, LM>& ExtensionRingSmall<L, LM>::operator=(const ExtensionRingSmall<L, LM>& other) {
    if (this != &other) {
        // zz_p::init(1ull << L);
        // zz_pPush push;
        // pcl.restore();
        f = other.f;
        modulus = other.modulus;
    }
    return *this;
}

template <int L, int LM>
template <int K>
ExtensionRingSmall<L, LM>& ExtensionRingSmall<L, LM>::operator=(const Z2<K>& other) {
    ExtensionRingSmall<L, LM>();
    // zz_p::init(1ull << L);
    // zz_pPush push;
    // pcl.restore();
    SetCoeff(f, 0, to_zz_p(other.debug()));
    return *this;
}

template <int L, int LM>
ExtensionRingSmall<L, LM>& ExtensionRingSmall<L, LM>::operator=(const long& other) {
    ExtensionRingSmall<L, LM>();
    // zz_p::init(1ull << L);
    // zz_pPush push;
    // pcl.restore();
    SetCoeff(f, 0, to_zz_p(other));
    return *this;
}

template <int L, int LM>
template <class U>
ExtensionRingSmall<L, LM>& ExtensionRingSmall<L, LM>::operator=(const gf2n_<U>& a) {
    ExtensionRingSmall<L, LM>();
    int size = a.size_in_bits();
    for (int i = 0; i < min(size, LM); i ++) {
        if (a.get_bit(i)) {
            SetCoeff(f, i);
        }
    }
}


// comparison
template <int L, int LM>
bool operator==(const ExtensionRingSmall<L, LM>& self, const ExtensionRingSmall<L, LM>& other);

// Addition
template <int L, int LM>
ExtensionRingSmall<L, LM> operator+(const ExtensionRingSmall<L, LM>& self, const ExtensionRingSmall<L, LM>& other);

template <int L, int LM>
ExtensionRingSmall<L, LM>& operator+=(ExtensionRingSmall<L, LM>& self, const ExtensionRingSmall<L, LM>& other);


template <int L, int LM>
ExtensionRingSmall<L, LM> operator-(const ExtensionRingSmall<L, LM>& self, const ExtensionRingSmall<L, LM>& other);

template <int L, int LM>
ExtensionRingSmall<L, LM>& operator-=(ExtensionRingSmall<L, LM>& self, const ExtensionRingSmall<L, LM>& other);


// Multiplication
template <int L, int LM>
ExtensionRingSmall<L, LM> operator*(const ExtensionRingSmall<L, LM>& self, const ExtensionRingSmall<L, LM>& other);

template <int L, int LM>
ExtensionRingSmall<L, LM>& operator*=(ExtensionRingSmall<L, LM>& self, const ExtensionRingSmall<L, LM>& other);

template <int L, int LM>
ExtensionRingSmall<L, LM> operator/(const ExtensionRingSmall<L, LM>& self, const ExtensionRingSmall<L, LM>& other);

template <int L, int LM>
ExtensionRingSmall<L, LM>& operator/=(ExtensionRingSmall<L, LM>& self, const ExtensionRingSmall<L, LM>& other);


/*
            Implementation
*/

template <int L, int LM>
ExtensionRingSmall<L, LM>::ExtensionRingSmall() {

    // zz_p::init(1ull << L);

    for (int i = 0; i < num_2_fields; i ++) {
        if (fields_2[i][0] == LM) {
            SetCoeff(modulus, fields_2[i][0]);
            SetCoeff(modulus, fields_2[i][1]);
            SetCoeff(modulus, fields_2[i][2]);
            SetCoeff(modulus, fields_2[i][3]);
            break;
        }
        if (i == num_2_fields - 1) {
            throw std::exception();
        }
    }

    SetCoeff(modulus, 0);

    // pc2 = zz_pContext(2);
    // pcl = zz_pContext(1ull << L);
}

template <int L, int LM>
ExtensionRingSmall<L, LM>::ExtensionRingSmall(zz_pX _f): ExtensionRingSmall() {
    f = reduce_zz_pX(_f);
}

template <int L, int LM>
ExtensionRingSmall<L, LM>::ExtensionRingSmall(zz_pX _f, zz_pX _modulus) {
    this->f = reduce_zz_pX(_f);
    this->modulus = _modulus;
    // pc2 = zz_pContext(2);
    // pcl = zz_pContext(1ull << L);
}

template <int L, int LM>
ExtensionRingSmall<L, LM>::ExtensionRingSmall(long a): ExtensionRingSmall() {
    // zz_p::init(1ull << L);
    // zz_pPush push;
    // pcl.restore();
    SetCoeff(f, 0, to_zz_p(a));
}

template <int L, int LM>
template <int K>
ExtensionRingSmall<L, LM>::ExtensionRingSmall(Z2<K> a): ExtensionRingSmall() {
    // zz_p::init(1ull << L);
    // zz_pPush push;
    // pcl.restore();
    SetCoeff(f, 0, to_zz_p(a.debug()));
}

template <int L, int LM>
template <class U>
ExtensionRingSmall<L, LM>::ExtensionRingSmall(gf2n_<U> a): ExtensionRingSmall() {
    int size = a.size_in_bits();
    for (int i = 0; i < min(size, LM); i ++) {
        if (a.get_bit(i)) {
            SetCoeff(f, i);
        }
    }
}


void copy(zz_pX& rhs, const zz_pX lhs, zz_pContext ctx) {
    zz_pContext bak;
    bak.save();
    ctx.restore();
    long mod = zz_p::modulus();
    int degree = deg(lhs);
    for (int i = 0; i <= degree; i++) {
        SetCoeff(rhs, i, to_zz_p(rep(lhs[i]) % mod));
    }
    bak.restore();
}

template <int L, int LM>
void ExtensionRingSmall<L, LM>::random(int size) {
    NTL::random(f, size);
}

template <int L, int LM>
inline int ExtensionRingSmall<L, LM>::getL() {
    return L;
}

template <int L, int LM>
inline zz_pX ExtensionRingSmall<L, LM>::get() {
    return f;
}

template <int L, int LM>
inline zz_pX ExtensionRingSmall<L, LM>::get_modulus() {
    return modulus;
}

template <int L, int LM>
bool operator==(const ExtensionRingSmall<L, LM>& self, const ExtensionRingSmall<L, LM>& other) {
    return self.f == other.f && self.modulus == other.modulus;
}

template <int L, int LM>
bool operator!=(const ExtensionRingSmall<L, LM>& self, const ExtensionRingSmall<L, LM>& other) {
    return !(self == other);
}

template <int L, int LM>
ExtensionRingSmall<L, LM> operator+(const ExtensionRingSmall<L, LM>& self, const ExtensionRingSmall<L, LM>& other) {
    assert(self.modulus == other.modulus);
    return ExtensionRingSmall<L, LM>(reduce_zz_pX(self.f + other.f), self.modulus);
}

template <int L, int LM>
ExtensionRingSmall<L, LM>& operator+=(ExtensionRingSmall<L, LM>& self, const ExtensionRingSmall<L, LM>& other) {
    assert(self.modulus == other.modulus);
    self = self + other;
    return self;
}

template <int L, int LM>
ExtensionRingSmall<L, LM> operator-(const ExtensionRingSmall<L, LM>& self, const ExtensionRingSmall<L, LM>& other) {
    assert(self.modulus == other.modulus);
    return ExtensionRingSmall<L, LM>(reduce_zz_pX(self.f - other.f), self.modulus);
}

template <int L, int LM>
ExtensionRingSmall<L, LM>& operator-=(ExtensionRingSmall<L, LM>& self, const ExtensionRingSmall<L, LM>& other) {
    assert(self.modulus == other.modulus);
    self = self - other;
    return self;
}

template <int L, int LM>
ExtensionRingSmall<L, LM> operator*(const ExtensionRingSmall<L, LM>& self, const ExtensionRingSmall<L, LM>& other) {
    assert(self.modulus == other.modulus);
    auto z = ExtensionRingSmall<L, LM>(reduce_zz_pX(self.f * other.f), self.modulus);
    return z;
}

template <int L, int LM>
ExtensionRingSmall<L, LM>& operator*=(ExtensionRingSmall<L, LM>& self, const ExtensionRingSmall<L, LM>& other) {
    assert(self.modulus == other.modulus);
    self = self * other;
    return self;
}

template <int L, int LM>
ExtensionRingSmall<L, LM> ExtensionRingSmall<L, LM>::invert() {

    zz_pContext bak;
    bak.save();

    ExtensionRingSmall<L, LM>::pc2.restore();

    zz_pX f2;
    zz_pX f_mod2;
    copy(f2, f, ExtensionRingSmall<L, LM>::pc2);
    copy(f_mod2, modulus, ExtensionRingSmall<L, LM>::pc2);

    zz_pX d, a, b;  
    XGCD(d, a, b, f_mod2, f2);

    ExtensionRingSmall<L, LM>::pcl.restore();

    zz_pX h = 1 - (a * modulus + b * f);

    zz_pX B = zz_pX::zero();

    for (int i = 0; i < L; i ++) {
        B += power(h, i);
    }

    B *= b;

    bak.restore();
    return ExtensionRingSmall<L, LM>(B, modulus);
}

template <int L, int LM>
ExtensionRingSmall<L, LM> operator/(const ExtensionRingSmall<L, LM>& self, const ExtensionRingSmall<L, LM>& other) {
    assert(self.modulus == other.modulus);
    return ExtensionRingSmall<L, LM>(reduce_zz_pX(self.f * other.inverse()), self.modulus);
}

template <int L, int LM>
ExtensionRingSmall<L, LM>& operator/=(ExtensionRingSmall<L, LM>& self, const ExtensionRingSmall<L, LM>& other) {
    assert(self.modulus == other.modulus);
    self = self / other;
    return self;
}

void store_zz_pX(zz_pX f, octetStream &os) {
    os.store((int) deg(f));
    for (int i = 0; i <= deg(f); i ++) {
        os.store((size_t) f[i]._zz_p__rep);
    }
}

zz_pX restore_zz_pX(octetStream &os) {
    int d;
    size_t coef;
    os.get(d);
    zz_pX ret = zz_pX::zero();
    for (int i = 0; i <= d; i ++) {
        os.get(coef);
        SetCoeff(ret, i, coef);
    }

    return ret;
}

template <int L, int LM>
void ExtensionRingSmall<L, LM>::pack(octetStream &os) {
    store_zz_pX(f, os);
}

template <int L, int LM>
void ExtensionRingSmall<L, LM>::unpack(octetStream &os) {
    f = restore_zz_pX(os);
    modulus = zz_pX::zero();
    for (int i = 0; i < num_2_fields; i ++) {
        if (fields_2[i][0] == LM) {
            SetCoeff(modulus, fields_2[i][0]);
            SetCoeff(modulus, fields_2[i][1]);
            SetCoeff(modulus, fields_2[i][2]);
            SetCoeff(modulus, fields_2[i][3]);
            break;
        }
    }
    SetCoeff(modulus, 0);
}

template <int L, int LM>
ExtensionRingSmall<L, LM> ExtensionRingSmall<L, LM>::conv_from_int(unsigned int x) {
    int idx = 0;
    ExtensionRingSmall<L, LM> ret;

    while (x && idx < LM) {
        if (x & 1) {
            SetCoeff(ret.f, idx);
        }
        x >>= 1;
        idx ++;
    }

    return ret;
}

template <int L, int LM>
void ExtensionRingSmall<L, LM>::randomize(PRNG& g) {
    uint64_t data = g.get_word();
    f = zz_pX::zero();
    for (int i = 0; i < LM; i ++) {
        if ((data >> i) & 1) {
            SetCoeff(f, i);
        }
    }
}

template <int L, int LM>
inline void ExtensionRingSmall<L, LM>::reduce() {
    int degree = deg(f);
    for (int i = degree; i >= LM; i --) {
        f[i - 42] -= f[i];
        f[i - LM] -= f[i];
        f[i] = 0;
    }
    f.normalize();
}


inline zz_pX reduce_zz_pX(zz_pX f) {
    int degree = deg(f);
    for (int i = degree; i >= 47; i --) {
        f[i - 42] -= f[i];
        f[i - 47] -= f[i];
        f[i] = 0;
    }
    f.normalize();
    return f;
}

template <int L, int LM>
ExtensionRingSmall<L, LM> inner_product(ExtensionRingSmall<L, LM>* a, ExtensionRingSmall<L, LM>* b, size_t size) {
    zz_pX ans = zz_pX::zero();

    for (size_t i = 0; i < size; i ++) {
        ans += a[i].f * b[i].f;
    }

    return ExtensionRingSmall<L, LM>(ans);

}

template <int L, int LM>
ExtensionRingSmall<L, LM> inner_product(ExtensionRingSmall<L, LM>** a, ExtensionRingSmall<L, LM>** b, size_t rows, size_t cols) {
    zz_pX ans = zz_pX::zero();
    for (size_t i = 0; i < rows; ++i) {
        for (size_t j = 0; j < cols; ++j) {
            ans += a[i][j].f * b[i][j].f;
        }
    }

    return ExtensionRingSmall<L, LM>(ans);
}

template <int L, int LM>
ExtensionRingSmall<L, LM> inner_product(ExtensionRingSmall<L, LM>** a, ExtensionRingSmall<L, LM>* b, size_t rows, size_t cols) {
    zz_pX ans = zz_pX::zero();
    for (size_t i = 0; i < rows; ++i) {
        for (size_t j = 0; j < cols; ++j) {
            ans += a[i][j].f * b[j].f;
        }
    }

    return ExtensionRingSmall<L, LM>(ans);
}

template <int L, int LM>
ExtensionRingSmall<L, LM> inner_product(ExtensionRingSmall<L, LM>* a, vector<ExtensionRingSmall<L, LM>> b, size_t size) {
    zz_pX ans = zz_pX::zero();

    for (size_t i = 0; i < size; i ++) {
        ans += a[i].f * b[i].f;
    }

    return ExtensionRingSmall<L, LM>(ans);
}

#endif