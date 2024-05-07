#ifndef EXTENSIONRING_HPP_
#define EXTENSIONRING_HPP_

#include <NTL/ZZ_pX.h>
#include "Math/gf2n.cpp"
#include "Tools/octetStream.h"
#include "Tools/random.h"

using namespace NTL;
using namespace std;

template <int L>
class ExtensionRing {

public:

    ZZ_pX f, modulus;
    ZZ_pContext pc2;
    ZZ_pContext pcl;

    ExtensionRing();
    ExtensionRing(const ExtensionRing<L> &other) { *this = other; }
    ExtensionRing(ZZ_pX _f);
    ExtensionRing(ZZ_pX _f, ZZ_pX _modulus);
    ExtensionRing(long a);

    template <class U>
    ExtensionRing(gf2n_<U> a);

    template <int K>
    ExtensionRing(Z2<K> a);

    static void init(int l = L) {
        ZZ_p::init(power2_ZZ(l));
    }

    inline int getL();
    inline ZZ_pX get();
    inline ZZ_pX get_modulus();

    void random(int size = L);

    ExtensionRing invert();

    ExtensionRing<L>& operator=(const ExtensionRing<L>& other);

    template <int K>
    ExtensionRing<L>& operator=(const Z2<K>& other);

    ExtensionRing<L>& operator=(const long& other);

    template <class U>
    ExtensionRing<L>& operator=(const gf2n_<U>& other);

    void pack(octetStream &os);
    void unpack(octetStream &os);

    static ExtensionRing<L> conv_from_int(unsigned int x);

    void assign_zero() { f = ZZ_pX::zero(); }
    void assign_one() { f = to_ZZ_pX(1); }

    bool is_zero() { return NTL::IsZero(f); }

    void randomize(PRNG& g);

};

void copy(ZZ_pX& rhs, const ZZ_pX lhs, ZZ_pContext ctx);
void store_ZZ_pX(ZZ_pX f, octetStream &os);

template <int L>
ExtensionRing<L> inner_product(ExtensionRing<L>* a, ExtensionRing<L>* b, size_t size);

template <int L>
ExtensionRing<L> inner_product(ExtensionRing<L>** a, ExtensionRing<L>** b, size_t rows, size_t cols);

template <int L>
ExtensionRing<L> inner_product(ExtensionRing<L>* a, vector<ExtensionRing<L>> b, size_t size);


// assignment

template <int L>
ExtensionRing<L>& ExtensionRing<L>::operator=(const ExtensionRing<L>& other) {
    if (this != &other) {
        ZZ_p::init(power2_ZZ(L));
        f = other.f;
        modulus = other.modulus;
        pc2 = ZZ_pContext(ZZ(2));
        pcl = ZZ_pContext(power2_ZZ(L));
    }
    return *this;
}

template <int L>
template <int K>
ExtensionRing<L>& ExtensionRing<L>::operator=(const Z2<K>& other) {
    ExtensionRing<L>();
    SetCoeff(f, 0, to_ZZ_p(other.debug()));
    return *this;
}

template <int L>
ExtensionRing<L>& ExtensionRing<L>::operator=(const long& other) {
    ExtensionRing<L>();
    SetCoeff(f, 0, to_ZZ_p(other));
    return *this;
}

template <int L>
template <class U>
ExtensionRing<L>& ExtensionRing<L>::operator=(const gf2n_<U>& a) {
    ExtensionRing<L>();
    int size = a.size_in_bits();
    for (int i = 0; i < min(size, L); i ++) {
        if (a.get_bit(i)) {
            SetCoeff(f, i);
        }
    }
}


// comparison
template <int L>
bool operator==(const ExtensionRing<L>& self, const ExtensionRing<L>& other);

// Addition
template <int L>
ExtensionRing<L> operator+(const ExtensionRing<L>& self, const ExtensionRing<L>& other);

template <int L>
ExtensionRing<L>& operator+=(ExtensionRing<L>& self, const ExtensionRing<L>& other);


template <int L>
ExtensionRing<L> operator-(const ExtensionRing<L>& self, const ExtensionRing<L>& other);

template <int L>
ExtensionRing<L>& operator-=(ExtensionRing<L>& self, const ExtensionRing<L>& other);


// Multiplication
template <int L>
ExtensionRing<L> operator*(const ExtensionRing<L> self, const ExtensionRing<L>& other);

template <int L>
ExtensionRing<L>& operator*=(ExtensionRing<L>& self, const ExtensionRing<L>& other);

template <int L>
ExtensionRing<L> operator/(const ExtensionRing<L> self, const ExtensionRing<L>& other);

template <int L>
ExtensionRing<L>& operator/=(ExtensionRing<L>& self, const ExtensionRing<L>& other);


/*
            Implementation
*/

template <int L>
ExtensionRing<L>::ExtensionRing() {

    ZZ_p::init(power2_ZZ(L));

    for (int i = 0; i < num_2_fields; i ++) {
        if (fields_2[i][0] == L) {
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

    pc2 = ZZ_pContext(ZZ(2));
    pcl = ZZ_pContext(power2_ZZ(L));
}

template <int L>
ExtensionRing<L>::ExtensionRing(ZZ_pX _f): ExtensionRing() {
    f = _f % modulus;
}

template <int L>
ExtensionRing<L>::ExtensionRing(ZZ_pX _f, ZZ_pX _modulus) {
    this->f = _f % _modulus;
    this->modulus = _modulus;
    pc2 = ZZ_pContext(ZZ(2));
    pcl = ZZ_pContext(power2_ZZ(L));
}

template <int L>
ExtensionRing<L>::ExtensionRing(long a): ExtensionRing() {
    SetCoeff(f, 0, to_ZZ_p(a));
}

template <int L>
template <int K>
ExtensionRing<L>::ExtensionRing(Z2<K> a): ExtensionRing() {
    SetCoeff(f, 0, to_ZZ_p(a.debug()));
}

template <int L>
template <class U>
ExtensionRing<L>::ExtensionRing(gf2n_<U> a): ExtensionRing() {
    int size = a.size_in_bits();
    for (int i = 0; i < min(size, L); i ++) {
        if (a.get_bit(i)) {
            SetCoeff(f, i);
        }
    }
}


void copy(ZZ_pX& rhs, const ZZ_pX lhs, ZZ_pContext ctx) {
    ZZ_pContext bak;
    bak.save();
    ctx.restore();
    ZZ mod = ZZ_p::modulus();
    int degree = deg(lhs);
    for (int i = 0; i <= degree; i++) {
        SetCoeff(rhs, i, to_ZZ_p(rep(lhs[i]) % mod));
    }
    bak.restore();
}

template <int L>
void ExtensionRing<L>::random(int size) {
    NTL::random(f, size);
}

template <int L>
inline int ExtensionRing<L>::getL() {
    return L;
}

template <int L>
inline ZZ_pX ExtensionRing<L>::get() {
    return f;
}

template <int L>
inline ZZ_pX ExtensionRing<L>::get_modulus() {
    return modulus;
}

template <int L>
bool operator==(const ExtensionRing<L>& self, const ExtensionRing<L>& other) {
    return self.f == other.f && self.modulus == other.modulus;
}

template <int L>
bool operator!=(const ExtensionRing<L>& self, const ExtensionRing<L>& other) {
    return !(self == other);
}

template <int L>
ExtensionRing<L> operator+(const ExtensionRing<L>& self, const ExtensionRing<L>& other) {
    assert(self.modulus == other.modulus);
    return ExtensionRing<L>((self.f + other.f) % self.modulus, self.modulus);
}

template <int L>
ExtensionRing<L>& operator+=(ExtensionRing<L>& self, const ExtensionRing<L>& other) {
    assert(self.modulus == other.modulus);
    self = self + other;
    return self;
}

template <int L>
ExtensionRing<L> operator-(const ExtensionRing<L>& self, const ExtensionRing<L>& other) {
    assert(self.modulus == other.modulus);
    return ExtensionRing<L>((self.f - other.f) % self.modulus, self.modulus);
}

template <int L>
ExtensionRing<L>& operator-=(ExtensionRing<L>& self, const ExtensionRing<L>& other) {
    assert(self.modulus == other.modulus);
    self = self - other;
    return self;
}

template <int L>
ExtensionRing<L> operator*(const ExtensionRing<L> self, const ExtensionRing<L>& other) {
    assert(self.modulus == other.modulus);
    return ExtensionRing<L>((self.f * other.f) % self.modulus, self.modulus);
}

template <int L>
ExtensionRing<L>& operator*=(ExtensionRing<L>& self, const ExtensionRing<L>& other) {
    assert(self.modulus == other.modulus);
    self = self * other;
    return self;
}

template <int L>
ExtensionRing<L> ExtensionRing<L>::invert() {

    ZZ_pContext bak;
    bak.save();

    ExtensionRing<L>::pc2.restore();

    ZZ_pX f2;
    ZZ_pX f_mod2;
    copy(f2, f, pc2);
    copy(f_mod2, modulus, pc2);

    ZZ_pX d, a, b;  
    XGCD(d, a, b, f_mod2, f2);

    ExtensionRing<L>::pcl.restore();

    ZZ_pX h = 1 - (a * modulus + b * f);

    ZZ_pX B = ZZ_pX::zero();

    for (int i = 0; i < L; i ++) {
        B += power(h, i);
    }

    B *= b;

    bak.restore();
    return ExtensionRing<L>(B, modulus);
}

template <int L>
ExtensionRing<L> operator/(const ExtensionRing<L> self, const ExtensionRing<L>& other) {
    assert(self.modulus == other.modulus);
    return ExtensionRing<L>((self.f * other.inverse()) % self.modulus, self.modulus);
}

template <int L>
ExtensionRing<L>& operator/=(ExtensionRing<L>& self, const ExtensionRing<L>& other) {
    assert(self.modulus == other.modulus);
    self = self / other;
    return self;
}

void store_ZZ_pX(ZZ_pX f, octetStream &os) {
    os.store((int) deg(f));
    size_t l;
    unsigned char *write_head;
    for (int i = 0; i <= deg(f); i ++) {
        l = NumBytes(f[i]._ZZ_p__rep);
        os.store(l);
        write_head = os.append(l);
        BytesFromZZ(write_head, f[i]._ZZ_p__rep, l);
    }
}

ZZ_pX restore_ZZ_pX(octetStream &os) {
    int d;
    os.get(d);
    size_t l;
    ZZ_pX ret = ZZ_pX::zero();
    unsigned char *read_head;
    for (int i = 0; i <= d; i ++) {
        os.get(l);
        read_head = os.consume(l);
        SetCoeff(ret, i, to_ZZ_p(ZZFromBytes(read_head, l)));
    }

    return ret;
}

template <int L>
void ExtensionRing<L>::pack(octetStream &os) {
    store_ZZ_pX(f, os);
}

template <int L>
void ExtensionRing<L>::unpack(octetStream &os) {
    f = restore_ZZ_pX(os);
    modulus = ZZ_pX::zero();
    for (int i = 0; i < num_2_fields; i ++) {
        if (fields_2[i][0] == L) {
            SetCoeff(modulus, fields_2[i][0]);
            SetCoeff(modulus, fields_2[i][1]);
            SetCoeff(modulus, fields_2[i][2]);
            SetCoeff(modulus, fields_2[i][3]);
            break;
        }
    }
    SetCoeff(modulus, 0);
}

template <int L>
ExtensionRing<L> ExtensionRing<L>::conv_from_int(unsigned int x) {
    int idx = 0;
    ExtensionRing<L> ret;

    while (x && idx < L) {
        if (x & 1) {
            SetCoeff(ret.f, idx);
        }
        x >>= 1;
        idx ++;
    }

    return ret;
}

template <int L>
void ExtensionRing<L>::randomize(PRNG& g) {
    uint64_t data = g.get_word();
    f = ZZ_pX::zero();
    for (int i = 0; i < L; i ++) {
        if ((data >> i) & 1) {
            SetCoeff(f, i);
        }
    }
}

template <int L>
ExtensionRing<L> inner_product(ExtensionRing<L>* a, ExtensionRing<L>* b, size_t size) {
    ZZ_pX ans = ZZ_pX::zero();

    for (size_t i = 0; i < size; i ++) {
        ans += a[i].f * b[i].f;
    }

    return ExtensionRing<L>(ans);

}

template <int L>
ExtensionRing<L> inner_product(ExtensionRing<L>** a, ExtensionRing<L>** b, size_t rows, size_t cols) {
    ZZ_pX ans = ZZ_pX::zero();
    for (size_t i = 0; i < rows; ++i) {
        for (size_t j = 0; j < cols; ++j) {
            ans += a[i][j].f * b[i][j].f;
        }
    }

    return ExtensionRing<L>(ans);
}

template <int L>
ExtensionRing<L> inner_product(ExtensionRing<L>* a, vector<ExtensionRing<L>> b, size_t size) {
    ZZ_pX ans = ZZ_pX::zero();

    for (size_t i = 0; i < size; i ++) {
        ans += a[i].f * b[i].f;
    }

    return ExtensionRing<L>(ans);
}

#endif