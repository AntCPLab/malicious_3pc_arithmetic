#include <vector>

#include "../Tools/Hash.h"
#include "../Math/gf2n.h"
#include "../Tools/octetStream.h"
// #include "../Math/ExtensionRing.hpp"
#include "../Math/ExtensionRingSmall.hpp"
#include "../Processor/OnlineOptions.h"

using namespace std;

// max bit_length for small extension ring is 59
typedef ExtensionRingSmall<59, 47> VerifyRing;
// typedef gf2n_long VerifyRing;

#define CACHE_SIZE 32

static VerifyRing caches[CACHE_SIZE][CACHE_SIZE];

VerifyRing customized_inverse(uint64_t i, uint64_t j) {
	if (caches[i][j])	return caches[i][j];
	caches[i][j] = (VerifyRing::conv_from_int(i) - VerifyRing::conv_from_int(j)).invert();
	return caches[i][j];
}

struct ArithDZKProof {
    vector<vector<VerifyRing>> p_evals_masked;

    // void print_out() {
    //     cout << "proof: ";
    //     for(auto row: p_evals_masked) {
    //         for(auto x: row) {
    //             cout << x << " ";
    //         }
    //     }
    //     cout << endl;
    // }

    void pack(octetStream &os) {
        os.store(p_evals_masked.size());
        for (auto each1: p_evals_masked) {
            os.store(each1.size());
            for (auto each2: each1) {
                each2.pack(os);
            }
        }
    }

    void unpack(octetStream &os) {
        size_t size = 0;
        os.get(size);
        p_evals_masked.resize(size);
        for (size_t i = 0; i < size; i ++) {
            size_t each_size = 0;
            os.get(each_size);
            p_evals_masked[i].resize(each_size);
            for (size_t j = 0; j < each_size; j ++) {
                p_evals_masked[i][j].unpack(os);
            }
        }
    }

    ArithDZKProof& operator = (const ArithDZKProof &other) {
        this->p_evals_masked.clear();
        this->p_evals_masked.resize(other.p_evals_masked.size());
        for (size_t i = 0; i < other.p_evals_masked.size(); i ++) {
            this->p_evals_masked[i].clear();
            this->p_evals_masked[i].resize(other.p_evals_masked[i].size());
            copy(other.p_evals_masked[i].begin(), other.p_evals_masked[i].end(), this->p_evals_masked[i].begin());
        }
        return *this;
    }
};

struct ArithVerMsg {
    vector<VerifyRing> b_ss;
    VerifyRing final_input;
    VerifyRing final_result_ss;

    ArithVerMsg() {}
    ArithVerMsg(vector<VerifyRing> b_ss, VerifyRing final_input, VerifyRing final_result_ss) {
        this->b_ss = b_ss;
        this->final_input = final_input;
        this->final_result_ss = final_result_ss;
    }

    void pack(octetStream &os) {
        os.store(b_ss.size());
        for (auto each: b_ss) {
            each.pack(os);
        }

        final_input.pack(os);
        final_result_ss.pack(os);
    }

    void unpack(octetStream &os) {
        size_t size = 0;
        os.get(size);
        b_ss.resize(size);

        for (size_t i = 0; i < size; i ++) {
            b_ss[i].unpack(os);
        }

        final_input.unpack(os);
        final_result_ss.unpack(os);
    }

    ArithVerMsg& operator = (const ArithVerMsg &other) {
        this->b_ss.clear();
        this->b_ss.resize(other.b_ss.size());
        copy(other.b_ss.begin(), other.b_ss.end(), this->b_ss.begin());
        this->final_input = other.final_input;
        this->final_result_ss = other.final_result_ss;
        return *this;
    }
};

template <class T>
class Langrange {
public:
    static void get_bases(uint64_t n, T** result);
    static void evaluate_bases(uint64_t n, T r, T* result);
};

template <class T>
inline void Langrange<T>::get_bases(uint64_t n, T** result) {
    for (uint64_t i = 0; i < n - 1; i++) {
        for(uint64_t j = 0; j < n; j++) {
            result[i][j].assign_one();
            for(uint64_t l = 0; l < n; l++) {
                if (l != j) {
                    // T denominator, numerator;
                    // denominator = T::conv_from_int(j) - T::conv_from_int(l);
                    // numerator = T::conv_from_int(i + n) - T::conv_from_int(l);
                    // result[i][j] = result[i][j] * denominator.invert() * numerator;

					result[i][j] = result[i][j] * customized_inverse(j, l) * (T::conv_from_int(i + n) - T::conv_from_int(l));
                }
            }
        }
    }
}

template <class T>
inline void Langrange<T>::evaluate_bases(uint64_t n, T r, T* result) {
    for(uint64_t i = 0; i < n; i++) {
        result[i].assign_one();
        for(uint64_t j = 0; j < n; j++) {
            if (j != i) {
                // T denominator, numerator; 
                // denominator = T::conv_from_int(i) - T::conv_from_int(j);
                // numerator = r - T::conv_from_int(j);
                // result[i] = result[i] * denominator.invert() * numerator;
				result[i] = result[i] * customized_inverse(i, j) * (r - T::conv_from_int(j));
            }
        }
    }
}

template <class U>
gf2n_<U> inner_product(const gf2n_<U>* x, const gf2n_<U>* y, size_t length) {
  gf2n_<U> answer;
  int128 tmp;
  for (size_t i = 0; i < length; ++i) {
    tmp ^= clmul<0>(int128(x[i].get()).a, int128(y[i].get()).a);
  }

  answer.reduce(tmp.get_upper(), tmp.get_lower());

  return answer;
}

gf2n_long inner_product(gf2n_long* x, vector<gf2n_long> y, size_t length) {
  gf2n_long answer;
  int128 tmp;
  for (size_t i = 0; i < length; ++i) {
    tmp ^= clmul<0>(int128(x[i].get()).a, int128(y[i].get()).a);
  }

  answer.reduce(tmp.get_upper(), tmp.get_lower());

  return answer;
}

gf2n_long inner_product(gf2n_long** x, gf2n_long** y, size_t rows, size_t cols) {
  gf2n_long answer;
  int128 tmp;
  for (size_t i = 0; i < rows; ++i) {
    for (size_t j = 0; j < cols; ++j) {
      tmp ^= clmul<0>(int128(x[i][j].get()).a, int128(y[i][j].get()).a);
    }
  }

  answer.reduce(tmp.get_upper(), tmp.get_lower());

  return answer;
}

gf2n_long inner_product_naive(gf2n_long* x, gf2n_long* y, size_t length) {
  gf2n_long answer = gf2n_long(0);
  for (size_t i = 0; i < length; ++i) {
    answer += x[i] * y[i];
  }
  return answer;
}

gf2n_long inner_product_naive(gf2n_long* x, vector<gf2n_long> y, size_t length) {
  gf2n_long answer = gf2n_long(0);
  for (size_t i = 0; i < length; ++i) {
    answer += x[i] * y[i];
  }
  return answer;
}

gf2n_long inner_product_naive(gf2n_long** x, gf2n_long** y, size_t rows, size_t cols) {
  gf2n_long answer = gf2n_long(0);
  for (size_t i = 0; i < rows; ++i) {
    for (size_t j = 0; j < cols; ++j) {
      answer += x[i][j] * y[i][j];
    }
  }
  return answer;
}