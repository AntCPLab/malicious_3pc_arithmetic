/*
 * Semi-honest ring protocol
 *
 */

#ifndef PROTOCOLS_TESTPROTOCOL_H_
#define PROTOCOLS_TESTPROTOCOL_H_

#define USE_MY_MULTIPLICATION
// #define SHOW_TIMECOST_LOGS

// #define USE_SINGLE_THREAD

#include "Protocols/Replicated.h"
#include "Protocols/MAC_Check_Base.h"
#include "Processor/Input.h"
#include "Protocols/SemiMC.h"
#include "Tools/random.h"

#include <thread>
#include <mutex>
#include <condition_variable>

#include "Tools/SafeQueue.h"
#include "Tools/my-utils.hpp"

typedef unsigned __int128 uint128_t;
typedef uint64_t MulRing;
typedef uint128_t VerifyRing;

const int N = 64;
const int KAPPA = 40;
const int EBITS = 64;

void print_uint128(uint128_t x) {
    if (x > 9) print_uint128(x / 10);
    putchar(x % 10 + '0');
}

#define show_uint128(value) \
    cout << #value << " = "; \
    print_uint128(value); \
    cout << endl;

typedef array<uint64_t, 2> RSShare;
struct MultiShare {
    RSShare x, y;
    RSShare z;
    RSShare rho;

    MultiShare() {
        x = {0, 0};
        y = {0, 0};
        z = {0, 0};
        rho = {0, 0};
    }
    
    MultiShare(RSShare x, RSShare y, RSShare z, RSShare rho) {
        this->x = x;
        this->y = y;
        this->z = z;
        this->rho = rho;
    }
};

template<class T>
class TestProtocol : public ProtocolBase<T>, public ReplicatedBase
{

    typedef ReplicatedBase super;

    array<octetStream, 2> os;
    PointerVector<typename T::clear> add_shares;
    typename T::clear dotprod_share;

    MultiShare *verify_shares;
    int pointer, pointer_answer, iter, Nbatches;
    int offset_data_xy, offset_data_z, offset_mono, offset_z_shares, offset_z_masks;

    PRNG global_prng, local_prng;

    int batch_size, ms, k, new_batch_size;
    VerifyRing *X_prover, *Y_prover, *Y_right, *X_left, *_Z_left, *_Z_right, *E;

    MulRing *a_triples, *b_triples, *c_triples, *kappa_c_triples;
    MulRing *kappa_e_left, *kappa_e_right, *thread_buffer_e_shares;
    MulRing *res_o_ss, *res_o_third_ss;

    VerifyRing *thread_buffer_c_add_shares, *kappa_c_add_shares_left, *kappa_c_add_shares_right;
    VerifyRing *kappa_c_add_shares_prover_left, *kappa_c_add_shares_prover_right;
   
    VerifyRing *lift_kappa_c_add_shares_left, *lift_kappa_c_add_shares_right;

    bool **choices;

    VerifyRing *random_coef_left, *random_coef_right, *random_coef_prover;
    VerifyRing *counter_prover, *counter_left, *counter_right;
    VerifyRing *thread_buffer;
    VerifyRing *Z_left, *Z_right;

    VerifyRing *XY_mask_left, *XY_mask_right, *XY_mask_prover, *Z_masks_left, *Z_masks_right, *Z_masks_prover;
    VerifyRing *XY_mask_thread_buffer, *Z_masks_thread_buffer;

    VerifyRing *coeffsX_prover, *coeffsY_prover;
    VerifyRing *coeffsX_left, *coeffsY_left;
    VerifyRing *coeffsX_right, *coeffsY_right;

    VerifyRing ***local_right, ***local_left;

    int s, vec_len;

    WaitSize ws;
    WaitQueue<MyPair<int, int> > cv;
    vector<shared_ptr<std::thread>> verify_threads;

    bool zero_check_flag = true;
    bool zkp_flag = true;

    template<class U>
    void trunc_pr(const vector<int>& regs, int size, U& proc, true_type);
    template<class U>
    void trunc_pr(const vector<int>& regs, int size, U& proc, false_type);

public:
    
    static const bool uses_triples = false;

    TestProtocol() {}
    TestProtocol(Player& P);
    TestProtocol(const ReplicatedBase &other) : 
        ReplicatedBase(other)
    {
    }

    // Init the protocol
    TestProtocol(const TestProtocol<T> &other) : super(other)
    {
        
    }

    ~TestProtocol() {

        if (X_prover == NULL)   return ;

        if (pointer > 0) {
            if (batch_size && pointer % batch_size != 0) {
                int padding = batch_size - pointer % batch_size;
                // cout << pointer << ", " << padding << endl;

                memset(X_prover + pointer * 2, 0, sizeof(VerifyRing) * padding * 2 * 2);
                memset(Y_prover + pointer * 2, 0, sizeof(VerifyRing) * padding * 2 * 2);
                memset(Y_right + pointer * 2, 0, sizeof(VerifyRing) * padding * 2 * 2);
                memset(X_left + pointer * 2, 0, sizeof(VerifyRing) * padding * 2 * 2);
                memset(E + pointer, 0, sizeof(VerifyRing) * padding * 2);

                memset(a_triples + pointer * 2, 0, sizeof(VerifyRing) * padding * 2 * 2);
                memset(b_triples + pointer * 2, 0, sizeof(VerifyRing) * padding * 2 * 2);
                memset(c_triples + pointer * 2, 0, sizeof(VerifyRing) * padding * 2 * 2);
            }
            verify_api();
        }

        // cout << "Pushing" << endl;

        for (int i = 0; i < (int) verify_threads.size(); i ++) {
            cv.push(MyPair<int, int>(0, 0));
        }

        // cout << "Joining" << endl;

        for (auto &thread: verify_threads) {
            if (thread->joinable()) {
                thread->join();
                // cout << "Joined" << endl;
            }
        }

        if(!zero_check_flag)  
            cout << "Zero check failed" << endl;
        if(!zkp_flag)  
            cout << "ZKP failed" << endl;    

        // cout << "Cleaning" << endl;

        delete[] X_prover;
        delete[] Y_prover;
        delete[] Y_right;
        delete[] X_left;
        delete[] E;

        delete[] a_triples;
        delete[] b_triples;
        delete[] c_triples;
        delete[] kappa_c_triples;
        delete[] kappa_c_add_shares_left;
        delete[] kappa_c_add_shares_right;
        delete[] kappa_c_add_shares_prover_left;
        delete[] kappa_c_add_shares_prover_right;
        delete[] thread_buffer_c_add_shares;
        delete[] res_o_ss;
        delete[] res_o_third_ss;
        delete[] kappa_e_left;
        delete[] kappa_e_right;
        delete[] thread_buffer_e_shares;
        delete[] lift_kappa_c_add_shares_left;
        delete[] lift_kappa_c_add_shares_right;

        // if (thread_buffer)
        //     delete[] thread_buffer;
        // if (thread_buffer_c_add_shares)
        //     delete[] thread_buffer_c_add_shares;

        if (choices) {
            for (int i = 0; i < KAPPA; i++) {
                if (choices[i])
                    delete[] choices[i];
            }
            delete[] choices;
        }

        delete[] random_coef_left;
        delete[] random_coef_right;
        delete[] random_coef_prover;

        delete[] counter_prover;
        delete[] counter_left;
        delete[] counter_right;

        delete[] Z_left;
        delete[] Z_right;

        delete[] coeffsX_prover;
        delete[] coeffsY_prover;
        delete[] coeffsX_left  ;
        delete[] coeffsY_left  ;
        delete[] coeffsX_right ;
        delete[] coeffsY_right ;

        for (int i = 0; i < ms; i ++) {
            for (int j = 0; j < k; j ++) {
                delete[] local_left[i][j];
                delete[] local_right[i][j];
            }
            delete[] local_left[i];
            delete[] local_right[i];
        }

        delete[] local_left;
        delete[] local_right;
    }


    // Public input.
    static void assign(T& share, const typename T::clear& value, int my_num)
    {
        assert(T::vector_length == 2);
        share.assign_zero();
        if (my_num < 2)
            share[my_num] = value;
        
        share.is_zero_share = true;
    }

    // prepare next round of multiplications
    void init_mul();

    // schedule multiplication
    void prepare_mul(const T&, const T&, int = -1);

    // execute protocol
    void exchange();

    template<class U>
    void trunc_pr(const vector<int>& regs, int size, U& proc);

    // return next product
    T finalize_mul(int = -1);

    void init_dotprod();
    void prepare_dotprod(const T& x, const T& y);
    void next_dotprod();
    T finalize_dotprod(int length);

    // void multiply(vector<T>& products, vector<pair<T, T>>& multiplicands,
    //         int begin, int end, SubProcessor<T>& proc);

    T get_random();

    void verify();

    template <typename U>
    U inner_product(U* v1, U* v2, size_t length) {
        U res = 0;
        for (size_t i = 0; i < length; i ++) {
            res += v1[i] * v2[i];
        }

        return res;
    }

    void verify_thread_handler();
    void verify_part1(int batch_id);
    void verify_part2(int batch_id);
    void verify_part3(int batch_id);
    void verify_part4(int batch_id);
    void verify_part5(int batch_id);
    void verify_part8(int batch_id);
    void verify_part9(int batch_id);

    void verify_api() {
        if (!pointer_answer)    return;

        while (pointer_answer >= batch_size * ms) {
            verify();
            pointer -= batch_size * ms;
            pointer_answer -= batch_size * ms;
        }
    }

};

#endif /* PROTOCOLS_SEMIRINGPROTOCOL_H_ */