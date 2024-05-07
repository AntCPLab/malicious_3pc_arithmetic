
#ifndef PROTOCOLS_TESTPROTOCOL_HPP_
#define PROTOCOLS_TESTPROTOCOL_HPP_

#include "TestProtocol.h"
#include "Replicated.hpp"

#include "Tools/benchmarking.h"
#include "Tools/Bundle.h"

#include "global_debug.hpp"
#include <ctime>
#include <chrono>

template <class T>
TestProtocol<T>::TestProtocol(Player &P) : ReplicatedBase(P)
{
	assert(T::vector_length == 2);

    pointer = 0;
    pointer_answer = 0;
    iter = 0;

    batch_size = OnlineOptions::singleton.batch_size;
    ms = OnlineOptions::singleton.max_status;
    k = OnlineOptions::singleton.k_size;
    new_batch_size = batch_size * 2;
    
    X_prover = new VerifyRing[new_batch_size * ms * 2];     // only works when batch_size % k == 0, otherwise it need to be (new_batch_size + k) * ms
    Y_prover = new VerifyRing[new_batch_size * ms * 2];
    Y_right = new VerifyRing[new_batch_size * ms * 2];
    X_left = new VerifyRing[new_batch_size * ms * 2];

    E = new VerifyRing[batch_size * ms];                // uint64_t also works

    a_triples = new MulRing[new_batch_size * ms];
    b_triples = new MulRing[new_batch_size * ms];
    c_triples = new MulRing[new_batch_size * ms];
    kappa_c_triples = new MulRing[KAPPA * ms * 2];

    kappa_c_add_shares_left = new VerifyRing[KAPPA * ms];
    kappa_c_add_shares_right = new VerifyRing[KAPPA * ms];
    kappa_c_add_shares_prover_left = new VerifyRing[KAPPA * ms];
    kappa_c_add_shares_prover_right = new VerifyRing[KAPPA * ms];
    thread_buffer_c_add_shares = new VerifyRing[KAPPA * ms];

    thread_buffer_e_shares = new MulRing[KAPPA * ms];
    kappa_e_left = new MulRing[KAPPA * ms];
    kappa_e_right = new MulRing[KAPPA * ms];

    lift_kappa_c_add_shares_left = new VerifyRing[KAPPA * ms];
    lift_kappa_c_add_shares_right = new VerifyRing[KAPPA * ms];

    res_o_ss = new MulRing[KAPPA * ms * 2];
    res_o_third_ss = new MulRing[KAPPA * ms];

    thread_buffer = new VerifyRing[new_batch_size * ms * 2];

    choices = new bool*[KAPPA];
      
    for (int i = 0; i < KAPPA; i++) {
        choices[i] = new bool[batch_size];
    }

    random_coef_left = new VerifyRing[KAPPA];
    random_coef_right = new VerifyRing[KAPPA];
    random_coef_prover = new VerifyRing[KAPPA];

    counter_prover = new VerifyRing[batch_size];
    counter_left = new VerifyRing[batch_size];
    counter_right = new VerifyRing[batch_size];

    Z_left = new VerifyRing[ms * 2];
    Z_right = new VerifyRing[ms * 2];

    coeffsX_prover = new VerifyRing[k * 2];
    coeffsY_prover = new VerifyRing[k * 2];
    coeffsX_left = new VerifyRing[k * 2];
    coeffsY_left = new VerifyRing[k * 2];
    coeffsX_right = new VerifyRing[k * 2];
    coeffsY_right = new VerifyRing[k * 2];

    local_left = new VerifyRing**[ms];
    local_right = new VerifyRing**[ms];

    for (int i = 0; i < ms; i ++) {
        local_left[i] = new VerifyRing*[k * 2];
        local_right[i] = new VerifyRing*[k * 2];
        for (int j = 0; j < 2 * k; j ++) {
            local_left[i][j] = new VerifyRing[k * 2];
            local_right[i][j] = new VerifyRing[k * 2];
        }
    }

    XY_mask_left = new VerifyRing[ms * 2 * 2];
    XY_mask_right = new VerifyRing[ms * 2 * 2];    
    XY_mask_prover = new VerifyRing[ms * 2 * 2];
    XY_mask_thread_buffer = new VerifyRing[ms * 2 * 2];

    Z_masks_left = new VerifyRing[ms * (2 * k + 1) * 2];
    Z_masks_right = new VerifyRing[ms * (2 * k + 1) * 2];
    Z_masks_prover = new VerifyRing[ms * (2 * k + 1) * 2];
    Z_masks_thread_buffer = new VerifyRing[ms * (2 * k + 1) * 2];

#ifndef USE_SINGLE_THREAD
    cout << "Adding threads" << endl;
    // chatGPT taught me to do this. Brilliant
    for (int i = 0; i < OnlineOptions::singleton.thread_number; i++) {
        std::shared_ptr<std::thread> _thread(new std::thread(&TestProtocol<T>::verify_thread_handler, this));
        verify_threads.push_back(_thread);
    }
    cout << "Thread size: " << verify_threads.size() << endl;
#endif

    octetStream os;
	os.append(shared_prngs[0].get_seed(), SEED_SIZE);
	P.send_relative(1, os);
	P.receive_relative(-1, os);
	shared_prngs[1].SetSeed(os.get_data());

    os.reset_write_head();

    local_prng.ReSeed();

}


template<class T>
void TestProtocol<T>::init_mul() {

	for (auto& o : os)
        o.reset_write_head();
    add_shares.clear();

    verify_api();
}


template <class T>
void TestProtocol<T>::verify_part1(int batch_id) {

    memset(kappa_c_triples + batch_id * KAPPA * 2, 0, sizeof(MulRing) * KAPPA * 2);

    // compute share_right of kappa higher-bit errors
    for (int i = 0; i < KAPPA; i ++) {

        VerifyRing e = 0;
        for (int j = 0; j < batch_size; j ++) {
            if (choices[i][j]) {
                e += E[batch_id * batch_size + j];
                kappa_c_triples[batch_id * KAPPA * 2 + i * 2] += c_triples[batch_id * new_batch_size + j * 2];
                kappa_c_triples[batch_id * KAPPA * 2 + i * 2 + 1] += c_triples[batch_id * new_batch_size + j * 2 + 1];
            }
        }

        // share the merged additive share of c (last 64 bits of e)
        thread_buffer_c_add_shares[batch_id * KAPPA + i] = (MulRing) e - thread_buffer_c_add_shares[batch_id * KAPPA + i];

        // get higher-bit errors (higher 64 bits of e)
        e = e >> 64;
        // share higher-bit errors
        MulRing tmp = thread_buffer_e_shares[batch_id * KAPPA + i];
        thread_buffer_e_shares[batch_id * KAPPA + i] = (MulRing) e - tmp;
        if (tmp + thread_buffer_e_shares[batch_id * KAPPA + i] < tmp) {
            thread_buffer_e_shares[batch_id * KAPPA + i] -= 1;
        }
    }

    ++ ws;

}

template <class T>
void TestProtocol<T>::verify_part8(int batch_id) {

    for (int i = 0; i < KAPPA; i ++) {
        // share with next party
        res_o_ss[batch_id * KAPPA * 2 + i * 2] = kappa_c_triples[batch_id * KAPPA * 2 + i * 2] - kappa_c_add_shares_left[batch_id * KAPPA + i] - kappa_c_add_shares_prover_right[batch_id * KAPPA + i];
        // share with previous party
        res_o_ss[batch_id * KAPPA * 2 + i * 2 + 1] = kappa_c_triples[batch_id * KAPPA * 2 + i * 2 + 1] - kappa_c_add_shares_right[batch_id * KAPPA + i] - kappa_c_add_shares_prover_left[batch_id * KAPPA + i];
    }
    
    ++ ws;
}

template <class T>
void TestProtocol<T>::verify_part9(int batch_id) {

    MulRing o;
    for (int i = 0; i < KAPPA; i ++) {
        o = res_o_ss[batch_id * KAPPA * 2 + i * 2] + res_o_ss[batch_id * KAPPA * 2 + i * 2 + 1] + res_o_third_ss[batch_id * KAPPA + i];
        if (o != 0) {
            zero_check_flag = false;
            // throw mac_fail("Zero check failed");
            // cout << "Zero check failed" << endl;
        }
    }
    
    ++ ws;
}

template <class T>
void TestProtocol<T>::verify_part2(int batch_id) {

    for (int i = 0; i < KAPPA; i ++) {
        // c_i + 2^k * h_i
        lift_kappa_c_add_shares_left[batch_id * KAPPA + i] = (VerifyRing) kappa_c_add_shares_left[batch_id * KAPPA + i] + (((VerifyRing) kappa_e_left[batch_id * KAPPA + i]) << 64);
        lift_kappa_c_add_shares_right[batch_id * KAPPA + i] = (VerifyRing) kappa_c_add_shares_right[batch_id * KAPPA + i] + (((VerifyRing) kappa_e_right[batch_id * KAPPA + i]) << 64);
    }

    ++ ws;
}

template <class T>
void TestProtocol<T>::verify_part3(int batch_id) {

    Z_left[batch_id] = 0;
    Z_right[batch_id] = 0;

    for (int i = 0; i < KAPPA; i ++) {
        Z_left[batch_id] += lift_kappa_c_add_shares_left[batch_id * KAPPA + i] * random_coef_left[i];
        Z_right[batch_id] += lift_kappa_c_add_shares_right[batch_id * KAPPA + i] * random_coef_right[i];
    }

    for (int j = 0; j < batch_size; j ++) {
        // y[1]
        X_prover[batch_id * new_batch_size + j * 2] = (VerifyRing) b_triples[batch_id * new_batch_size + j * 2 + 1] * counter_prover[j];
        Y_right[batch_id * new_batch_size + j * 2 + 1] = (VerifyRing) b_triples[batch_id * new_batch_size + j * 2 + 1] * counter_right[j];
        // x[1]
        X_prover[batch_id * new_batch_size + j * 2 + 1] = (VerifyRing) a_triples[batch_id * new_batch_size + j * 2 + 1] * counter_prover[j];
        Y_right[batch_id * new_batch_size + j * 2] = (VerifyRing) a_triples[batch_id * new_batch_size + j * 2 + 1] * counter_right[j];
        // x[0]
        Y_prover[batch_id * new_batch_size + j * 2] = (VerifyRing) a_triples[batch_id * new_batch_size + j * 2] * counter_prover[j];
        X_left[batch_id * new_batch_size + j * 2 + 1] = (VerifyRing) a_triples[batch_id * new_batch_size + j * 2] * counter_left[j];
        // y[0]
        Y_prover[batch_id * new_batch_size + j * 2 + 1] = (VerifyRing) b_triples[batch_id * new_batch_size + j * 2] * counter_prover[j];
        X_left[batch_id * new_batch_size + j * 2] = (VerifyRing) b_triples[batch_id * new_batch_size + j * 2] * counter_left[j];
        // x[1] * y[1]
        Z_right[batch_id] -= (VerifyRing) a_triples[batch_id * new_batch_size + j * 2 + 1] * (VerifyRing) b_triples[batch_id * new_batch_size + j * 2 + 1] * counter_right[j];
    }

    ++ ws;
}

template <class T>
void TestProtocol<T>::verify_part4(int batch_id) {

    // cout << "in verify_part4" << endl;

    for (int i = 0; i < k; i ++) {
        for (int j = 0; j < k; j ++) {
            if (i == 0 && j == 0) {
                continue;
            }
            if (iter == 0) {
                VerifyRing ip = inner_product(X_prover + batch_id * new_batch_size + i * vec_len, 
                                Y_prover + batch_id * new_batch_size + j * vec_len, 
                                vec_len);

                thread_buffer[batch_id * k * k + i * k + j] = ip - thread_buffer[batch_id * k * k + i * k + j];
                thread_buffer[offset_z_shares + batch_id * k * k + i * k + j] = ip - thread_buffer[offset_z_shares + batch_id * k * k + i * k + j];
            } 
            else {
                thread_buffer[batch_id * k * k + i * k + j] = 
                    inner_product(X_prover + batch_id * new_batch_size + i * vec_len, 
                                Y_prover + batch_id * new_batch_size + j * vec_len, 
                                vec_len)
                    - thread_buffer[batch_id * k * k + i * k + j];

                thread_buffer[offset_z_shares + batch_id * k * k + i * k + j] = 
                    inner_product(X_prover + offset_data_xy + batch_id * new_batch_size + i * vec_len, 
                                Y_prover + offset_data_xy + batch_id * new_batch_size + j * vec_len, 
                                vec_len)
                    - thread_buffer[offset_z_shares + batch_id * k * k + i * k + j];
            }
        }
    }

    if (vec_len == k) {
        XY_mask_prover[2 * batch_id] = local_prng.getDoubleWord();
        XY_mask_prover[2 * batch_id + 1] = local_prng.getDoubleWord();
        XY_mask_thread_buffer[2 * batch_id] = XY_mask_prover[2 * batch_id] - XY_mask_thread_buffer[2 * batch_id];
        XY_mask_thread_buffer[2 * batch_id + 1] = XY_mask_prover[2 * batch_id] - XY_mask_thread_buffer[2 * batch_id + 1];

        XY_mask_prover[offset_mono * 2 + 2 * batch_id] = local_prng.getDoubleWord();
        XY_mask_prover[offset_mono * 2 + 2 * batch_id + 1] = local_prng.getDoubleWord();
        XY_mask_thread_buffer[offset_mono * 2 + 2 * batch_id] = XY_mask_prover[offset_mono * 2 + 2 * batch_id] - XY_mask_thread_buffer[offset_mono * 2 + 2 * batch_id];
        XY_mask_thread_buffer[offset_mono * 2 + 2 * batch_id + 1] = XY_mask_prover[offset_mono * 2 + 2 * batch_id] - XY_mask_thread_buffer[offset_mono * 2 + 2 * batch_id + 1];

        int cur_offset_z_masks = batch_id * (2 * k + 1);
        int cur_offset_xy = batch_id * new_batch_size;
        // x_0 * y_0
        Z_masks_thread_buffer[cur_offset_z_masks] = XY_mask_prover[batch_id * 2] * XY_mask_prover[batch_id * 2 + 1] - Z_masks_thread_buffer[cur_offset_z_masks];
        Z_masks_thread_buffer[cur_offset_z_masks + offset_z_masks] = XY_mask_prover[offset_mono * 2 + batch_id * 2] * XY_mask_prover[offset_mono * 2 + batch_id * 2 + 1] - Z_masks_thread_buffer[cur_offset_z_masks];

        for (int i = 0; i < k; i++) {
            // x_0 * y_i, i = 1, ... k
            Z_masks_thread_buffer[cur_offset_z_masks + 1 + i] = XY_mask_prover[batch_id * 2] * X_prover[cur_offset_xy + i] - Z_masks_thread_buffer[cur_offset_z_masks + 1 + i];
            // x_i * y_0, i = 1, ... k
            Z_masks_thread_buffer[cur_offset_z_masks + 1 + k + i] = XY_mask_prover[batch_id * 2 + 1] * Y_prover[cur_offset_xy + i] - Z_masks_thread_buffer[cur_offset_z_masks + 1 + k + i];
            Z_masks_thread_buffer[cur_offset_z_masks + offset_z_masks + 1 + i] = XY_mask_prover[offset_mono * 2 + batch_id * 2] * X_prover[cur_offset_xy + offset_data_xy + i] - Z_masks_thread_buffer[cur_offset_z_masks + offset_z_masks + 1 + i];
            Z_masks_thread_buffer[cur_offset_z_masks + offset_z_masks + 1 + k + i] = XY_mask_prover[offset_mono * 2 + batch_id * 2 + 1] * Y_prover[cur_offset_xy + offset_data_xy + i] - Z_masks_thread_buffer[cur_offset_z_masks + offset_z_masks + 1 + k + i];
        }
    }

    ++ ws;
}

template <class T>
void TestProtocol<T>::verify_part5(int batch_id) {

    // cout << "in verify_part5" << endl;

    VerifyRing res_left[k * 2], res_right[k * 2];
    int cur_offset_xy = batch_id * new_batch_size;
    int cur_offset_xy_2 = batch_id * new_batch_size + offset_data_xy;

    local_left[batch_id][0][0] = Z_left[batch_id];
    local_right[batch_id][0][0] = Z_right[batch_id];

    if (iter == 0) {
        local_left[batch_id][k][k] = Z_left[batch_id];
        local_right[batch_id][k][k] = Z_right[batch_id];
    }
    else {
        local_left[batch_id][k][k] = Z_left[offset_mono + batch_id];
        local_right[batch_id][k][k] = Z_right[offset_mono + batch_id];
    }

    for (int i = 1; i < k; i ++) {
        local_left[batch_id][0][0] -= local_left[batch_id][i][i];
        local_right[batch_id][0][0] -= local_right[batch_id][i][i];

        local_left[batch_id][k][k] -= local_left[batch_id][k + i][k + i];
        local_right[batch_id][k][k] -= local_right[batch_id][k + i][k + i];
    }

    for (int j = 0; j < vec_len; j ++) {

        if (iter == 0) { // cannot put behind (X_prover[cur_offset_xy_2 + j] already multiplied)
            X_prover[cur_offset_xy_2 + j] = X_prover[cur_offset_xy + j] * coeffsX_prover[k];
            Y_prover[cur_offset_xy_2 + j] = Y_prover[cur_offset_xy + j] * coeffsY_prover[k];
            X_left[cur_offset_xy_2 + j] = X_left[cur_offset_xy + j] * coeffsX_left[k];
            Y_right[cur_offset_xy_2 + j] = Y_right[cur_offset_xy + j] * coeffsY_right[k];
        }
        else {
            X_prover[cur_offset_xy_2 + j] *= coeffsX_prover[k];
            Y_prover[cur_offset_xy_2 + j] *= coeffsY_prover[k];
            X_left[cur_offset_xy_2 + j] *= coeffsX_left[k];
            Y_right[cur_offset_xy_2 + j] *= coeffsY_right[k];
        }

        X_prover[cur_offset_xy + j] *= coeffsX_prover[0];
        Y_prover[cur_offset_xy + j] *= coeffsY_prover[0];
        X_left[cur_offset_xy + j] *= coeffsX_left[0];
        Y_right[cur_offset_xy + j] *= coeffsY_right[0];
    }

    for (int i = 1; i < k; i ++) {
        for (int j = 0; j < vec_len; j ++) {
            if (iter == 0) {
                X_prover[cur_offset_xy_2 + j] += X_prover[cur_offset_xy + j + i * vec_len] * coeffsX_prover[k + i];
                Y_prover[cur_offset_xy_2 + j] += Y_prover[cur_offset_xy + j + i * vec_len] * coeffsY_prover[k + i];
                X_left[cur_offset_xy_2 + j] += X_left[cur_offset_xy + j + i * vec_len] * coeffsX_left[k + i];
                Y_right[cur_offset_xy_2 + j] += Y_right[cur_offset_xy + j + i * vec_len] * coeffsY_right[k + i];
            } 
            else {
                X_prover[cur_offset_xy_2 + j] += X_prover[cur_offset_xy_2 + j + i * vec_len] * coeffsX_prover[k + i];
                Y_prover[cur_offset_xy_2 + j] += Y_prover[cur_offset_xy_2 + j + i * vec_len] * coeffsY_prover[k + i];
                X_left[cur_offset_xy_2 + j] += X_left[cur_offset_xy_2 + j + i * vec_len] * coeffsX_left[k + i];
                Y_right[cur_offset_xy_2 + j] += Y_right[cur_offset_xy_2 + j + i * vec_len] * coeffsY_right[k + i];
            }

            X_prover[cur_offset_xy + j] += X_prover[cur_offset_xy + j + i * vec_len] * coeffsX_prover[i];
            Y_prover[cur_offset_xy + j] += Y_prover[cur_offset_xy + j + i * vec_len] * coeffsY_prover[i];
            X_left[cur_offset_xy + j] += X_left[cur_offset_xy + j + i * vec_len] * coeffsX_left[i];
            Y_right[cur_offset_xy + j] += Y_right[cur_offset_xy + j + i * vec_len] * coeffsY_right[i];
        }
    }

    for (int i = 0; i < k; i ++) {
        X_prover[cur_offset_xy + vec_len + i] = 0;
        Y_prover[cur_offset_xy + vec_len + i] = 0;
        X_left[cur_offset_xy + vec_len + i] = 0;
        Y_right[cur_offset_xy + vec_len + i] = 0;

        X_prover[cur_offset_xy_2 + vec_len + i] = 0;
        Y_prover[cur_offset_xy_2 + vec_len + i] = 0;
        X_left[cur_offset_xy_2 + vec_len + i] = 0;
        Y_right[cur_offset_xy_2 + vec_len + i] = 0;
    }

    for (int i = 0; i < k; i ++) {
        res_left[i] = 0;
        res_right[i] = 0;

        res_left[k + i] = 0;
        res_right[k + i] = 0;

        for (int j = 0; j < k; j ++) {
            res_left[i] += coeffsY_left[j] * local_left[batch_id][i][j];
            res_right[i] += coeffsY_right[j] * local_right[batch_id][i][j];

            res_left[k + i] += coeffsY_left[k + j] * local_left[batch_id][k + i][k + j];
            res_right[k + i] += coeffsY_right[k + j] * local_right[batch_id][k + i][k + j];
        }
    }

    Z_left[batch_id] = Z_right[batch_id] = 0;
    Z_left[offset_mono + batch_id] = Z_right[offset_mono + batch_id] = 0;

    for (int i = 0; i < k; i ++) {
        Z_left[batch_id] += res_left[i] * coeffsX_left[i];
        Z_right[batch_id] += res_right[i] * coeffsX_right[i];

        Z_left[offset_mono + batch_id] += res_left[k + i] * coeffsX_left[k + i];
        Z_right[offset_mono + batch_id] += res_right[k + i] * coeffsX_right[k + i];
    }

    if (vec_len == 1) {
        X_left[cur_offset_xy] += XY_mask_left[2 * batch_id];
        Y_right[cur_offset_xy] += XY_mask_right[2 * batch_id + 1];
     
        X_left[cur_offset_xy_2] += XY_mask_left[offset_mono * 2 + 2 * batch_id];
        Y_right[cur_offset_xy_2] += XY_mask_right[offset_mono * 2 + 2 * batch_id + 1];

        // Z_00
        Z_left[batch_id] += Z_masks_left[batch_id * (2 * k + 1)];
        Z_right[batch_id] += Z_masks_right[batch_id * (2 * k + 1)];

        Z_left[offset_mono + batch_id] += Z_masks_left[offset_z_masks + batch_id * (2 * k + 1)];
        Z_right[offset_mono + batch_id] += Z_masks_right[offset_z_masks + batch_id * (2 * k + 1)];

        for (int i = 0; i < k; i ++) {
            // x_0 * y_i, i = 1, ..., k
            Z_left[batch_id] += Z_masks_left[batch_id * (2 * k + 1) + 1 + i] * coeffsX_left[i];
            // x_i * y_0, i = 1, ..., k
            Z_left[batch_id] += Z_masks_left[batch_id * (2 * k + 1) + 1 + k + i] * coeffsY_left[i];

            Z_right[batch_id] += Z_masks_right[batch_id * (2 * k + 1) + 1 + i] * coeffsX_right[i];
            Z_right[batch_id] += Z_masks_right[batch_id * (2 * k + 1) + 1 + k + i] * coeffsY_right[i];

            Z_left[offset_mono + batch_id] += Z_masks_left[offset_z_masks + batch_id * (2 * k + 1) + 1 + i] * coeffsX_left[k + i];
            Z_left[offset_mono + batch_id] += Z_masks_left[offset_z_masks + batch_id * (2 * k + 1) + 1 + k + i] * coeffsY_left[k + i];

            Z_right[offset_mono + batch_id] += Z_masks_right[offset_z_masks + batch_id * (2 * k + 1) + 1 + i] * coeffsX_right[k + i];
            Z_right[offset_mono + batch_id] += Z_masks_right[offset_z_masks + batch_id * (2 * k + 1) + 1 + k + i] * coeffsY_right[k + i];
        }
    }

    // cout << "end of part 5" << endl;
    ++ ws;
}

// This solution is similar to Protocols/Malicious3PCProtocol.hpp, verify_thread_handler, verify_part1, verify_part2.
template<class T>
void TestProtocol<T>::verify_thread_handler() {

    // cout << "in verify_thread_handler" << endl;

    MyPair<int, int> data;

    while (true) { 
        if (!cv.pop_dont_stop(data)) {
            continue;
        }

        // data = cv.pop();

#define PART(x)\
    case x: \
    verify_part ## x(data.second); \
    break

        switch (data.first) {
        PART(1);
        PART(2);
        PART(3);
        PART(4);
        PART(5);
        PART(8);
        PART(9);

        default:
            return ;
        }
    }
}

/*
 * TODO: parallel verify multiple batches.
 * 
 * There are four pass_arounds to do:
 *      1. pass around the random seed for random choices
 *      2. pass around the share_right
 *      3. in chop: inner_product and coefficients
 *      4. co-verify
 * 
 * According to our previous work, if we want to use multi-thread, we have to seperate the online and offline phase, 
 * because message cannot interact in multi-thread.
 * 
 */
template <class T>
void TestProtocol<T>::verify() {

    // auto start = std::chrono::high_resolution_clock::now();
    
    // Initialize
    Nbatches = (pointer_answer - 1) / batch_size + 1;
    ws.set_target(Nbatches);

    // cout << "Nbatches: " << Nbatches << endl;

    offset_data_xy = new_batch_size * Nbatches;
    offset_data_z = batch_size * Nbatches;
    offset_mono = Nbatches;
    offset_z_shares = k * k * Nbatches;
    offset_z_masks = (2 * k + 1) * Nbatches;

    //========================= Share Additive Shares of Inner-Product Results and Higher-bit Errors ========================= 

#ifdef SHOW_TIMECOST_LOGS

    auto cp1 = std::chrono::high_resolution_clock::now();

#endif

    octet my_seed[SEED_SIZE], left_seed[SEED_SIZE], right_seed[SEED_SIZE];
    local_prng.get_octets(my_seed, SEED_SIZE);

    for (auto &o : os)
        o.reset_write_head();
    os[0].append(my_seed, SEED_SIZE);

    P.pass_around(os[0], os[1], 1);
    os[1].consume(left_seed, SEED_SIZE);

    P.pass_around(os[0], os[1], -1);
    os[1].consume(right_seed, SEED_SIZE);

    octet global_seed[SEED_SIZE];
    for (int i = 0; i < SEED_SIZE; i++) {
        global_seed[i] = my_seed[i] ^ left_seed[i] ^ right_seed[i];
    } 
    global_prng.SetSeed(global_seed);

    // for (int i = 0; i < KAPPA; i++) {
    //     for (int j = 0; j < batch_size; j ++) {
    //         choices[i][j] = global_prng.get_bit();       // low efficiency
    //     }
    // }
    // auto end1 = std::chrono::high_resolution_clock::now();
    // cout << "get_bit time: " << (end1 - start1).count() / 1e6 << " ms" << endl;
    
    // start1 = std::chrono::high_resolution_clock::now();
    for (int i = 0; i < KAPPA; i++) {
        global_prng.get_octets((octet*)choices[i], batch_size);
        for (int j = 0; j < batch_size; j++) {
            choices[i][j] &= 1;
        }
    }
    // end1 = std::chrono::high_resolution_clock::now();
    // cout << "get_octets time: " << (end1 - start1).count() / 1e6 << " ms" << endl;

    // Kappa times of linear combination using random 0/1 coefficients

    // share kappa_c_add_shares and kappa_higher_bit_error (generate share_left)
    for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
        for (int i = 0; i < KAPPA; i ++) {
            // additive shares of c
            thread_buffer_c_add_shares[batch_id * KAPPA + i] = shared_prngs[1].get_word();
            kappa_c_add_shares_left[batch_id * KAPPA + i] = shared_prngs[0].get_word();
            // higher-bit errors
            thread_buffer_e_shares[batch_id * KAPPA + i] = shared_prngs[1].get_word();
            kappa_e_left[batch_id * KAPPA + i] = shared_prngs[0].get_word();
        }
    }
    
    memcpy(kappa_c_add_shares_prover_left, thread_buffer_c_add_shares, sizeof(VerifyRing) * Nbatches * KAPPA);

#ifdef SHOW_TIMECOST_LOGS

    auto cp2 = std::chrono::high_resolution_clock::now();
    cout << "preprocessing time: " << (cp2 - cp1).count() / 1e6 << " ms" << endl;

#endif

#ifndef USE_SINGLE_THREAD
    ws.reset();
    // compute share_right of kappa_c_add_shares and higher-bit errors
    for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
        cv.push(MyPair<int, int>(1, batch_id));
    }
    ws.wait();
#elif
    // compute share_right of kappa_c_add_shares and higher-bit errors
    memset(kappa_c_triples, 0, sizeof(MulRing) * KAPPA * 2 * Nbatches);

    for (int batch_id = 0; batch_id < Nbatches; batch_id++) {
        // compute share_right of kappa higher-bit errors
        int batch_offset = batch_id * batch_size;
        int kappa_batch_offset = batch_id * KAPPA;
        int new_batch_offset = batch_id * new_batch_size;

        for (int i = 0; i < KAPPA; i++) {
            VerifyRing e = 0;
            int kappa_index = kappa_batch_offset + i;
            int kappa_c_triples_index = batch_id * KAPPA * 2 + i * 2;

            MulRing tmp = thread_buffer_c_add_shares[kappa_index];
            MulRing tmp2 = thread_buffer_e_shares[kappa_index];

            for (int j = 0; j < batch_size; j++) {
                if (__builtin_expect(choices[i][j], 1)) {
                    e += E[batch_offset + j];
                    kappa_c_triples[kappa_c_triples_index] += c_triples[new_batch_offset + j * 2];
                    kappa_c_triples[kappa_c_triples_index + 1] += c_triples[new_batch_offset + j * 2 + 1];
                }
            }

            MulRing new_tmp = (MulRing)e - tmp;
            if ((MulRing)tmp + new_tmp < tmp) {
                new_tmp -= ((VerifyRing)1 << 64);
            }
            thread_buffer_c_add_shares[kappa_index] = new_tmp;

            e >>= 64;
            thread_buffer_e_shares[kappa_index] = (MulRing)e - tmp2;
        }
    }
#endif

    #ifdef SHOW_TIMECOST_LOGS
        auto cp3 = std::chrono::high_resolution_clock::now();
        cout << "verify part1 costs " << (cp3 - cp2).count() / 1e6 << " ms." << endl;
    #endif

    memcpy(kappa_c_add_shares_prover_right, thread_buffer_c_add_shares, sizeof(VerifyRing) * Nbatches * KAPPA);

    for (auto &o : os)
        o.reset_write_head();

    for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
        for (int i = 0; i < KAPPA; i ++) {
            os[0].store(thread_buffer_c_add_shares[batch_id * KAPPA + i]);
            os[0].store(thread_buffer_e_shares[batch_id * KAPPA + i]);
        }
    }

    P.pass_around(os[0], os[1], 1);

    // get share_right of kappa_c_add_shares
    for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
        for (int i = 0; i < KAPPA; i ++) {
            os[1].get(kappa_c_add_shares_right[batch_id * KAPPA + i]);
            os[1].get(kappa_e_right[batch_id * KAPPA + i]);
        }
    }
    #ifdef SHOW_TIMECOST_LOGS
        auto cp4 = std::chrono::high_resolution_clock::now();
        cout << "Communication and pack-unpack costs " << (cp4 - cp3).count() / 1e6 << "ms." << endl;
    #endif
    // auto end = std::chrono::high_resolution_clock::now();
    // cout << "Sharing Additive Shares and Higher-bit Errors: " << (end - start).count() / 1e6 << " ms" << endl;

    //========================= Check Zero ========================= 

#ifndef USE_SINGLE_THREAD
    ws.reset();
    for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
        cv.push(MyPair<int, int>(8, batch_id));
    }
    ws.wait();
#elif
    for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
        for (int i = 0; i < KAPPA; i ++) {
            // share with next party
            res_o_ss[batch_id * KAPPA * 2 + i * 2] = kappa_c_triples[batch_id * KAPPA * 2 + i * 2] - (MulRing)kappa_c_add_shares_left[batch_id * KAPPA + i] - (MulRing)kappa_c_add_shares_prover_right[batch_id * KAPPA + i];
            // share with previous party
            res_o_ss[batch_id * KAPPA * 2 + i * 2 + 1] = kappa_c_triples[batch_id * KAPPA * 2 + i * 2 + 1] - (MulRing)kappa_c_add_shares_right[batch_id * KAPPA + i] - (MulRing)kappa_c_add_shares_prover_left[batch_id * KAPPA + i];
        }
    }
#endif

    #ifdef SHOW_TIMECOST_LOGS
        auto cp5 = std::chrono::high_resolution_clock::now();
        cout << "verify part8 costs " << (cp5 - cp4).count() << endl;
    #endif

    for (auto &o : os)
        o.reset_write_head();

    for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
        for (int i = 0; i < KAPPA; i ++) {
            os[0].store(res_o_ss[batch_id * KAPPA * 2 + i * 2 + 1]);
        }
    }

    P.pass_around(os[0], os[1], 1);

    for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
        for (int i = 0; i < KAPPA; i ++) {
            os[1].get(res_o_third_ss[batch_id * KAPPA + i]);
        }
    }

#ifdef SHOW_TIMECOST_LOGS

    auto cp6 = std::chrono::high_resolution_clock::now();
    cout << "Communication and pack-unpack costs " << (cp6 - cp5).count() / 1e6 << " ms." << endl;

#endif

#ifndef USE_SINGLE_THREAD
    ws.reset();
    for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
        cv.push(MyPair<int, int>(9, batch_id));
    }
    ws.wait();
#elif
    bool zero_check_res = true;
    for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
        MulRing o;
        for (int i = 0; i < KAPPA; i ++) {
            o = res_o_ss[batch_id * KAPPA * 2 + i * 2] + res_o_ss[batch_id * KAPPA * 2 + i * 2 + 1] + res_o_third_ss[batch_id * KAPPA + i];
            if (o != 0) {
                zero_check_res = false;
            }
        }
    }

    if (!zero_check_res) {
        cout << "Zero check failed" << endl;
    }
#endif

    #ifdef SHOW_TIMECOST_LOGS
        auto cp7 = std::chrono::high_resolution_clock::now();
        cout << "zero check costs " << (cp7 - cp6).count() / 1e6 << " ms." << endl;
    #endif

    //========================= Recover Higher Bits Errors ========================= 

    // start = std::chrono::high_resolution_clock::now();

#ifndef USE_SINGLE_THREAD
    ws.reset();
     for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
        cv.push(MyPair<int, int>(2, batch_id));
    }
    ws.wait();
#elif
    for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
        for (int i = 0; i < KAPPA; i ++) {
            // c_i + 2^k * h_i
            lift_kappa_c_add_shares_left[batch_id * KAPPA + i] = kappa_c_add_shares_left[batch_id * KAPPA + i] + (((VerifyRing) kappa_e_left[batch_id * KAPPA + i]) << 64);
            lift_kappa_c_add_shares_right[batch_id * KAPPA + i] = kappa_c_add_shares_right[batch_id * KAPPA + i] + (((VerifyRing) kappa_e_right[batch_id * KAPPA + i]) << 64);
        }
    }
#endif

    #ifdef SHOW_TIMECOST_LOGS
        auto cp8 = std::chrono::high_resolution_clock::now();
        cout << "verify part2 costs " << (cp8 - cp7).count() / 1e6 << " ms." << endl;
    #endif
    // end = std::chrono::high_resolution_clock::now();
    // cout << "Recover Higher Bits Errors: " << (end - start).count() / 1e6 << " ms" << endl;

    //========================= Merge Into One Triple Using Random Linear Combination ========================= 

    // start = std::chrono::high_resolution_clock::now();

    octet seed_left[SEED_SIZE], seed_right[SEED_SIZE], seed_prover[SEED_SIZE];

    // seed for the random coefs.
    shared_prngs[1].get_octets(seed_left, SEED_SIZE);       // as Verifier left
    shared_prngs[0].get_octets(seed_right, SEED_SIZE);      // as Verifier right

    for (auto &o : os)
        o.reset_write_head();

    os[0].append(seed_left, SEED_SIZE); // should store the seed after passing around share of `e`

    P.pass_around(os[0], os[1], 1);

    os[1].consume(seed_prover, SEED_SIZE);

    PRNG random_coef_prng_left, random_coef_prng_right, random_coef_prng_prover;

    random_coef_prng_left.SetSeed(seed_left);
    random_coef_prng_right.SetSeed(seed_right);
    random_coef_prng_prover.SetSeed(seed_prover);

    // The random_coefs can be used in every batch_id. 
    for (int i = 0; i < KAPPA; i ++) {
        random_coef_left[i] = random_coef_prng_left.getDoubleWord();
        random_coef_right[i] = random_coef_prng_right.getDoubleWord();
        random_coef_prover[i] = random_coef_prng_prover.getDoubleWord();
    }

    memset(counter_prover, 0, sizeof(VerifyRing) * batch_size);
    memset(counter_left, 0, sizeof(VerifyRing) * batch_size);
    memset(counter_right, 0, sizeof(VerifyRing) * batch_size);

    // Compute the real coefficient. Also they can be used in every batch_id.
    for (int i = 0; i < KAPPA; i ++) {
        for (int j = 0; j < batch_size; j ++) {
            if (choices[i][j]) {
                counter_prover[j] += random_coef_prover[i];
                counter_left[j] += random_coef_left[i];
                counter_right[j] += random_coef_right[i];
            }
        }
    }

#ifdef SHOW_TIMECOST_LOGS
    auto cp9 = std::chrono::high_resolution_clock::now();
    cout << "Preparation before part3 costs " << (cp9 - cp8).count() / 1e6 << " ms." << endl;
#endif

#ifndef USE_SINGLE_THREAD
    ws.reset();
     for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
        cv.push(MyPair<int, int>(3, batch_id));
    }
    ws.wait();
#elif
    for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
        Z_left[batch_id] = 0;
        Z_right[batch_id] = 0;

        for (int i = 0; i < KAPPA; i ++) {
            Z_left[batch_id] += lift_kappa_c_add_shares_left[batch_id * KAPPA + i] * random_coef_left[i];
            Z_right[batch_id] += lift_kappa_c_add_shares_right[batch_id * KAPPA + i] * random_coef_right[i];
        }

        for (int j = 0; j < batch_size; j ++) {

            Y_prover[batch_id * new_batch_size + j * 2] = (VerifyRing) a_triples[batch_id * new_batch_size + j * 2] * counter_prover[j];
            Y_prover[batch_id * new_batch_size + j * 2 + 1] = (VerifyRing) b_triples[batch_id * new_batch_size + j * 2] * counter_prover[j];

            X_prover[batch_id * new_batch_size + j * 2] = (VerifyRing) b_triples[batch_id * new_batch_size + j * 2 + 1];// * counter_prover[j];
            X_prover[batch_id * new_batch_size + j * 2 + 1] = (VerifyRing) a_triples[batch_id * new_batch_size + j * 2 + 1];// * counter_prover[j];

            X_left[batch_id * new_batch_size + j * 2] = (VerifyRing) b_triples[batch_id * new_batch_size + j * 2];// * counter_left[j];
            X_left[batch_id * new_batch_size + j * 2 + 1] = (VerifyRing) a_triples[batch_id * new_batch_size + j * 2];// * counter_left[j];

            Y_right[batch_id * new_batch_size + j * 2] = (VerifyRing) a_triples[batch_id * new_batch_size + j * 2 + 1] * counter_right[j];
            Y_right[batch_id * new_batch_size + j * 2 + 1] = (VerifyRing) b_triples[batch_id * new_batch_size + j * 2 + 1] * counter_right[j];
            
            // x[1] * y[1]
            Z_right[batch_id] -= (VerifyRing) a_triples[batch_id * new_batch_size + j * 2 + 1] * (VerifyRing) b_triples[batch_id * new_batch_size + j * 2 + 1] * counter_right[j];        
        }
    }
#endif

    #ifdef SHOW_TIMECOST_LOGS
        auto cp10 = std::chrono::high_resolution_clock::now();
        cout << "verify part3 costs " << (cp10 - cp9).count() / 1e6 << " ms." << endl;
    #endif
    //========================= Recursive Reduction ========================= 

    // preparation before chop
    s = new_batch_size;
    vec_len = (s - 1) / k + 1;

#ifdef SHOW_TIMECOST_LOGS
    cout << "In while loop: " << endl;
#endif
    // chop

    iter = 0;

    while (true) {
 
        for (auto &o : os)
            o.reset_write_head();
        
        #ifdef SHOW_TIMECOST_LOGS
                auto while_cp1 = std::chrono::high_resolution_clock::now();
        #endif

        // thread_buffer stores random numbers with left.
        for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
            for (int i = 0; i < k; i ++) {
                for (int j = 0; j < k; j ++) {
                    if (i == 0 && j == 0) {  
                        continue;
                    }
                    thread_buffer[batch_id * k * k + i * k + j] = shared_prngs[1].getDoubleWord();
                    local_left[batch_id][i][j] = shared_prngs[0].getDoubleWord();

                    thread_buffer[offset_z_shares + batch_id * k * k + i * k + j] = shared_prngs[1].getDoubleWord();
                    local_left[batch_id][k + i][k + j] = shared_prngs[0].getDoubleWord();
                }
            }
        }

        if (vec_len == k) {
            for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
                XY_mask_thread_buffer[2 * batch_id] = shared_prngs[1].getDoubleWord();
                XY_mask_thread_buffer[2 * batch_id + 1] = shared_prngs[1].getDoubleWord();
                XY_mask_left[2 * batch_id] = shared_prngs[0].getDoubleWord();
                XY_mask_left[2 * batch_id + 1] = shared_prngs[0].getDoubleWord();

                XY_mask_thread_buffer[offset_mono * 2 + 2 * batch_id] = shared_prngs[1].getDoubleWord();
                XY_mask_thread_buffer[offset_mono * 2 + 2 * batch_id + 1] = shared_prngs[1].getDoubleWord();
                XY_mask_left[offset_mono * 2 + 2 * batch_id] = shared_prngs[0].getDoubleWord();
                XY_mask_left[offset_mono * 2 + 2 * batch_id + 1] = shared_prngs[0].getDoubleWord();

                for (int i = 0; i < 2 * k + 1; i++) {
                    Z_masks_thread_buffer[batch_id * (2 * k + 1) + i] = shared_prngs[1].getDoubleWord();
                    Z_masks_left[batch_id * (2 * k + 1) + i] = shared_prngs[0].getDoubleWord();

                    Z_masks_thread_buffer[offset_z_masks + batch_id * (2 * k + 1) + i] = shared_prngs[1].getDoubleWord();
                    Z_masks_left[offset_z_masks + batch_id * (2 * k + 1) + i] = shared_prngs[0].getDoubleWord();
                }
            }
        }

        #ifdef SHOW_TIMECOST_LOGS
                auto while_cp2 = std::chrono::high_resolution_clock::now();
                cout << "\tpreparation before part4 costs " << (while_cp2 - while_cp1).count() / 1e6 << " ms." << endl;
        #endif

#ifndef USE_SINGLE_THREAD
        ws.reset();
        for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
            cv.push(MyPair<int, int>(4, batch_id));
        }
        ws.wait();
#elif
        for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
            for (int i = 0; i < k; i ++) {
                for (int j = 0; j < k; j ++) {
                    if (i == 0 && j == 0) {
                        continue;
                    }
                    if (iter == 0) {
                        VerifyRing ip = inner_product(X_prover + batch_id * new_batch_size + i * vec_len, 
                                        Y_prover + batch_id * new_batch_size + j * vec_len, 
                                        vec_len);

                        thread_buffer[batch_id * k * k + i * k + j] = ip - thread_buffer[batch_id * k * k + i * k + j];
                        thread_buffer[offset_z_shares + batch_id * k * k + i * k + j] = ip - thread_buffer[offset_z_shares + batch_id * k * k + i * k + j];
                    } 
                    else {
                        thread_buffer[batch_id * k * k + i * k + j] = 
                            inner_product(X_prover + batch_id * new_batch_size + i * vec_len, 
                                        Y_prover + batch_id * new_batch_size + j * vec_len, 
                                        vec_len)
                            - thread_buffer[batch_id * k * k + i * k + j];

                        thread_buffer[offset_z_shares + batch_id * k * k + i * k + j] = 
                            inner_product(X_prover + offset_data_xy + batch_id * new_batch_size + i * vec_len, 
                                        Y_prover + offset_data_xy + batch_id * new_batch_size + j * vec_len, 
                                        vec_len)
                            - thread_buffer[offset_z_shares + batch_id * k * k + i * k + j];
                    }
                }
            }

            if (vec_len == k) {
                XY_mask_prover[2 * batch_id] = local_prng.getDoubleWord();
                XY_mask_prover[2 * batch_id + 1] = local_prng.getDoubleWord();
                XY_mask_thread_buffer[2 * batch_id] = XY_mask_prover[2 * batch_id] - XY_mask_thread_buffer[2 * batch_id];
                XY_mask_thread_buffer[2 * batch_id + 1] = XY_mask_prover[2 * batch_id + 1] - XY_mask_thread_buffer[2 * batch_id + 1];

                XY_mask_prover[offset_mono * 2 + 2 * batch_id] = local_prng.getDoubleWord();
                XY_mask_prover[offset_mono * 2 + 2 * batch_id + 1] = local_prng.getDoubleWord();
                XY_mask_thread_buffer[offset_mono * 2 + 2 * batch_id] = XY_mask_prover[offset_mono * 2 + 2 * batch_id] - XY_mask_thread_buffer[offset_mono * 2 + 2 * batch_id];
                XY_mask_thread_buffer[offset_mono * 2 + 2 * batch_id + 1] = XY_mask_prover[offset_mono * 2 + 2 * batch_id + 1] - XY_mask_thread_buffer[offset_mono * 2 + 2 * batch_id + 1];

                int cur_offset_z_masks = batch_id * (2 * k + 1);
                int cur_offset_xy = batch_id * new_batch_size;
                // x_0 * y_0
                Z_masks_thread_buffer[cur_offset_z_masks] = XY_mask_prover[batch_id * 2] * XY_mask_prover[batch_id * 2 + 1] - Z_masks_thread_buffer[cur_offset_z_masks];
                Z_masks_thread_buffer[cur_offset_z_masks + offset_z_masks] = XY_mask_prover[offset_mono * 2 + batch_id * 2] * XY_mask_prover[offset_mono * 2 + batch_id * 2 + 1] - Z_masks_thread_buffer[cur_offset_z_masks];

                for (int i = 0; i < k; i++) {
                    // x_0 * y_i, i = 1, ... k
                    Z_masks_thread_buffer[cur_offset_z_masks + 1 + i] = XY_mask_prover[batch_id * 2] * X_prover[cur_offset_xy + i] - Z_masks_thread_buffer[cur_offset_z_masks + 1 + i];
                    // x_i * y_0, i = 1, ... k
                    Z_masks_thread_buffer[cur_offset_z_masks + 1 + k + i] = XY_mask_prover[batch_id * 2 + 1] * Y_prover[cur_offset_xy + i] - Z_masks_thread_buffer[cur_offset_z_masks + 1 + k + i];
                    Z_masks_thread_buffer[cur_offset_z_masks + offset_z_masks + 1 + i] = XY_mask_prover[offset_mono * 2 + batch_id * 2] * X_prover[cur_offset_xy + offset_data_xy + i] - Z_masks_thread_buffer[cur_offset_z_masks + offset_z_masks + 1 + i];
                    Z_masks_thread_buffer[cur_offset_z_masks + offset_z_masks + 1 + k + i] = XY_mask_prover[offset_mono * 2 + batch_id * 2 + 1] * Y_prover[cur_offset_xy + offset_data_xy + i] - Z_masks_thread_buffer[cur_offset_z_masks + offset_z_masks + 1 + k + i];
                }
            }
        }
#endif

        #ifdef SHOW_TIMECOST_LOGS
                auto while_cp3 = std::chrono::high_resolution_clock::now();
                cout << "\tverift part4 costs " << (while_cp3 - while_cp2).count() / 1e6 << " ms." << endl;
        #endif

        for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
            for (int i = 0; i < k; i ++) {
                for (int j = 0; j < k; j ++) {
                    if (i == 0 && j == 0) {
                        continue;
                    }
                    os[0].store(thread_buffer[batch_id * k * k + i * k + j]);
                    os[0].store(thread_buffer[offset_z_shares + batch_id * k * k + i * k + j]);
                }
            }
        }

        if (vec_len == k) {
            for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
                os[0].store(XY_mask_thread_buffer[batch_id * 2]);
                os[0].store(XY_mask_thread_buffer[batch_id * 2 + 1]);

                os[0].store(XY_mask_thread_buffer[offset_mono * 2 + batch_id * 2]);
                os[0].store(XY_mask_thread_buffer[offset_mono * 2 + batch_id * 2 + 1]);

                for (int i = 0; i < 2 * k + 1; i++) {
                    os[0].store(Z_masks_thread_buffer[batch_id * (2 * k + 1) + i]);
                    os[0].store(Z_masks_thread_buffer[offset_z_masks + batch_id * (2 * k + 1) + i]);
                }
            }
        }

        P.pass_around(os[0], os[1], 1);

        for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
            for (int i = 0; i < k; i ++) {
                for (int j = 0; j < k; j ++) {
                    if (i == 0 && j == 0) {
                        continue;
                    }
                    os[1].get(local_right[batch_id][i][j]);
                    os[1].get(local_right[batch_id][k + i][k + j]);
                }
            }
        }

        if (vec_len == k) {
            for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
                os[1].get(XY_mask_right[batch_id * 2]);
                os[1].get(XY_mask_right[batch_id * 2 + 1]);

                os[1].get(XY_mask_right[offset_mono * 2 + batch_id * 2]);
                os[1].get(XY_mask_right[offset_mono * 2 + batch_id * 2 + 1]);

                for (int i = 0; i < 2 * k + 1; i++) {
                    os[1].get(Z_masks_right[batch_id * (2 * k + 1) + i]);
                    os[1].get(Z_masks_right[offset_z_masks + batch_id * (2 * k + 1) + i]);
                }
            }
        }

        for (auto &o : os)
            o.reset_write_head();

        // should store the seed after passing around share of inner products. 
        for (int i = 0; i < k; i ++) {
            coeffsX_left[i] = shared_prngs[1].getDoubleWord();
            coeffsY_left[i] = shared_prngs[1].getDoubleWord();
            coeffsX_right[i] = shared_prngs[0].getDoubleWord();
            coeffsY_right[i] = shared_prngs[0].getDoubleWord();
            
            coeffsX_left[k + i] = shared_prngs[1].getDoubleWord();
            coeffsY_left[k + i] = shared_prngs[1].getDoubleWord();
            coeffsX_right[k + i] = shared_prngs[0].getDoubleWord();
            coeffsY_right[k + i] = shared_prngs[0].getDoubleWord();

            os[0].store(coeffsX_left[i]);
            os[0].store(coeffsY_left[i]);
            os[0].store(coeffsX_left[k + i]);
            os[0].store(coeffsY_left[k + i]);
        }

        P.pass_around(os[0], os[1], 1);

        for (int i = 0; i < k; i ++) {
            os[1].get(coeffsX_prover[i]);
            os[1].get(coeffsY_prover[i]);

            os[1].get(coeffsX_prover[k + i]);
            os[1].get(coeffsY_prover[k + i]);
        }
            
    #ifdef SHOW_TIMECOST_LOGS
            auto while_cp4 = std::chrono::high_resolution_clock::now();
            cout << "\tcommunication and pack-unpack costs " << (while_cp4 - while_cp3).count() / 1e6 << " ms." << endl;
    #endif

#ifndef USE_SINGLE_THREAD
        ws.reset();
        for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
            cv.push(MyPair<int, int>(5, batch_id));
        }
        ws.wait();
#elif
        for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
            VerifyRing res_left[k * 2], res_right[k * 2];
            int cur_offset_xy = batch_id * new_batch_size;
            int cur_offset_xy_2 = batch_id * new_batch_size + offset_data_xy;

            local_left[batch_id][0][0] = Z_left[batch_id];
            local_right[batch_id][0][0] = Z_right[batch_id];

            if (__glibc_unlikely(iter == 0)) {
                local_left[batch_id][k][k] = Z_left[batch_id];
                local_right[batch_id][k][k] = Z_right[batch_id];
            }
            else {
                local_left[batch_id][k][k] = Z_left[offset_mono + batch_id];
                local_right[batch_id][k][k] = Z_right[offset_mono + batch_id];
            }

            for (int i = 1; i < k; i ++) {
                local_left[batch_id][0][0] -= local_left[batch_id][i][i];
                local_right[batch_id][0][0] -= local_right[batch_id][i][i];

                local_left[batch_id][k][k] -= local_left[batch_id][k + i][k + i];
                local_right[batch_id][k][k] -= local_right[batch_id][k + i][k + i];
            }

            for (int j = 0; j < vec_len; j ++) {
                if (__glibc_unlikely(iter == 0)) { // cannot put behind (X_prover[cur_offset_xy_2 + j] already multiplied)
                    X_prover[cur_offset_xy_2 + j] = X_prover[cur_offset_xy + j] * coeffsX_prover[k];
                    Y_prover[cur_offset_xy_2 + j] = Y_prover[cur_offset_xy + j] * coeffsY_prover[k];
                    X_left[cur_offset_xy_2 + j] = X_left[cur_offset_xy + j] * coeffsX_left[k];
                    Y_right[cur_offset_xy_2 + j] = Y_right[cur_offset_xy + j] * coeffsY_right[k];
                }
                else {
                    X_prover[cur_offset_xy_2 + j] *= coeffsX_prover[k];
                    Y_prover[cur_offset_xy_2 + j] *= coeffsY_prover[k];
                    X_left[cur_offset_xy_2 + j] *= coeffsX_left[k];
                    Y_right[cur_offset_xy_2 + j] *= coeffsY_right[k];
                }

                X_prover[cur_offset_xy + j] *= coeffsX_prover[0];
                Y_prover[cur_offset_xy + j] *= coeffsY_prover[0];
                X_left[cur_offset_xy + j] *= coeffsX_left[0];
                Y_right[cur_offset_xy + j] *= coeffsY_right[0];
            }

            for (int i = 1; i < k; i ++) {
                for (int j = 0; j < vec_len; j ++) {
                    if (__glibc_unlikely(iter == 0)) {
                        X_prover[cur_offset_xy_2 + j] += X_prover[cur_offset_xy + j + i * vec_len] * coeffsX_prover[k + i];
                        Y_prover[cur_offset_xy_2 + j] += Y_prover[cur_offset_xy + j + i * vec_len] * coeffsY_prover[k + i];
                        X_left[cur_offset_xy_2 + j] += X_left[cur_offset_xy + j + i * vec_len] * coeffsX_left[k + i];
                        Y_right[cur_offset_xy_2 + j] += Y_right[cur_offset_xy + j + i * vec_len] * coeffsY_right[k + i];
                    } 
                    else {
                        X_prover[cur_offset_xy_2 + j] += X_prover[cur_offset_xy_2 + j + i * vec_len] * coeffsX_prover[k + i];
                        Y_prover[cur_offset_xy_2 + j] += Y_prover[cur_offset_xy_2 + j + i * vec_len] * coeffsY_prover[k + i];
                        X_left[cur_offset_xy_2 + j] += X_left[cur_offset_xy_2 + j + i * vec_len] * coeffsX_left[k + i];
                        Y_right[cur_offset_xy_2 + j] += Y_right[cur_offset_xy_2 + j + i * vec_len] * coeffsY_right[k + i];
                    }

                    X_prover[cur_offset_xy + j] += X_prover[cur_offset_xy + j + i * vec_len] * coeffsX_prover[i];
                    Y_prover[cur_offset_xy + j] += Y_prover[cur_offset_xy + j + i * vec_len] * coeffsY_prover[i];
                    X_left[cur_offset_xy + j] += X_left[cur_offset_xy + j + i * vec_len] * coeffsX_left[i];
                    Y_right[cur_offset_xy + j] += Y_right[cur_offset_xy + j + i * vec_len] * coeffsY_right[i];
                }
            }

            for (int i = 0; i < k; i ++) {
                X_prover[cur_offset_xy + vec_len + i] = 0;
                Y_prover[cur_offset_xy + vec_len + i] = 0;
                X_left[cur_offset_xy + vec_len + i] = 0;
                Y_right[cur_offset_xy + vec_len + i] = 0;

                X_prover[cur_offset_xy_2 + vec_len + i] = 0;
                Y_prover[cur_offset_xy_2 + vec_len + i] = 0;
                X_left[cur_offset_xy_2 + vec_len + i] = 0;
                Y_right[cur_offset_xy_2 + vec_len + i] = 0;
            }

            for (int i = 0; i < k; i ++) {
                res_left[i] = 0;
                res_right[i] = 0;

                res_left[k + i] = 0;
                res_right[k + i] = 0;

                for (int j = 0; j < k; j ++) {
                    res_left[i] += coeffsY_left[j] * local_left[batch_id][i][j];
                    res_right[i] += coeffsY_right[j] * local_right[batch_id][i][j];

                    res_left[k + i] += coeffsY_left[k + j] * local_left[batch_id][k + i][k + j];
                    res_right[k + i] += coeffsY_right[k + j] * local_right[batch_id][k + i][k + j];
                }
            }

            Z_left[batch_id] = Z_right[batch_id] = 0;
            Z_left[offset_mono + batch_id] = Z_right[offset_mono + batch_id] = 0;

            for (int i = 0; i < k; i ++) {
                Z_left[batch_id] += res_left[i] * coeffsX_left[i];
                Z_right[batch_id] += res_right[i] * coeffsX_right[i];

                Z_left[offset_mono + batch_id] += res_left[k + i] * coeffsX_left[k + i];
                Z_right[offset_mono + batch_id] += res_right[k + i] * coeffsX_right[k + i];
            }

            if (vec_len == 1) {
                X_left[cur_offset_xy] += XY_mask_left[2 * batch_id];
                Y_right[cur_offset_xy] += XY_mask_right[2 * batch_id + 1];
            
                X_left[cur_offset_xy_2] += XY_mask_left[offset_mono * 2 + 2 * batch_id];
                Y_right[cur_offset_xy_2] += XY_mask_right[offset_mono * 2 + 2 * batch_id + 1];

                // Z_00
                Z_left[batch_id] += Z_masks_left[batch_id * (2 * k + 1)];
                Z_right[batch_id] += Z_masks_right[batch_id * (2 * k + 1)];

                Z_left[offset_mono + batch_id] += Z_masks_left[offset_z_masks + batch_id * (2 * k + 1)];
                Z_right[offset_mono + batch_id] += Z_masks_right[offset_z_masks + batch_id * (2 * k + 1)];

                for (int i = 0; i < k; i ++) {
                    // x_0 * y_i, i = 1, ..., k
                    Z_left[batch_id] += Z_masks_left[batch_id * (2 * k + 1) + 1 + i] * coeffsX_left[i];
                    // x_i * y_0, i = 1, ..., k
                    Z_left[batch_id] += Z_masks_left[batch_id * (2 * k + 1) + 1 + k + i] * coeffsY_left[i];

                    Z_right[batch_id] += Z_masks_right[batch_id * (2 * k + 1) + 1 + i] * coeffsX_right[i];
                    Z_right[batch_id] += Z_masks_right[batch_id * (2 * k + 1) + 1 + k + i] * coeffsY_right[i];

                    Z_left[offset_mono + batch_id] += Z_masks_left[offset_z_masks + batch_id * (2 * k + 1) + 1 + i] * coeffsX_left[k + i];
                    Z_left[offset_mono + batch_id] += Z_masks_left[offset_z_masks + batch_id * (2 * k + 1) + 1 + k + i] * coeffsY_left[k + i];

                    Z_right[offset_mono + batch_id] += Z_masks_right[offset_z_masks + batch_id * (2 * k + 1) + 1 + i] * coeffsX_right[k + i];
                    Z_right[offset_mono + batch_id] += Z_masks_right[offset_z_masks + batch_id * (2 * k + 1) + 1 + k + i] * coeffsY_right[k + i];
                }
            }
        }
#endif
    #ifdef SHOW_TIMECOST_LOGS
            auto while_cp5 = std::chrono::high_resolution_clock::now();
            cout << "\tverify part5 costs " << (while_cp5 - while_cp4).count() / 1e6 << " ms." << endl;
    #endif

        if (vec_len == 1) {
            break;
        }

        s = vec_len;
        vec_len = (s - 1) / k + 1;
        iter++;
    }

    // end = std::chrono::high_resolution_clock::now();
    // cout << "Recursive reduction: " << (end - start).count() / 1e6 << " ms" << endl;

    //========================= Final Check ========================= 

    // start = std::chrono::high_resolution_clock::now();

    #ifdef SHOW_TIMECOST_LOGS
        auto cp11 = std::chrono::high_resolution_clock::now();
    #endif

    for (auto &o : os)
        o.reset_write_head();

    for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
        os[0].store(XY_mask_right[2 * batch_id]);
        os[0].store(Y_right[new_batch_size * batch_id] + XY_mask_right[2 * batch_id + 1]);
        os[0].store(Z_right[batch_id]);

        os[0].store(XY_mask_right[offset_mono * 2 + 2 * batch_id]);
        os[0].store(Y_right[offset_data_xy + new_batch_size * batch_id] + XY_mask_right[offset_mono * 2 + 2 * batch_id + 1]);
        os[0].store(Z_right[offset_mono + batch_id]);
    }

    // send to Verifier_left
    P.pass_around(os[0], os[1], 1);

    for (int batch_id = 0; batch_id < Nbatches; batch_id ++) {
        VerifyRing x, y, z, x2, y2, z2;
        os[1].get(x);
        os[1].get(y);
        os[1].get(z);
        os[1].get(x2);
        os[1].get(y2);
        os[1].get(z2);

        x += X_left[new_batch_size * batch_id] + XY_mask_left[2 * batch_id];
        y += XY_mask_left[2 * batch_id +1 ];
        z += Z_left[batch_id];

        x2 += X_left[offset_data_xy + new_batch_size * batch_id] + XY_mask_left[offset_mono * 2 + 2 * batch_id + 1];
        y2 += XY_mask_left[offset_mono * 2 + 2 * batch_id + 1];
        z2 += Z_left[offset_mono + batch_id];

        if (x * y != z || x2 * y2 != z2) {
            zkp_flag = false;
        }

        // if (x * y != z) {
        //     cout << batch_id << "-th proof check failed" << endl;
        // }
        // if (x2 * y2 != z2) {
        //     cout << batch_id << "-th proof (2) check failed" << endl;
        // }
    }

    // if (!zkp_flag) {
    //     // throw mac_fail("ZKP check failed");
    //     cout << "ZKP check failed" << endl;
    // }

    #ifdef SHOW_TIMECOST_LOGS
        auto cp12 = std::chrono::high_resolution_clock::now();
        cout << "zkp check costs " << (cp12 - cp11).count() / 1e6 << " ms." << endl;
    #endif
    // end = std::chrono::high_resolution_clock::now();
    // cout << "Final Check: " << (end - start).count() / 1e6 << " ms" << endl;

}

template <class T>
void TestProtocol<T>::prepare_mul(const T& x, const T& y, int n) {

    E[pointer] = (VerifyRing) x[0].debug() * ((VerifyRing) y[0].debug() + (VerifyRing) y[1].debug()) + (VerifyRing) x[1].debug() * (VerifyRing) y[0].debug();

    // share = x[0] * y[0] + x[0] * y[1] + x[1] * y[0]
	// typename T::value_type share = x.local_mul(y);
    MulRing share = (MulRing) E[pointer];

    typename T::value_type tmp[2];
    for (int i = 0; i < 2; i++)
        tmp[i].randomize(shared_prngs[i], n);
    
    // add_share = x[0] * y[0] + x[0] * y[1] + x[1] * y[0] + tmp[0] - tmp[1]
    auto add_share = (typename T::value_type) share + tmp[0] - tmp[1];
    add_share.pack(os[0], n);

    // x[0] * y[0] + x[0] * y[1] + x[1] * y[0] + tmp[0] - tmp[1]
    add_shares.push_back(add_share);
    // inner-product: x[0] * y[1] + x[1] * y[0]
    // res1: tmp[1]
    // res2: - x[0] * y[0] - tmp[0]
   
    a_triples[pointer * 2] = (MulRing) x[0].debug();
    a_triples[pointer * 2 + 1] = (MulRing) x[1].debug();
    b_triples[pointer * 2] = (MulRing) y[0].debug();
    b_triples[pointer * 2 + 1] = (MulRing) y[1].debug();

    pointer ++;

}

template <class T>
void TestProtocol<T>::exchange() {

	if (os[0].get_length() > 0) {
        P.pass_around(os[0], os[1], 1);
    }
        
    this->rounds++;
    
}

template <class T>
inline T TestProtocol<T>::finalize_mul(int n) {

    this->counter++;
    this->bit_counter += (n == -1 ? T::clear::length() : n);
    T result;
    result[0] = add_shares.next();
    result[1].unpack(os[1], n);             // received from player i-1 and set it in index 1
                                            // so index 1 is shared with previous and index 0 is shared with next
                                            // which is the same as shared_prngs

    c_triples[pointer_answer * 2] = (MulRing) result[0].debug();
    c_triples[pointer_answer * 2 + 1] = (MulRing) result[1].debug();

    pointer_answer++;

    return result;
}


template<class T>
inline void TestProtocol<T>::init_dotprod()
{
	init_mul();
    dotprod_share.assign_zero();

	
}

template<class T>
inline void TestProtocol<T>::prepare_dotprod(const T& x, const T& y)
{

	dotprod_share = dotprod_share.lazy_add(x.local_mul(y));
}

template<class T>
inline void TestProtocol<T>::next_dotprod()
{

	dotprod_share.normalize();
    typename T::value_type tmp[2];
    for (int i = 0; i < 2; i++)
        tmp[i].randomize(shared_prngs[i], -1);
    auto add_share = dotprod_share + tmp[0] - tmp[1];
    add_share.pack(os[0], -1);
    add_shares.push_back(add_share);
    dotprod_share.assign_zero();
}

template<class T>
inline T TestProtocol<T>::finalize_dotprod(int length)
{
	(void) length;
    this->dot_counter++;
    return finalize_mul();
}

template<class T>
T TestProtocol<T>::get_random() {
	T res;
	for (int i = 0; i < 2; i++) {
		res[i].randomize(shared_prngs[i]);
	}
	return res;
}

template<class T>
template<class U>
void TestProtocol<T>::trunc_pr(const vector<int>& regs, int size, U& proc,
        false_type)
{
    assert(regs.size() % 4 == 0);
    assert(proc.P.num_players() == 3);
    assert(proc.Proc != 0);
    typedef typename T::clear value_type;
    int gen_player = 2;
    int comp_player = 1;
    bool generate = P.my_num() == gen_player;
    bool compute = P.my_num() == comp_player;
    ArgList<TruncPrTupleWithGap<value_type>> infos(regs);
    auto& S = proc.get_S();

    octetStream cs;
    ReplicatedInput<T> input(P);

    if (generate)
    {
        SeededPRNG G;
        for (auto info : infos)
            for (int i = 0; i < size; i++)
            {
                auto r = G.get<value_type>();
                input.add_mine(info.upper(r));
                if (info.small_gap())
                    input.add_mine(info.msb(r));
                (r + S[info.source_base + i][0]).pack(cs);
            }
        P.send_to(comp_player, cs);
    }
    else
        input.add_other(gen_player);

    if (compute)
    {
        P.receive_player(gen_player, cs);
        for (auto info : infos)
            for (int i = 0; i < size; i++)
            {
                auto c = cs.get<value_type>() + S[info.source_base + i].sum();
                input.add_mine(info.upper(c));
                if (info.small_gap())
                    input.add_mine(info.msb(c));
            }
    }

    input.add_other(comp_player);
    input.exchange();
    init_mul();

    for (auto info : infos)
        for (int i = 0; i < size; i++)
        {
            this->trunc_pr_counter++;
            auto c_prime = input.finalize(comp_player);
            auto r_prime = input.finalize(gen_player);
            S[info.dest_base + i] = c_prime - r_prime;

            if (info.small_gap())
            {
                auto c_dprime = input.finalize(comp_player);
                auto r_msb = input.finalize(gen_player);
                S[info.dest_base + i] += ((r_msb + c_dprime)
                        << (info.k - info.m));
                prepare_mul(r_msb, c_dprime);
            }
        }

    exchange();

    for (auto info : infos)
        for (int i = 0; i < size; i++)
            if (info.small_gap())
                S[info.dest_base + i] -= finalize_mul()
                        << (info.k - info.m + 1);
}

template<class T>
template<class U>
void TestProtocol<T>::trunc_pr(const vector<int>& regs, int size, U& proc,
        true_type)
{
    (void) regs, (void) size, (void) proc;
    throw runtime_error("trunc_pr not implemented");
}

template<class T>
template<class U>
void TestProtocol<T>::trunc_pr(const vector<int>& regs, int size,
        U& proc)
{

	if (TRUNC_LOG_LEVEL & TRUNC_PROCESS) {
		cout << "In trunc_pr()" << endl;
	}
	if (TRUNC_LOG_LEVEL & TRUNC_DETAIL) {
		cout << "regs: ";
		for (auto i : regs) {
			cout << i << " ";
		}
		cout << endl << size << endl;
	}

    this->trunc_rounds++;
    trunc_pr(regs, size, proc, T::clear::characteristic_two);
}

#endif