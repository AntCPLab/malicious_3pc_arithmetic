#ifndef PROTOCOLS_BGIN19PROTOCOL_HPP_
#define PROTOCOLS_BGIN19PROTOCOL_HPP_

#include "BGIN19Protocol.h"
#include "Replicated.hpp"
  
#include "Tools/benchmarking.h"
#include "Tools/Bundle.h"

#include "global_debug.hpp"
#include <ctime>
#include <chrono>
#include "Tools/performance.h"

template <class T>
BGIN19Protocol<T>::BGIN19Protocol(Player &P) : ReplicatedBase(P)
{

    cout << "Create Protocol with K = " << T::type_string() << endl;

    assert(P.num_players() == 3);
	if (not P.is_encrypted())
		insecure("unencrypted communication", false);

    // if T::type_string() ends with "gf2n_long"
    if (T::type_string().find("gf2n_long") != std::string::npos) {
        return ;
    } 

    VerifyRing::init();
    zz_p::init(1ull << 59);

	shared_prngs[0].ReSeed();
	octetStream os;
	os.append(shared_prngs[0].get_seed(), SEED_SIZE);
	P.send_relative(1, os);
	P.receive_relative(-1, os);
	shared_prngs[1].SetSeed(os.get_data());

    os.reset_write_head();

    if (P.my_real_num() == 0) {
        global_prngs[0].ReSeed();
        os.append(global_prngs[0].get_seed(), SEED_SIZE);
        P.send_all(os);
    }
    else {
        P.receive_player(0, os);
        global_prngs[0].SetSeed(os.get_data());
    }

    octet seed1[SEED_SIZE], seed2[SEED_SIZE];
    global_prngs[0].get_octets(seed1, SEED_SIZE);
    global_prngs[0].get_octets(seed2, SEED_SIZE);
    global_prngs[1].SetSeed(seed1);
    global_prngs[2].SetSeed(seed2);

    counter1 = counter2 = 0;

#ifndef USE_SINGLE_THREAD
    // for (int i = 0; i < global_thread_number; i++) {
    //     std::shared_ptr<std::thread> _thread(new std::thread(&BGIN19Protocol<T>::thread_handler, this));
    //     threads.push_back(_thread);
    // }
    // cout << "Now thread size = " << threads.size() << endl;
    while ((int) threads.size() < global_thread_number) {
        std::shared_ptr<std::thread> _thread(new std::thread(&BGIN19Protocol<T>::thread_handler, this));
        threads.push_back(_thread);
    }
    cout << "Global thread number = " << global_thread_number << endl;
#endif

    eval_p_poly = new VerifyRing[2 * global_k_size - 1];
    eval_base = new VerifyRing[global_k_size];
    eval_result = new VerifyRing*[global_k_size];
    for(int i = 0; i < global_k_size; i++) {
        eval_result[i] = new VerifyRing[global_k_size];
    }

    mul_triples = new MultiShare[global_batch_size * global_max_status * 2];
    thetas = new VerifyRing*[global_max_status];
    betas = new VerifyRing*[global_max_status];

    int _T = ((global_batch_size - 1) / global_k_size + 1) * global_k_size;
    int s = (_T - 1) / global_k_size + 1;

    for (int i = 0; i < global_max_status; i ++) {
        thetas[i] = new VerifyRing[s];
        betas[i] = new VerifyRing[global_k_size];
    }

    int cnt = log(2 * _T) / log(global_k_size) + 1;
    rs_as_prover = new VerifyRing*[global_max_status];
    rs_as_verifier1 = new VerifyRing*[global_max_status];
    rs_as_verifier2 = new VerifyRing*[global_max_status];

    for (int i = 0; i < global_max_status; i ++) {
        rs_as_prover[i] = new VerifyRing[cnt + 1];
        rs_as_verifier1[i] = new VerifyRing[cnt + 1];
        rs_as_verifier2[i] = new VerifyRing[cnt + 1];
    }

    zkp_datas = new ZKPData[global_max_status];
    verify_results = new bool[global_max_status];

    outfile = new ofstream[global_thread_number];
    for (int i = 0; i < global_thread_number; i ++) {
        outfile[i].open("logs/party_" + to_string(P.my_real_num()) + "_" + to_string(i));
    }

}

template <class T>
void BGIN19Protocol<T>::thread_handler() {
    zz_p::init(1ull << 59);
    ThreadInfo data;

    while (true) { 
        if (!cv.pop_dont_stop(data)) {
            continue;
        }

        // cout << "data.first: " << data.first << ", data.second: " << data.second << endl;

#define REGPART(x) \
    case x: \
        _##x(data.second); \
        break

        if (data.first == EXIT) {
            return;
        }

        switch (data.first) {
            REGPART(PROVE1);
            REGPART(PROVE2);
            REGPART(VERIFY1);
            REGPART(VERIFY);
            default: {
                return;
            }
        }
    }
}

template<class T>
void BGIN19Protocol<T>::init_mul() {

    while (counter1 >= global_batch_size * global_max_status) {
        verify_api(global_batch_size * global_max_status);
    }

	for (auto& o : os)
        o.reset_write_head();
    add_shares.clear();

}

template <class T>
void BGIN19Protocol<T>::prepare_mul(const T& x, const T& y, int n) {
	
	typename T::value_type share = x.local_mul(y);

    array<typename T::value_type, 2> tmp;
    for (int i = 0; i < 2; i++)
        tmp[i].randomize(shared_prngs[i], n);
    auto add_share = share + tmp[0] - tmp[1];
    add_share.pack(os[0], n);
    add_shares.push_back(add_share);

    mul_triples[counter1].x[0] = x[0];
    mul_triples[counter1].x[1] = x[1];
    mul_triples[counter1].y[0] = y[0];
    mul_triples[counter1].y[1] = y[1];
    mul_triples[counter1].rho = tmp;
    counter1 ++;
}

template <class T>
void BGIN19Protocol<T>::exchange() {

	if (os[0].get_length() > 0) {
        P.pass_around(os[0], os[1], 1);
    }
}

template <class T>
inline T BGIN19Protocol<T>::finalize_mul(int n) {

    this->counter++;
    this->bit_counter += (n == -1 ? T::clear::length() : n);
    T result;
    result[0] = add_shares.next();
    result[1].unpack(os[1], n);             // received from player i-1 and set it in index 1
                                            // so index 1 is shared with previous and index 0 is shared with next
                                            // which is the same as shared_prngs

    mul_triples[counter2].z[0] = result[0];
    mul_triples[counter2].z[1] = result[1];
    counter2 ++;

    return result;
}

template <class _T>
void BGIN19Protocol<_T>::_PROVE1(int tid) {

    // outfile[tid] << "Preprocessing" << endl;

    // cout << "in prove1" << endl;

    ZKPData &data = zkp_datas[tid];

    int k = data.k_size;
    int size = data.batch_size;
    int cols = (size - 1) / k + 1;

    int temp_pointer = 0;

    for (int i = 0; i < k; i++) {

        for (int j = 0; j < cols; j++) {
            if (temp_pointer >= size) {
                data.input_left[i][j * 2].assign_zero();
                data.input_left[i][j * 2 + 1].assign_zero();
                data.input_right[i][j * 2].assign_zero();
                data.input_right[i][j * 2 + 1].assign_zero();
                data.input_left_next[i][j * 2].assign_zero();
                data.input_left_next[i][j * 2 + 1].assign_zero();
                data.input_right_prev[i][j * 2].assign_zero();
                data.input_right_prev[i][j * 2 + 1].assign_zero();
                data.input_mono_prev[i][j].assign_zero();
                data.input_mono_next[i][j].assign_zero();
            } else {
                VerifyRing x_first = mul_triples[global_batch_size * tid + temp_pointer].x[0];
                VerifyRing y_first = mul_triples[global_batch_size * tid + temp_pointer].y[0];
                VerifyRing x_second = mul_triples[global_batch_size * tid + temp_pointer].x[1];
                VerifyRing y_second = mul_triples[global_batch_size * tid + temp_pointer].y[1];
                VerifyRing rho_first = mul_triples[global_batch_size * tid + temp_pointer].rho[0];
                VerifyRing rho_second = mul_triples[global_batch_size * tid + temp_pointer].rho[1];
                VerifyRing z_second = mul_triples[global_batch_size * tid + temp_pointer].z[1];

                // Share with P_{i+1}
                data.input_left[i][j * 2] = x_first;
                data.input_left[i][j * 2 + 1] = y_first;
                // Share with P_{i-1}
                data.input_right[i][j * 2] = y_second;
                data.input_right[i][j * 2 + 1] = x_second;

                data.input_left_next[i][j * 2] = x_second;
                data.input_left_next[i][j * 2 + 1] = y_second;

                data.input_right_prev[i][j * 2] = y_first;
                data.input_right_prev[i][j * 2 + 1] = x_first;

                data.input_mono_prev[i][j] = rho_first;
                data.input_mono_next[i][j] = z_second - x_second * y_second - rho_second;

                // gf2n_long left = zkp_datas[0].input_left[i][j * 2] * zkp_datas[0].input_right[i][j * 2]
                //              + zkp_datas[0].input_left[i][j * 2 + 1] * zkp_datas[0].input_right[i][j * 2 + 1];
                // gf2n_long right = zkp_datas[0].input_mono_prev[i][j] + zkp_datas[0].input_mono_next[i][j];
                // assert(left == right);
            }
            temp_pointer++;
        }
    }
    // cout << "in prove1, cp 1" << endl;

    // outfile[tid] << "set coeff" << endl;

    int T = ((size - 1) / k + 1) * k;
    int s = (T - 1) / k + 1;

    for(int i = 0; i < k; i++) {
        for(int j = 0; j < s; j++) {
            data.input_left[i][2 * j] *= thetas[tid][j];
            data.input_left[i][2 * j + 1] *= thetas[tid][j];
        }
    }
    // cout << "in prove1, cp 2" << endl;

    // outfile[tid] << "get bases" << endl;

    Langrange<VerifyRing>::get_bases(k, data.base);
    data.s = s * 2;

    // outfile[tid] << "inner product" << endl;

    for(int i = 0; i < k; i++) {
        for(int j = 0; j < k; j++) {
            eval_result[i][j] = inner_product(data.input_left[i], data.input_right[j], (size_t) data.s);
        }
    }
    // cout << "in prove1, cp 3" << endl;

    // outfile[tid] << "eval_p_poly" << endl;

    for(int i = 0; i < k; i++) {
        eval_p_poly[i] = eval_result[i][i];
    }

    for(int i = 0; i < k - 1; i++) {
        eval_p_poly[i + k] = 0;
        for(int j = 0; j < k; j++) {
            for (int l = 0; l < k; l++) {
                eval_p_poly[i + k] = eval_p_poly[i + k] + data.base[i][j] * eval_result[j][l] * data.base[i][l];
            }
        }
    }    
    // cout << "in prove1, cp 4" << endl;

    // outfile[tid] << "cp1" << endl;

    vector<VerifyRing> ss(2 * k - 1);       
    for(int i = 0; i < 2 * k - 1; i++) {           
        ss[i] = eval_p_poly[i];
    }
    data.proof.p_evals_masked.push_back(ss);

    // outfile[tid] << "cp2" << endl;
    // cout << "in prove1, cp 5" << endl;

    ++ ws;

    // outfile[tid] << "finish" << endl;
}

template <class _T>
void BGIN19Protocol<_T>::_PROVE2(int tid) {
    ZKPData &data = zkp_datas[tid];

    if (data.s == 1) {
        ++ ws;
        return ;
    }

    int k = data.k_size;

    int s0 = data.s;
    int index;
    s0 = data.s;
    data.s = (data.s - 1) / k + 1;

    Langrange<VerifyRing>::evaluate_bases(k, rs_as_prover[tid][verify_round], eval_base);

    for(int i = 0; i < k; i++) {
        for(int j = 0; j < data.s; j++) {
            index = i * data.s + j;
            
            if (index < s0) {
                VerifyRing temp_result;
                temp_result.assign_zero();
                for(int l = 0; l < k; l++) {
                    temp_result += eval_base[l] * data.input_left[l][index];
                }
                data.input_left[i][j] = temp_result;

                temp_result.assign_zero();
                for(int l = 0; l < k; l++) {
                    temp_result += eval_base[l] * data.input_right[l][index];
                }
                data.input_right[i][j] = temp_result;
            }
            else {
                data.input_left[i][j].assign_zero();
                data.input_right[i][j].assign_zero();
            }
        }
    }

    for(int i = 0; i < k; i++) {
        for(int j = 0; j < k; j++) {
            eval_result[i][j] = inner_product(data.input_left[i], data.input_right[j], (size_t) data.s);
        }
    }

    for(int i = 0; i < k; i++) {
        eval_p_poly[i] = eval_result[i][i];
    }

    for(int i = 0; i < k - 1; i++) {
        eval_p_poly[i + k] = 0;
        for(int j = 0; j < k; j++) {
            for (int l = 0; l < k; l++) {
                eval_p_poly[i + k] = eval_p_poly[i + k] + data.base[i][j] * eval_result[j][l] * data.base[i][l];
            }
        }
    }

    vector<VerifyRing> ss(2 * k - 1);       
    for(int i = 0; i < 2 * k - 1; i++) {           
        ss[i] = eval_p_poly[i];
    }
    data.proof.p_evals_masked.push_back(ss);

    ++ ws;

}

template <class _T>
void BGIN19Protocol<_T>::prove(int size) {

    // outfile[0] << "Preprocessing" << endl;

    // auto cp1 = std::chrono::high_resolution_clock::now();

    // cout << size << endl;
    if (size == 0) {
        ++ ws;
        return ;
    }

    int k = OnlineOptions::singleton.k_size;
    int total = 0;

    while (size > 0) {
        if ((int) size > global_batch_size) {
            zkp_datas[total].set(global_batch_size, k);
        }
        else {
            zkp_datas[total].set(size, k);
        }

        total += 1;
        size -= global_batch_size;
    }

    // auto cp11 = std::chrono::high_resolution_clock::now();
    // cout << "Prove: preprocessing 1.1: " << (cp11 - cp1).count() / 1e6 << "ms" << endl;

    total_zkp_datas = total;

    VerifyRing local_rs;
    local_prng.SetSeed(seed_prove);

    int T = ((global_batch_size - 1) / k + 1) * k;
    int local_s = (T - 1) / k + 1;

    for (int i = 0; i < total; i ++) {
        for(int j = 0; j < local_s; j++) {
            thetas[i][j].randomize(local_prng);
        }

        for(int j = 0; j < k; j++) {
            betas[i][j].randomize(local_prng);
        }
    }
    
    // cout << "cp 1, total: " << total << endl;
    // outfile[0] << "part 1" << endl;

    // auto cp2 = std::chrono::high_resolution_clock::now();

    // cout << "Prove: preprocessing 1.2: " << (cp2 - cp11).count() / 1e6 << "ms" << endl;
    // cout << "Prove: preprocessing: " << (cp2 - cp1).count() / 1e6 << "ms" << endl;

    ws.set_target(total);
    

    for (int i = 0; i < total; i ++) {
        cv.push(ThreadInfo(PROVE1, i));
    }

    ws.wait();
    // cout << "cp 2" << endl;

    // auto cp3 = std::chrono::high_resolution_clock::now();

    // cout << "Prove: part 1: " << (cp3 - cp2).count() / 1e6 << "ms" << endl;


    local_s *= 2;
    verify_round = 0;

    while(true){

        // auto cp4 = std::chrono::high_resolution_clock::now();

        for (auto &o: os) {
            o.reset_write_head();
        }

        // outfile[0] << "data preprocessing" << endl;

        for (int i = 0; i < total; i ++) {
            auto &ss = zkp_datas[i].proof.p_evals_masked[verify_round];
            zkp_datas[i].verify_proof.p_evals_masked.push_back(vector<VerifyRing>());
            // assert(&ss != NULL);
            os[0].store(ss.size());
            VerifyRing rand;
            for (auto &s: ss) {
                rand.randomize(shared_prngs[1]);
                s -= rand;
                s.pack(os[0]);
                rand.randomize(shared_prngs[0]);
                zkp_datas[i].verify_proof.p_evals_masked[verify_round].push_back(rand);
            }
        }

        // auto cp41 = std::chrono::high_resolution_clock::now();
        // cout << "Prove: preprocessing 2.1: " << (cp41 - cp4).count() / 1e6 << "ms" << endl;

        for (int i = 0; i < total; i ++) {
            rs_as_verifier1[i][verify_round].randomize(shared_prngs[1]);     // Party 2 send to Party 0
            rs_as_verifier1[i][verify_round].pack(os[0]);
            rs_as_verifier2[i][verify_round].randomize(shared_prngs[0]);     // Party 1's shared_prngs[0] = Party 2's shared_prngs[1]
        }

        // auto cp42 = std::chrono::high_resolution_clock::now();
        // cout << "Prove: preprocessing 2.2: " << (cp42 - cp41).count() / 1e6 << "ms" << endl;

        // outfile[0] << "data exchange" << endl;

        P.pass_around(os[0], os[1], 1);

        // outfile[0] << "Unpack" << endl;
        // auto cp43 = std::chrono::high_resolution_clock::now();
        // cout << "Prove: prep.comm: " << (cp43 - cp42).count() / 1e6 << "ms" << endl;

        for (int i = 0; i < total; i ++) {
            size_t size = 0;
            os[1].get(size);
            vector<VerifyRing> prover_ss(size);
            for (size_t j = 0; j < size; j ++) {
                prover_ss[j].unpack(os[1]);
            }
            zkp_datas[i].other_proof.p_evals_masked.push_back(prover_ss);
        }

        for (int i = 0; i < total; i ++) {
            rs_as_prover[i][verify_round].unpack(os[1]);
        }

        if (local_s == 1) {
            break;
        }

        // outfile[0] << "Prove part 2" << endl;
        // cout << "cp 2.5, total: " << total << endl;
        // auto cp5 = std::chrono::high_resolution_clock::now();

        // cout << "Prove: preprocessing 2.3: " << (cp5 - cp43).count() / 1e6 << "ms" << endl;
        // cout << "Prove: preprocessing 2: " << (cp5 - cp4).count() / 1e6 << "ms" << endl;

        ws.reset();
        ws.set_target(total);
        for (int i = 0; i < total; i ++) {
            cv.push(ThreadInfo(PROVE2, i));
        }
        ws.wait();
        // cout << "cp 2.6" << endl;

        // auto cp6 = std::chrono::high_resolution_clock::now();
        // cout << "Prove: part 2: " << (cp6 - cp5).count() / 1e6 << "ms" << endl;

        verify_round ++;

        local_s = (local_s - 1) / k + 1;
    }
    // cout << "cp 3" << endl;

}


/*
TODO: although verify could be done without communication, but it needs PRNG
      to generate random numbers, which cannot be done in threads.
      two solutions:
        1. use main thread to generate random numbers
        2. create prng for each thread.
*/

template <class _T>
void BGIN19Protocol<_T>::_VERIFY1(int tid) {
    ZKPData &data = zkp_datas[tid];

    int batch_size = data.batch_size;
    int k = data.k_size;
    int T = ((batch_size - 1) / k + 1) * k;
    int s = (T - 1) / k + 1;
    int len = log(2 * T) / log(k) + 1;

    vector<VerifyRing> b_ss(len);
    VerifyRing final_input, final_result_ss;
    final_input.assign_zero(), final_result_ss.assign_zero();

    int cnt = 0;

    VerifyRing out_ss, sum_ss;
    out_ss.assign_zero();

    // VerifyRing** coeffs = new VerifyRing*[k];

    // for(int i = 0; i < k; i++) {
    //     coeffs[i] = new VerifyRing[s];
    //     for(int j = 0; j < s; j++) {
    //         coeffs[i][j] = betas[tid][i] * thetas[tid][j];
    //     }
    // }

    VerifyRing **input;

    // cout << "cp 1" << endl;
    if (verify_flag == 1) {
        out_ss = inner_product(data.input_mono_next, thetas[tid], (size_t)k, (size_t)s);
        input = data.input_left_next;
    }
        
    else {
        out_ss = inner_product(data.input_mono_prev, thetas[tid], (size_t)k, (size_t)s);
        input = data.input_right_prev;
    }
        
    // cout << "cp 2" << endl;
    
    sum_ss.assign_zero();
    for(int j = 0; j < k; j++) { 
        sum_ss += inner_product(betas[tid], data.other_proof.p_evals_masked[cnt], (size_t)k);
    }
    b_ss[cnt] = sum_ss - out_ss;
    // cout << "cp 3" << endl;
    
    VerifyRing* eval_base = new VerifyRing[k];
    VerifyRing* eval_base_2k = new VerifyRing[2 * k - 1];

    int index = 0;
    s *= 2;
    int s0 = s;
    VerifyRing r;

    while(true)
    {
        
        sum_ss.assign_zero();
        for(int j = 0; j < k; j++) { 
            sum_ss += data.other_proof.p_evals_masked[cnt][j];
        }

        r = rs_as_verifier1[tid][cnt];

        // memcpy(tmp, &proof.p_evals_masked[cnt], sizeof(gf2n_long) * (2 * k - 1));
        out_ss = inner_product(eval_base_2k, data.other_proof.p_evals_masked[cnt], (size_t)(2 * k - 1));
        // out_ss = inner_product(eval_base_2k, proof.p_evals_masked[cnt], 2 * k - 1);

        // out_ss.assign_zero();
        // for(uint64_t i = 0; i < 2 * k - 1; i++) {
        //     out_ss += eval_base_2k[i] * proof.p_evals_masked[cnt][i];
        // }

        b_ss[cnt] = sum_ss - out_ss;

        if(s == 1) {
            r = rs_as_verifier1[tid][cnt + 1];
            Langrange<VerifyRing>::evaluate_bases(k, r, eval_base);
            
            for(int i = 0; i < k; i++) {
                final_input += eval_base[i] * input[i][0];
            }
            Langrange<VerifyRing>::evaluate_bases(2 * k - 1, r, eval_base_2k);

            final_result_ss += inner_product(eval_base_2k, data.other_proof.p_evals_masked[cnt], (size_t)(2 * k - 1));
            break;
        }

        Langrange<VerifyRing>::evaluate_bases(k, r, eval_base);
        s0 = s;
        s = (s - 1) / k + 1;
        for(int i = 0; i < k; i++) {
            for(int j = 0; j < s; j++) {
                index = i * s + j;
                if (index < s0) {
                    VerifyRing temp_result;
                    temp_result.assign_zero();
                    for(int l = 0; l < k; l++) {
                        temp_result += eval_base[l] * input[l][index];
                    }
                    input[i][j] = temp_result;
                }
                else {
                    input[i][j].assign_zero();
                }
            }
        }

        cnt++;
    }

    delete[] eval_base;
    delete[] eval_base_2k;

    data.vermsg = ArithVerMsg(
        b_ss,
        final_input,
        final_result_ss
    );

    ++ ws;
}

template <class _T>
void BGIN19Protocol<_T>::gen_vermsg() {

    // auto cp1 = std::chrono::high_resolution_clock::now();

    int k = global_k_size;

    int T = ((global_batch_size - 1) / k + 1) * k;
    int s = (T - 1) / k + 1;

    if (verify_flag == 1) {
        local_prng.SetSeed(seed_verify1);
    }
    else {
        local_prng.SetSeed(seed_verify2);
    }
    
    
    for (int i = 0; i < total_zkp_datas; i ++) {
        for(int j = 0; j < s; j++) {
            thetas[i][j].randomize(local_prng);
        }

        for(int j = 0; j < k; j++) {
            betas[i][j].randomize(local_prng);
        }
    }

    // auto cp2 = std::chrono::high_resolution_clock::now();

    // cout << "GenVerMsg: preprocessing: " << (cp2 - cp1).count() / 1e6 << "ms" << endl;

    ws.set_target(total_zkp_datas);
    for (int i = 0; i < total_zkp_datas; i ++) {
        cv.push(ThreadInfo(VERIFY1, i));
    }

    ws.wait();

    // auto cp3 = std::chrono::high_resolution_clock::now();
    // cout << "GenVerMsg: part 1: " << (cp3 - cp2).count() / 1e6 << "ms" << endl;
}

template <class _T>
void BGIN19Protocol<_T>::_VERIFY(int tid) {
    ZKPData &data = zkp_datas[tid];

    VerifyRing b;
    int T = ((data.batch_size - 1) / data.k_size + 1) * data.k_size;
    int len = log(2 * T) / log(data.k_size) + 1;

    for(int i = 0; i < len; i++) {
        b = data.vermsg.b_ss[i] + data.other_vermsg.b_ss[i];
        
        if(!b.is_zero()) {    
            // cout << "b != 0 at index " << i << endl; 
            verify_results[tid] = false;
            ++ ws;
            return ;
        }
    }
    VerifyRing res = data.vermsg.final_input * data.other_vermsg.final_input;
    VerifyRing p_eval_r = data.vermsg.final_result_ss + data.other_vermsg.final_result_ss;
    
    if(res != p_eval_r) {   
        // cout << "res != p_eval_r" << endl;
        verify_results[tid] = false;
        ++ ws;
        return ;
    } 

    // cout << "out of arith_verify..." << endl;
    verify_results[tid] = true;
    
    ++ ws;
}

template <class _T>
bool BGIN19Protocol<_T>::verify() {

    // auto cp1 = std::chrono::high_resolution_clock::now();

    int k = global_k_size;
    int next_player_id = (P.my_real_num() + 1) % 3;
    int T = ((global_batch_size - 1) / k + 1) * k;
    int s = (T - 1) / k + 1;
    // cout << "cp 1" << endl;
    
    for (int i = 0; i < total_zkp_datas; i ++) {
        for(int j = 0; j < s; j++) {
            thetas[i][j].randomize(global_prngs[next_player_id]);
        }

        for(int j = 0; j < k; j++) {
            betas[i][j].randomize(global_prngs[next_player_id]);
        }
    }
    // cout << "cp 2" << endl;
    
    for (auto &o : os) {
        o.reset_write_head();
    }

    for (int i = 0; i < total_zkp_datas; i ++) {
        zkp_datas[i].vermsg.pack(os[0]);
    }

    // auto cp11 = std::chrono::high_resolution_clock::now();
    // cout << "Verify: preprocessing 1.1: " << (cp11 - cp1).count() / 1e6 << "ms" << endl;

    P.pass_around(os[0], os[1], 1);
    // cout << "cp 3" << endl;

    // auto cp12 = std::chrono::high_resolution_clock::now();
    // cout << "Verify: prep.comm: " << (cp12 - cp11).count() / 1e6 << "ms" << endl;

    for (int i = 0; i < total_zkp_datas; i ++) {
        zkp_datas[i].other_vermsg.unpack(os[1]);
        zkp_datas[i].other_proof = zkp_datas[i].verify_proof;
    }
    // cout << "cp 4" << endl;

    // auto cp2 = std::chrono::high_resolution_clock::now();
    // cout << "Verify: preprocessing: " << (cp2 - cp12).count() / 1e6 << "ms" << endl;

    ws.set_target(total_zkp_datas);
    for (int i = 0; i < total_zkp_datas; i ++) {
        cv.push(ThreadInfo(VERIFY1, i));
    }
    ws.wait();

    // auto cp3 = std::chrono::high_resolution_clock::now();
    // cout << "Verify: part 1: " << (cp3 - cp2).count() / 1e6 << "ms" << endl;

    // cout << "cp 5" << endl;


    ws.reset();
    for (int i = 0; i < total_zkp_datas; i ++) {
        cv.push(ThreadInfo(VERIFY, i));
    }
    // cout << "cp 6" << endl;

    ws.wait();
    // cout << "cp 7" << endl;

    // auto cp4 = std::chrono::high_resolution_clock::now();
    // cout << "Verify: part 2: " << (cp4 - cp3).count() / 1e6 << "ms" << endl;


    for (int i = 0; i < total_zkp_datas; i ++) {
        if (!verify_results[i]) {
            return false;
        }
    }
    return true;
}

template <class _T>
void BGIN19Protocol<_T>::prove_single_thread(int size) {
    // outfile[0] << "Preprocessing" << endl;

    int k = OnlineOptions::singleton.k_size;
    int total = 0;

    while (size > 0) {
        if ((int) size > global_batch_size) {
            zkp_datas[total].set(global_batch_size, k);
        }
        else {
            zkp_datas[total].set(size, k);
        }

        total += 1;
        size -= global_batch_size;
    }

    total_zkp_datas = total;

    VerifyRing local_rs;
    local_prng.SetSeed(seed_prove);

    int T = ((global_batch_size - 1) / k + 1) * k;
    int local_s = (T - 1) / k + 1;

    for (int i = 0; i < total; i ++) {
        for(int j = 0; j < local_s; j++) {
            thetas[i][j].randomize(local_prng);
        }

        for(int j = 0; j < k; j++) {
            betas[i][j].randomize(local_prng);
        }
    }
    
    // outfile[0] << "part 1" << endl;

    for (int tid = 0; tid < total; tid ++) {
        ZKPData &data = zkp_datas[tid];

        int k = data.k_size;
        int size = data.batch_size;
        int cols = (size - 1) / k + 1;

        int temp_pointer = 0;

        for (int i = 0; i < k; i++) {

            for (int j = 0; j < cols; j++) {
                if (temp_pointer >= size) {
                    data.input_left[i][j * 2].assign_zero();
                    data.input_left[i][j * 2 + 1].assign_zero();
                    data.input_right[i][j * 2].assign_zero();
                    data.input_right[i][j * 2 + 1].assign_zero();
                    data.input_left_next[i][j * 2].assign_zero();
                    data.input_left_next[i][j * 2 + 1].assign_zero();
                    data.input_right_prev[i][j * 2].assign_zero();
                    data.input_right_prev[i][j * 2 + 1].assign_zero();
                    data.input_mono_prev[i][j].assign_zero();
                    data.input_mono_next[i][j].assign_zero();
                } else {

                    VerifyRing x_first = mul_triples[global_batch_size * tid + temp_pointer].x[0].debug();
                    VerifyRing y_first = mul_triples[global_batch_size * tid + temp_pointer].y[0].debug();
                    VerifyRing x_second = mul_triples[global_batch_size * tid + temp_pointer].x[1].debug();
                    VerifyRing y_second = mul_triples[global_batch_size * tid + temp_pointer].y[1].debug();
                    VerifyRing rho_first = mul_triples[global_batch_size * tid + temp_pointer].rho[0].debug();
                    VerifyRing rho_second = mul_triples[global_batch_size * tid + temp_pointer].rho[1].debug();
                    VerifyRing z_second = mul_triples[global_batch_size * tid + temp_pointer].z[1].debug();

                    // Share with P_{i+1}
                    data.input_left[i][j * 2] = x_first;
                    data.input_left[i][j * 2 + 1] = y_first;
                    // Share with P_{i-1}
                    data.input_right[i][j * 2] = y_second;
                    data.input_right[i][j * 2 + 1] = x_second;

                    data.input_left_next[i][j * 2] = x_second;
                    data.input_left_next[i][j * 2 + 1] = y_second;

                    data.input_right_prev[i][j * 2] = y_first;
                    data.input_right_prev[i][j * 2 + 1] = x_first;

                    data.input_mono_prev[i][j] = rho_first;
                    data.input_mono_next[i][j] = z_second - x_second * y_second - rho_second;

                    // gf2n_long left = zkp_datas[0].input_left[i][j * 2] * zkp_datas[0].input_right[i][j * 2]
                    //              + zkp_datas[0].input_left[i][j * 2 + 1] * zkp_datas[0].input_right[i][j * 2 + 1];
                    // gf2n_long right = zkp_datas[0].input_mono_prev[i][j] + zkp_datas[0].input_mono_next[i][j];
                    // assert(left == right);

                }
                temp_pointer++;
            }
        }

        // outfile[0] << "set coeff" << endl;

        int T = ((size - 1) / k + 1) * k;
        int s = (T - 1) / k + 1;

        for(int i = 0; i < k; i++) {
            for(int j = 0; j < s; j++) {
                data.input_left[i][2 * j] *= thetas[tid][j];
                data.input_left[i][2 * j + 1] *= thetas[tid][j];
            }
        }

        // outfile[0] << "get bases" << endl;

        Langrange<VerifyRing>::get_bases(k, data.base);
        data.s = s * 2;

        // outfile[0] << "inner product" << endl;

        for(int i = 0; i < k; i++) {
            for(int j = 0; j < k; j++) {
                eval_result[i][j] = inner_product(data.input_left[i], data.input_right[j], (size_t) data.s);
            }
        }

        // outfile[0] << "eval_p_poly" << endl;

        for(int i = 0; i < k; i++) {
            eval_p_poly[i] = eval_result[i][i];
        }

        for(int i = 0; i < k - 1; i++) {
            eval_p_poly[i + k] = 0;
            for(int j = 0; j < k; j++) {
                for (int l = 0; l < k; l++) {
                    eval_p_poly[i + k] = eval_p_poly[i + k] + data.base[i][j] * eval_result[j][l] * data.base[i][l];
                }
            }
        }    

        // outfile[0] << "cp1" << endl;

        vector<VerifyRing> ss(2 * k - 1);       
        for(int i = 0; i < 2 * k - 1; i++) {           
            ss[i] = eval_p_poly[i];
        }
        data.proof.p_evals_masked.push_back(ss);
    }

    local_s *= 2;
    verify_round = 0;

    while(true){

        for (auto &o: os) {
            o.reset_write_head();
        }

        // outfile[0] << "data preprocessing" << endl;

        for (int i = 0; i < total; i ++) {
            auto &ss = zkp_datas[i].proof.p_evals_masked[verify_round];
            zkp_datas[i].verify_proof.p_evals_masked.push_back(vector<VerifyRing>());
            os[0].store(ss.size());
            VerifyRing rand;
            for (auto &s: ss) {
                rand.randomize(shared_prngs[1]);
                s -= rand;
                s.pack(os[0]);
                rand.randomize(shared_prngs[0]);
                zkp_datas[i].verify_proof.p_evals_masked[verify_round].push_back(rand);
            }
        }

        P.pass_around(os[0], os[1], 1);

        for (int i = 0; i < total; i ++) {
            size_t size = 0;
            os[1].get(size);
            vector<VerifyRing> prover_ss(size);
            for (size_t j = 0; j < size; j ++) {
                prover_ss[j].unpack(os[1]);
            }
            zkp_datas[i].other_proof.p_evals_masked.push_back(prover_ss);
        }

        if (local_s == 1) {
            break;
        }

        for (auto &o: os) {
            o.reset_write_head();
        }

        for (int i = 0; i < total; i ++) {
            rs_as_verifier1[i][verify_round].randomize(shared_prngs[1]);     // Party 2 send to Party 0
            rs_as_verifier1[i][verify_round].pack(os[0]);
            rs_as_verifier2[i][verify_round].randomize(shared_prngs[0]);     // Party 1's shared_prngs[0] = Party 2's shared_prngs[1]
        }

        // outfile[0] << "data exchange" << endl;

        P.pass_around(os[0], os[1], 1);

        // outfile[0] << "Unpack" << endl;

        for (int i = 0; i < total; i ++) {
            rs_as_prover[i][verify_round].unpack(os[1]);
        }

        // outfile[0] << "Prove part 2" << endl;

        for (int tid = 0; tid < total; tid ++) {
            ZKPData &data = zkp_datas[tid];

            if (data.s == 1) {
                continue;
            }

            int k = data.k_size;

            int s0 = data.s;
            int index;
            s0 = data.s;
            data.s = (data.s - 1) / k + 1;

            Langrange<VerifyRing>::evaluate_bases(k, rs_as_prover[tid][verify_round], eval_base);

            for(int i = 0; i < k; i++) {
                for(int j = 0; j < data.s; j++) {
                    index = i * data.s + j;
                    
                    if (index < s0) {
                        VerifyRing temp_result;
                        temp_result.assign_zero();
                        for(int l = 0; l < k; l++) {
                            temp_result += eval_base[l] * data.input_left[l][index];
                        }
                        data.input_left[i][j] = temp_result;

                        temp_result.assign_zero();
                        for(int l = 0; l < k; l++) {
                            temp_result += eval_base[l] * data.input_right[l][index];
                        }
                        data.input_right[i][j] = temp_result;
                    }
                    else {
                        data.input_left[i][j].assign_zero();
                        data.input_right[i][j].assign_zero();
                    }
                }
            }

            for(int i = 0; i < k; i++) {
                for(int j = 0; j < k; j++) {
                    eval_result[i][j] = inner_product(data.input_left[i], data.input_right[j], (size_t) data.s);
                }
            }

            for(int i = 0; i < k; i++) {
                eval_p_poly[i] = eval_result[i][i];
            }

            for(int i = 0; i < k - 1; i++) {
                eval_p_poly[i + k] = 0;
                for(int j = 0; j < k; j++) {
                    for (int l = 0; l < k; l++) {
                        eval_p_poly[i + k] = eval_p_poly[i + k] + data.base[i][j] * eval_result[j][l] * data.base[i][l];
                    }
                }
            }    

            vector<VerifyRing> ss(2 * k - 1);       
            for(int i = 0; i < 2 * k - 1; i++) {           
                ss[i] = eval_p_poly[i];
            }
            data.proof.p_evals_masked.push_back(ss);
        }

        verify_round ++;

        local_s = (local_s - 1) / k + 1;
    }

}

template <class _T>
void BGIN19Protocol<_T>::gen_vermsg_single_thread() {
    int k = global_k_size;

    int T = ((global_batch_size - 1) / k + 1) * k;
    int s = (T - 1) / k + 1;

    if (verify_flag == 1) {
        local_prng.SetSeed(seed_verify1);
    }
    else {
        local_prng.SetSeed(seed_verify2);
    }
    
    // outfile[0] << "preprocessing" << endl;
    
    for (int i = 0; i < total_zkp_datas; i ++) {
        for(int j = 0; j < s; j++) {
            thetas[i][j].randomize(local_prng);
        }

        for(int j = 0; j < k; j++) {
            betas[i][j].randomize(local_prng);
        }
    }

    for (int tid = 0; tid < total_zkp_datas; tid ++) {
        ZKPData &data = zkp_datas[tid];

        int batch_size = data.batch_size;
        int k = data.k_size;
        int T = ((batch_size - 1) / k + 1) * k;
        int s = (T - 1) / k + 1;
        int len = log(2 * T) / log(k) + 1;

        vector<VerifyRing> b_ss(len);
        VerifyRing final_input, final_result_ss;
        final_input.assign_zero(), final_result_ss.assign_zero();

        int cnt = 0;

        VerifyRing out_ss, sum_ss;
        out_ss.assign_zero();

        // VerifyRing** coeffs = new VerifyRing*[k];

        // for(int i = 0; i < k; i++) {
        //     coeffs[i] = new VerifyRing[s];
        //     for(int j = 0; j < s; j++) {
        //         coeffs[i][j] = betas[tid][i] * thetas[tid][j];
        //     }
        // }

        VerifyRing **input;

        // outfile[0] << "ip" << endl;

        if (verify_flag == 1) {
            out_ss = inner_product(data.input_mono_next, thetas[tid], (size_t)k, (size_t)s);
            input = data.input_left_next;
        }
            
        else {
            out_ss = inner_product(data.input_mono_prev, thetas[tid], (size_t)k, (size_t)s);
            input = data.input_right_prev;
        }
            
        
        sum_ss.assign_zero();
        for(int j = 0; j < k; j++) { 
            sum_ss += inner_product(betas[tid], data.other_proof.p_evals_masked[cnt], (size_t)k);
        }
        b_ss[cnt] = sum_ss - out_ss;
        
        VerifyRing* eval_base = new VerifyRing[k];
        VerifyRing* eval_base_2k = new VerifyRing[2 * k - 1];

        int index = 0;
        s *= 2;
        int s0 = s;
        VerifyRing r;

        while(true)
        {

            // outfile[0] << "ip2" << endl;
            
            sum_ss.assign_zero();
            for(int j = 0; j < k; j++) { 
                sum_ss += data.other_proof.p_evals_masked[cnt][j];
            }

            r = rs_as_verifier1[tid][cnt];

            // memcpy(tmp, &proof.p_evals_masked[cnt], sizeof(gf2n_long) * (2 * k - 1));
            out_ss = inner_product(eval_base_2k, data.other_proof.p_evals_masked[cnt], (size_t)(2 * k - 1));
            // out_ss = inner_product(eval_base_2k, proof.p_evals_masked[cnt], 2 * k - 1);

            // out_ss.assign_zero();
            // for(uint64_t i = 0; i < 2 * k - 1; i++) {
            //     out_ss += eval_base_2k[i] * proof.p_evals_masked[cnt][i];
            // }

            b_ss[cnt] = sum_ss - out_ss;

            if(s == 1) {
                r = rs_as_verifier1[tid][cnt + 1];
                Langrange<VerifyRing>::evaluate_bases(k, r, eval_base);
                
                for(int i = 0; i < k; i++) {
                    final_input += eval_base[i] * input[i][0];
                }
                Langrange<VerifyRing>::evaluate_bases(2 * k - 1, r, eval_base_2k);

                final_result_ss += inner_product(eval_base_2k, data.other_proof.p_evals_masked[cnt], (size_t)(2 * k - 1));
                break;
            }

            // outfile[0] << "evaluate_bases" << endl;

            Langrange<VerifyRing>::evaluate_bases(k, r, eval_base);

            // outfile[0] << "get input" << endl;

            s0 = s;
            s = (s - 1) / k + 1;
            for(int i = 0; i < k; i++) {
                for(int j = 0; j < s; j++) {
                    index = i * s + j;
                    if (index < s0) {
                        VerifyRing temp_result;
                        temp_result.assign_zero();
                        for(int l = 0; l < k; l++) {
                            temp_result += eval_base[l] * input[l][index];
                        }
                        input[i][j] = temp_result;
                    }
                    else {
                        input[i][j].assign_zero();
                    }
                }
            }

            cnt++;
        }

        delete[] eval_base;
        delete[] eval_base_2k;

        data.vermsg = ArithVerMsg(
            b_ss,
            final_input,
            final_result_ss
        );
    }
}

template <class _T>
bool BGIN19Protocol<_T>::verify_single_thread() {
    int k = global_k_size;
    int next_player_id = (P.my_real_num() + 1) % 3;
    int T = ((global_batch_size - 1) / k + 1) * k;
    int s = (T - 1) / k + 1;
    
    for (int i = 0; i < total_zkp_datas; i ++) {
        for(int j = 0; j < s; j++) {
            thetas[i][j].randomize(global_prngs[next_player_id]);
        }

        for(int j = 0; j < k; j++) {
            betas[i][j].randomize(global_prngs[next_player_id]);
        }
    }
    
    for (auto &o : os) {
        o.reset_write_head();
    }

    for (int i = 0; i < total_zkp_datas; i ++) {
        zkp_datas[i].vermsg.pack(os[0]);
    }

    P.pass_around(os[0], os[1], 1);

    for (int i = 0; i < total_zkp_datas; i ++) {
        zkp_datas[i].other_vermsg.unpack(os[1]);
        zkp_datas[i].other_proof = zkp_datas[i].verify_proof;
    }

    // outfile[0] << "gen_vermsg" << endl;

    for (int tid = 0; tid < total_zkp_datas; tid ++) {
        ZKPData &data = zkp_datas[tid];

        int batch_size = data.batch_size;
        int k = data.k_size;
        int T = ((batch_size - 1) / k + 1) * k;
        int s = (T - 1) / k + 1;
        int len = log(2 * T) / log(k) + 1;

        vector<VerifyRing> b_ss(len);
        VerifyRing final_input, final_result_ss;
        final_input.assign_zero(), final_result_ss.assign_zero();

        int cnt = 0;

        VerifyRing out_ss, sum_ss;
        out_ss.assign_zero();

        // VerifyRing** coeffs = new VerifyRing*[k];

        // for(int i = 0; i < k; i++) {
        //     coeffs[i] = new VerifyRing[s];
        //     for(int j = 0; j < s; j++) {
        //         coeffs[i][j] = betas[tid][i] * thetas[tid][j];
        //     }
        // }

        VerifyRing **input;

        if (verify_flag == 1) {
            out_ss = inner_product(data.input_mono_next, thetas[tid], (size_t)k, (size_t)s);
            input = data.input_left_next;
        }
            
        else {
            out_ss = inner_product(data.input_mono_prev, thetas[tid], (size_t)k, (size_t)s);
            input = data.input_right_prev;
        }
            
        
        sum_ss.assign_zero();
        for(int j = 0; j < k; j++) { 
            sum_ss += inner_product(betas[tid], data.other_proof.p_evals_masked[cnt], (size_t)k);
        }
        b_ss[cnt] = sum_ss - out_ss;
        
        VerifyRing* eval_base = new VerifyRing[k];
        VerifyRing* eval_base_2k = new VerifyRing[2 * k - 1];

        int index = 0;
        s *= 2;
        int s0 = s;
        VerifyRing r;

        while(true)
        {
            
            sum_ss.assign_zero();
            for(int j = 0; j < k; j++) { 
                sum_ss += data.other_proof.p_evals_masked[cnt][j];
            }

            r = rs_as_verifier1[tid][cnt];

            // memcpy(tmp, &proof.p_evals_masked[cnt], sizeof(gf2n_long) * (2 * k - 1));
            out_ss = inner_product(eval_base_2k, data.other_proof.p_evals_masked[cnt], (size_t)(2 * k - 1));
            // out_ss = inner_product(eval_base_2k, proof.p_evals_masked[cnt], 2 * k - 1);

            // out_ss.assign_zero();
            // for(uint64_t i = 0; i < 2 * k - 1; i++) {
            //     out_ss += eval_base_2k[i] * proof.p_evals_masked[cnt][i];
            // }

            b_ss[cnt] = sum_ss - out_ss;

            if(s == 1) {
                r = rs_as_verifier1[tid][cnt + 1];
                Langrange<VerifyRing>::evaluate_bases(k, r, eval_base);
                
                for(int i = 0; i < k; i++) {
                    final_input += eval_base[i] * input[i][0];
                }
                Langrange<VerifyRing>::evaluate_bases(2 * k - 1, r, eval_base_2k);

                final_result_ss += inner_product(eval_base_2k, data.other_proof.p_evals_masked[cnt], (size_t)(2 * k - 1));
                break;
            }

            Langrange<VerifyRing>::evaluate_bases(k, r, eval_base);
            s0 = s;
            s = (s - 1) / k + 1;
            for(int i = 0; i < k; i++) {
                for(int j = 0; j < s; j++) {
                    index = i * s + j;
                    if (index < s0) {
                        VerifyRing temp_result;
                        temp_result.assign_zero();
                        for(int l = 0; l < k; l++) {
                            temp_result += eval_base[l] * input[l][index];
                        }
                        input[i][j] = temp_result;
                    }
                    else {
                        input[i][j].assign_zero();
                    }
                }
            }

            cnt++;
        }

        delete[] eval_base;
        delete[] eval_base_2k;

        data.vermsg = ArithVerMsg(
            b_ss,
            final_input,
            final_result_ss
        );
    }

    // outfile[0] << "Check" << endl;

    for (int tid = 0; tid < total_zkp_datas; tid ++) {

        ZKPData &data = zkp_datas[tid];

        int T = ((data.batch_size - 1) / k + 1) * k;
        int len = log(2 * T) / log(k) + 1;

        VerifyRing b;
        bool continue_flag = false;

        for(int i = 0; i < len; i++) {
            b = data.vermsg.b_ss[i] + data.other_vermsg.b_ss[i];
            
            if(!b.is_zero()) {    
                // cout << "b != 0 at index " << i << endl; 
                verify_results[tid] = false;
                continue_flag = true;
                break;
            }
        }

        if (continue_flag) {
            continue;
        }

        VerifyRing res = data.vermsg.final_input * data.other_vermsg.final_input;
        VerifyRing p_eval_r = data.vermsg.final_result_ss + data.other_vermsg.final_result_ss;
        
        if(res != p_eval_r) {   
            // cout << "res != p_eval_r" << endl;
            verify_results[tid] = false;
            continue;
        } 

        // cout << "out of arith_verify..." << endl;
        verify_results[tid] = true;

    }

    for (int i = 0; i < total_zkp_datas; i ++) {
        if (!verify_results[i]) {
            return false;
        }
    }
    return true;
}

template <class T>
void BGIN19Protocol<T>::verify_api(int size) {

    shared_prngs[0].get_octets(seed_verify1, SEED_SIZE);
    shared_prngs[1].get_octets(seed_verify2, SEED_SIZE);

    for (auto &o : os) {
        o.reset_write_head();
    }

    os[0].store_bytes(seed_verify1, SEED_SIZE);
    P.pass_around(os[0], os[1], -1);
    os[1].consume(seed_prove, SEED_SIZE);

    // cout << "prove" << endl;

#ifdef USE_SINGLE_THREAD
    prove_single_thread(size);
#else
    // cout << "calling prove" << endl;
    prove(size);
#endif
    verify_flag = 1;

    // cout << "gen_vermsg" << endl;

#ifdef USE_SINGLE_THREAD
    gen_vermsg_single_thread();
#else
    // cout << "calling gen_vermsg" << endl;
    gen_vermsg();
#endif
    verify_flag = 0;

    // cout << "verify" << endl;

#ifdef USE_SINGLE_THREAD
    if (!verify_single_thread()) {
        // throw mac_fail("MAC check failed");
        outfile[0] << "MAC check failed" << endl;
    }
#else
    // cout << "calling verify" << endl;
    if (!verify()) {
        cout << "MAC check failed" << endl;
        // throw mac_fail("MAC check failed");
    }
#endif

    if (counter1 > size) {
        memcpy(mul_triples + counter1, mul_triples, (counter1 - size) * sizeof(MultiShare));
    }

    counter1 -= size;
    counter2 = counter1;
}


template<class T>
inline void BGIN19Protocol<T>::init_dotprod()
{
	init_mul();
    dotprod_share.assign_zero();
	
}

template<class T>
inline void BGIN19Protocol<T>::prepare_dotprod(const T& x, const T& y)
{

	dotprod_share = dotprod_share.lazy_add(x.local_mul(y));
}

template<class T>
inline void BGIN19Protocol<T>::next_dotprod()
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
inline T BGIN19Protocol<T>::finalize_dotprod(int length)
{
	(void) length;
    this->dot_counter++;
    return finalize_mul();
}

template<class T>
T BGIN19Protocol<T>::get_random() {
	T res;
	for (int i = 0; i < 2; i++) {
		res[i].randomize(shared_prngs[i]);
	}
	return res;
}

template<class T>
template<class U>
void BGIN19Protocol<T>::trunc_pr(const vector<int>& regs, int size, U& proc,
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
void BGIN19Protocol<T>::trunc_pr(const vector<int>& regs, int size, U& proc,
        true_type)
{
    (void) regs, (void) size, (void) proc;
    throw runtime_error("trunc_pr not implemented");
}

template<class T>
template<class U>
void BGIN19Protocol<T>::trunc_pr(const vector<int>& regs, int size,
        U& proc)
{

    this->trunc_rounds++;
    trunc_pr(regs, size, proc, T::clear::characteristic_two);
}

#endif